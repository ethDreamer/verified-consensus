module
public import DecoupledConsensusProofs.Execution.Runtime
public import DecoupledConsensusProofs.Protocol.Handlers.TickBridges
public import DecoupledConsensusInternal.ModelVocabulary.Execution.WindowActionReads
public import DecoupledConsensusProofs.Protocol.Schedule.VoteWindow
public import DecoupledConsensusProofs.Protocol.Grades.NamedNode

/-!
# Attestation inputs and emissions inside the vote window

Uses the shared scheduler's duty order, the input reads, and the setup's window
bounds to identify the attestation at an actual action tick. Earlier duties may
emit other objects at the same time (PROTOCOL.md `sec:public-handlers`).
-/
@[expose] public section
namespace DecoupledConsensusModel.Proofs.WindowAction
open Execution Protocol NamedActionReads
variable {V : Type} [DecidableEq V] [Fintype V]

private theorem proposal_slot (gc : GradeContract V) (S : Setup V) (v : V)
    (st : NamedStore V) :
    (NamedDuties.propose_block_with gc S.E S.hc S.cfg (S.node v) st).1.core.s = st.core.s := by
  dsimp only [NamedDuties.propose_block_with]
  split
  · rfl
  · exact (NamedAdmission.on_block_clock .alsoCarried S.E S.hc S.cfg st _).2

private theorem vote_slot (gc : GradeContract V) (S : Setup V) (v : V)
    (st : NamedStore V) :
    (NamedDuties.goldfish_vote_with gc S.E S.hc (S.node v) st).1.core.s = st.core.s := by
  dsimp only [NamedDuties.goldfish_vote_with, goldfish_vote_with]
  split_ifs
  · exact Optimistic.on_goldfish_vote_checked_slot S.E st.core _
  · rfl

/-- Earlier duties preserve the clock staged for the action. -/
theorem windowRead_slot (S : Setup V) (v : V) (before : NamedNodeState V) (t : Time) :
    (windowReadFrom S v before t).st.core.s = S.E.slotOf t := by
  simp only [windowReadFrom]
  split_ifs <;> simp only [NamedDuties.update_confirmation_with, update_confirmation_with,
    proposal_slot, vote_slot, NamedStore.setClock]

/-- Window bounds make the actual attestation input belong to its declared round. -/
theorem actionRead_round (S : Setup V) (v : V) (before : NamedNodeState V) (r : Round) :
    S.hc.round_of (windowActionReadFrom S v before r).st.core.s = r := by
  rw [windowActionReadFrom, windowRead_slot, S.act_round]

omit [DecidableEq V] [Fintype V] in
private theorem no_attest_proposal (p : Prop) [Decidable p]
    (body : Option (NamedBlock V)) (row : NamedAttestation V) :
    NamedObject.attest row ∉ (if p then
      match body with | none => [] | some B => [NamedObject.block B] else []) := by
  split_ifs <;> cases body <;> simp

omit [DecidableEq V] [Fintype V] in
private theorem no_attest_vote (p : Prop) [Decidable p]
    (vote : Option (GoldfishVote V)) (row : NamedAttestation V) :
    NamedObject.attest row ∉ (if p then vote.toList.map NamedObject.gfVote else []) := by
  split_ifs <;> cases vote <;> simp

private theorem suffix_fields (gc : GradeContract V) (S : Setup V)
    (v : V) (st : NamedStore V) (record : NamedRecord) (t : Time)
    (row : NamedAttestation V) (prior : List (NamedObject V))
    (hprefix : NamedObject.attest row ∉ prior)
    (h : NamedObject.attest row ∈ (if t = (S.node v).act (S.hc.round_of st.core.s) ∧
        (S.node v).awake (S.hc.round_of st.core.s) = true then
      let out := NamedDuties.attest_with gc S.E S.hc (S.node v) st record
      (out.1, out.2.1, prior ++ [NamedObject.attest out.2.2])
    else (st, record, prior)).2.2) :
    t = (S.node v).act row.round ∧ (S.node v).awake row.round = true ∧
      row.val_index = v := by
  split_ifs at h with hact
  · simp only [List.mem_append, List.mem_singleton, hprefix, false_or,
      NamedObject.attest.injEq] at h
    subst row
    exact ⟨hact.1, hact.2, S.node_val_index v⟩
  · exact False.elim (hprefix h)

/-- Every emitted attestation identifies its validator's actual action time. -/
theorem emitted_at_action_time (S : Setup V) (v : V) (before : NamedNodeState V)
    (t : Time) (row : NamedAttestation V)
    (h : NamedObject.attest row ∈ (Execution.NamedNode.tick S v before t).2) :
    t = (S.node v).act row.round ∧ (S.node v).awake row.round = true ∧
      row.val_index = v := by
  change NamedObject.attest row ∈
    (Protocol.NamedTick.tick (NamedProfile.gradeContract (preparedCache S before t))
      S.E S.hc S.cfg (S.node v) before.st before.record t).2.2 at h
  rw [NamedTick.tick_computed_duties] at h
  dsimp only at h
  apply suffix_fields _ S v _ before.record t row _ ?_ h
  simp only [List.mem_append, no_attest_vote, or_false]
  exact no_attest_proposal _ _ row

/-- Exactly the selected attestation is emitted at an awake action tick, even
when proposal or Goldfish emissions share that tick. -/
theorem attestation_mem_at_action (S : Setup V) (v : V) (before : NamedNodeState V)
    (r : Round) (row : NamedAttestation V) :
    NamedObject.attest row ∈ (Execution.NamedNode.tick S v before ((S.node v).act r)).2 ↔
      (S.node v).awake r = true ∧
      row = (NamedDuties.attest_with
        (NamedProfile.gradeContract (windowActionReadFrom S v before r).cache)
        S.E S.hc (S.node v) (windowActionReadFrom S v before r).st before.record).2.2 := by
  have hround := actionRead_round S v before r
  change NamedObject.attest row ∈
    (Protocol.NamedTick.tick
      (NamedProfile.gradeContract (preparedCache S before ((S.node v).act r)))
      S.E S.hc S.cfg (S.node v) before.st before.record ((S.node v).act r)).2.2 ↔ _
  rw [NamedTick.tick_computed_duties]
  simp only [windowActionReadFrom, windowReadFrom] at hround ⊢
  simp only [hround, eq_self, true_and]
  by_cases hawake : (S.node v).awake r = true
  · simp only [hawake, ite_true, List.mem_append, List.mem_singleton,
      no_attest_vote, or_false, NamedObject.attest.injEq, true_and]
    split
    · split <;> simp only [List.not_mem_nil, List.mem_singleton, reduceCtorEq, false_or]
    · simp only [List.not_mem_nil, false_or]
  · simp only [hawake, Bool.false_eq_true, ite_false, List.mem_append,
      no_attest_vote, or_false, false_and, iff_false]
    split
    · split <;> simp only [List.not_mem_nil, List.mem_singleton, reduceCtorEq, not_false_eq_true]
    · simp only [List.not_mem_nil, not_false_eq_true]

/-- Exact run emissions use the strict-time input at the validator's own action. -/
theorem run_emission_iff (S : Setup V) (rho : Run V)
    (sch : ScheduleWellFormed S rho) (v : V) (r : Round) (row : NamedAttestation V) :
    NamedRun.emits S rho v (.attest row) ((S.node v).act r) ↔
      (∃ i : Nat, rho.events[i]? = some (.tick v ((S.node v).act r))) ∧
      (S.node v).awake r = true ∧ row = windowActionAttestationAt S rho v r := by
  constructor
  · rintro ⟨i, hi, hm⟩
    change NamedObject.attest row ∈
      (Execution.NamedNode.tick S v (NamedRun.stateBefore S rho i v)
        ((S.node v).act r)).2 at hm
    rw [NamedRuntime.tick_prefix_eq_strict S rho (NamedScheduleWellFormed.sorted sch)
      (NamedScheduleWellFormed.nodup sch) hi] at hm
    exact ⟨⟨i, hi⟩, (attestation_mem_at_action S v _ r row).mp hm⟩
  · rintro ⟨⟨i, hi⟩, hawake, hrow⟩
    refine ⟨i, hi, ?_⟩
    change NamedObject.attest row ∈
      (Execution.NamedNode.tick S v (NamedRun.stateBefore S rho i v) ((S.node v).act r)).2
    rw [NamedRuntime.tick_prefix_eq_strict S rho (NamedScheduleWellFormed.sorted sch)
      (NamedScheduleWellFormed.nodup sch) hi]
    exact (attestation_mem_at_action S v _ r row).mpr ⟨hawake, hrow⟩

/-- Public-grid totality supplies the actual tick and its exact attestation. -/
theorem honest_emits_action (S : Setup V) {rho : Run V} (sch : ScheduleWellFormed S rho)
    {v : V} (hv : v ∈ rho.honest) (r : Round)
    (hawake : (S.node v).awake r = true) (hhor : (S.node v).act r ≤ rho.horizon) :
    NamedRun.emits S rho v (.attest (windowActionAttestationAt S rho v r))
      ((S.node v).act r) := by
  apply Optimistic.emits_of_on_tick_emit S sch hv
    (S.act_public v r) (S.act_nonneg v r) hhor
  exact (attestation_mem_at_action S v
    (NamedRun.stateBeforeTime S rho ((S.node v).act r) v) r _).mpr ⟨hawake, rfl⟩

end DecoupledConsensusModel.Proofs.WindowAction
