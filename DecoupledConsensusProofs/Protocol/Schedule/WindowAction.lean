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

/-- The input clock retains the time staged before the earlier duties. -/
theorem windowRead_time (S : Setup V) (v : V) (before : NamedNodeState V) (t : Time) :
    (windowReadFrom S v before t).st.core.t = t := by
  have hp (gc : GradeContract V) (st : NamedStore V) :
      (NamedDuties.propose_block_with gc S.E S.hc S.cfg (S.node v) st).1.core.t =
        st.core.t := (named_propose_clock gc S.E S.hc S.cfg (S.node v) st).1
  have hv (gc : GradeContract V) (st : NamedStore V) :
      (NamedDuties.goldfish_vote_with gc S.E S.hc (S.node v) st).1.core.t =
        st.core.t := by
    dsimp only [NamedDuties.goldfish_vote_with, goldfish_vote_with]
    split_ifs
    · exact on_goldfish_vote_checked_time S.E st.core _
    · rfl
  simp only [windowReadFrom]
  split_ifs <;> simp only [NamedDuties.update_confirmation_with, update_confirmation_with,
    hp, hv, NamedStore.setClock]

/-- Properties preserved by the preceding duties hold at the attestation input. -/
theorem windowRead_preserves (S : Setup V) (v : V) (before : NamedNodeState V)
    (t : Time) (P : NamedStore V → Prop)
    (hclock : ∀ st, P st → P (NamedStore.setClock S.E st t))
    (hprop : ∀ st, P st → P (NamedDuties.propose_block_with
      (NamedProfile.gradeContract (preparedCache S before t))
      S.E S.hc S.cfg (S.node v) st).1)
    (hgf : ∀ st, P st → P (NamedDuties.goldfish_vote_with
      (NamedProfile.gradeContract (preparedCache S before t)) S.E S.hc (S.node v) st).1)
    (hconf : ∀ st s, P st → P (NamedDuties.update_confirmation_with
      (NamedProfile.gradeContract (preparedCache S before t)) S.E S.hc st s))
    (h : P before.st) : P (windowReadFrom S v before t).st := by
  dsimp only [windowReadFrom]
  split_ifs <;> solve_by_elim (maxDepth := 10) [hclock, hprop, hgf, hconf]

/-- Retained-body and confirmation invariants survive all earlier duties. -/
theorem windowRead_invariant (S : Setup V) (v : V) (before : NamedNodeState V) (t : Time)
    (h : NamedConfirmationMembership.Invariant S.E S.cfg before.st) :
    NamedConfirmationMembership.Invariant S.E S.cfg (windowReadFrom S v before t).st := by
  apply windowRead_preserves S v before t _
    (fun st hs => NamedConfirmationMembership.invariant_clock S.E S.cfg st t hs)
    (fun st hs => NamedConfirmationMembership.invariant_propose _ S.E S.hc S.cfg
      (S.node v) st hs)
    (fun st hs => NamedConfirmationMembership.invariant_goldfish_vote _ S.E S.hc S.cfg
      (S.node v) st hs)
    (fun st s hs => NamedConfirmationMembership.invariant_update _ S.E S.hc S.cfg st s hs) h

/-- Window bounds make the actual attestation input belong to its declared round. -/
theorem actionRead_round (S : Setup V) (v : V) (before : NamedNodeState V) (r : Round) :
    S.hc.round_of (windowActionReadFrom S v before r).st.core.s = r := by
  rw [windowActionReadFrom, windowRead_slot, S.act_round]

/-- An awake action admits its row into the store after the preceding duties. -/
theorem tick_store_at_action (S : Setup V) (v : V) (before : NamedNodeState V)
    (r : Round) (hawake : (S.node v).awake r = true) :
    (Execution.NamedNode.tick S v before ((S.node v).act r)).1.st =
      let n := windowActionReadFrom S v before r
      (NamedDuties.attest_with (NamedProfile.gradeContract n.cache)
        S.E S.hc (S.node v) n.st n.record).1 := by
  have hround := actionRead_round S v before r
  change (Protocol.NamedTick.tick
    (NamedProfile.gradeContract (preparedCache S before ((S.node v).act r)))
    S.E S.hc S.cfg (S.node v) before.st before.record ((S.node v).act r)).1 = _
  rw [NamedTick.tick_computed_duties]
  simp only [windowActionReadFrom, windowReadFrom] at hround ⊢
  simp only [hround, hawake, and_self, ite_true]

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

/-- The scheduler's attestation fields identify the action under any grade contract. -/
theorem tick_attestation_fields (gc : GradeContract V) (S : Setup V)
    (v : V) (st : NamedStore V) (record : NamedRecord)
    (t : Time) (row : NamedAttestation V)
    (h : NamedObject.attest row ∈
      (Protocol.NamedTick.tick gc S.E S.hc S.cfg (S.node v) st record t).2.2) :
    t = (S.node v).act row.round ∧ (S.node v).awake row.round = true ∧
      row.val_index = v := by
  rw [NamedTick.tick_computed_duties] at h
  dsimp only at h
  apply suffix_fields _ S v _ record t row _ ?_ h
  simp only [List.mem_append, no_attest_vote, or_false]
  exact no_attest_proposal _ _ row

/-- Every emitted attestation identifies its validator's actual action time. -/
theorem emitted_at_action_time (S : Setup V) (v : V) (before : NamedNodeState V)
    (t : Time) (row : NamedAttestation V)
    (h : NamedObject.attest row ∈ (Execution.NamedNode.tick S v before t).2) :
    t = (S.node v).act row.round ∧ (S.node v).awake row.round = true ∧
      row.val_index = v :=
  tick_attestation_fields _ S v before.st before.record t row h

/-- A run emission identifies its author's action without schedule assumptions. -/
theorem run_emission_fields (S : Setup V) {rho : Run V} {v : V}
    {t : Time} {row : NamedAttestation V}
    (h : NamedRun.emits S rho v (.attest row) t) :
    t = (S.node v).act row.round ∧ (S.node v).awake row.round = true ∧
      row.val_index = v := by
  obtain ⟨i, _, hm⟩ := h
  exact emitted_at_action_time S v (NamedRun.stateBefore S rho i v) t row hm

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

/-- The indexed emission exposes the actual input after preceding same-tick duties. -/
theorem run_emission_stages (S : Setup V) (rho : Run V)
    {v : V} {row : NamedAttestation V} {t : Time}
    (hem : NamedRun.emits S rho v (.attest row) t) :
    ∃ i : Nat, rho.events[i]? = some (.tick v t) ∧
      NamedObject.attest row ∈ NamedRun.emittedAt S rho i v t ∧
      let n := windowActionReadFrom S v (NamedRun.stateBefore S rho i v) row.round
      (NamedDuties.attest_with (NamedProfile.gradeContract n.cache)
        S.E S.hc (S.node v) n.st n.record).2.2 = row ∧
      row.val_index = v ∧ row.round = S.hc.round_of n.st.core.s ∧
      t = (S.node v).act row.round ∧ (S.node v).awake row.round = true := by
  obtain ⟨ht, hawake, hval⟩ := run_emission_fields S hem
  subst t
  obtain ⟨i, hi, ho⟩ := hem
  have hrow := ((attestation_mem_at_action S v
    (NamedRun.stateBefore S rho i v) row.round row).mp ho).2.symm
  exact ⟨i, hi, ho, hrow, hval, (actionRead_round S v _ row.round).symm, rfl, hawake⟩

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
