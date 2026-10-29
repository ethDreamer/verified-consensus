module
public import DecoupledConsensusInternal.Definitions.NamedJointOutageEvents
public import DecoupledConsensusProofs.Protocol.Duties.Inputs.IntrinsicEntry
public import DecoupledConsensusProofs.Execution.StrictEventCut

/-!
# Entries signed at actual action events

Extracts the named source from the actual window read. Source scope uses the
post-tick store, since the proposal duty can insert a body earlier in that tick.
The point-instance lemmas recover the original signed-source contract.
-/
@[expose] public section
namespace DecoupledConsensusModel.Proofs.NamedWindowIntrinsicEntry
open Execution Internal.NamedOutageEntry Internal.NamedStableChainOutage
open Internal.NamedJointOutage Protocol
variable {V : Type} [DecidableEq V] [Fintype V]

/-- Every emitted height pair names the entry of its actual selected source. -/
theorem emitted_height_signed_source (S : Setup V) (rho : NamedRun V)
    {a : NamedAttestation V} {t : Time}
    (hem : NamedRun.emits S rho a.val_index (.attest a) t)
    {h : Height} {root : BlockId} {timeout : Bool}
    (hp : a.height_pair = .vote h root timeout) :
    ∃ i : Nat, ∃ source entry : NamedBlock V,
      WindowSignedSourceAt S rho i a source entry ∧
      (Protocol.derive_named S.E S.cfg source).h = h ∧
      entry.root = root := by
  obtain ⟨i, hi, ho, hrow, _, hr, htime, _⟩ :=
    WindowAction.run_emission_stages S rho hem
  subst t
  let n := NamedActionReads.windowActionReadFrom S a.val_index
    (NamedRun.stateBefore S rho i a.val_index) a.round
  let gc := NamedProfile.gradeContract n.cache
  change (Protocol.NamedDuties.attest_with gc S.E S.hc (S.node a.val_index)
    n.st n.record).2.2 = a at hrow
  change a.round = S.hc.round_of n.st.core.s at hr
  have hinv := WindowAction.windowRead_invariant S a.val_index
    (NamedRun.stateBefore S rho i a.val_index) ((S.node a.val_index).act a.round)
    (Proofs.NamedRuntime.stateBefore_invariants S rho i a.val_index).1
  have hcoh : Proofs.NamedStore.Coherent S.E S.cfg n.st := hinv.1.1
  have hpair : (Protocol.NamedActions.round_action_with gc S.E S.hc
      (S.node a.val_index) n.st.core.toHealing n.record).2.height_pair =
      .vote h root timeout := by
    change (Protocol.NamedDuties.attest_with gc S.E S.hc (S.node a.val_index)
      n.st n.record).2.2.height_pair = _
    rw [hrow]
    exact hp
  obtain ⟨nu, hfields⟩ := Proofs.NamedActions.round_action_names_source gc S.E S.hc
    (S.node a.val_index) n.st.core.toHealing n.record h root timeout hpair
  change (Protocol.fg_source_with gc S.E S.hc n.st.core.toHealing
      (S.hc.round_of n.st.core.s)
      (Protocol.grade2_block_with gc S.E S.hc n.st.core.toHealing
        (S.hc.round_of n.st.core.s))).map
      (fun q => ((n.st.core.σ q).h, (n.st.core.σ q).T_h.root,
        (n.st.core.σ q).nj)) = some (h, root, nu) at hfields
  rw [← hr] at hfields
  obtain ⟨raw, hraw, hvalues⟩ := Option.map_eq_some_iff.mp hfields
  have hmem : raw ∈ n.st.core.T :=
    NamedActionSources.frame_fg_source_mem S n.cache n.st a.round hinv hraw
  rw [hcoh.1] at hmem
  obtain ⟨source, hsource, he⟩ := Finset.mem_image.mp hmem
  rw [← he] at hraw hvalues
  rw [hcoh.2.2.2.2 source hsource] at hvalues
  have hheight : (Protocol.derive_named S.E S.cfg source).h = h :=
    congrArg Prod.fst hvalues
  have hroot : (Protocol.derive_named S.E S.cfg source).T_h.root = root :=
    congrArg (fun x : Height × BlockId × Bool => x.2.1) hvalues
  obtain ⟨entry, hentry, heEntry, hentryHeight⟩ :=
    Proofs.NamedEntryHeight.entry_ancestor_same_height S.E S.cfg source
  have heroot : entry.root = root :=
    (Proofs.NamedWire.erase_root entry).symm.trans ((congrArg Block.root heEntry).trans hroot)
  refine ⟨i, source, entry, ?_, hheight, heroot⟩
  refine ⟨hi, ho, hrow, hsource, hraw, hentry, heEntry, hentryHeight, timeout, ?_⟩
  simpa only [hheight, heroot] using hp


/-- Source extraction retains a supplied event index in a well-formed run. -/
theorem emitted_height_signed_source_at (S : Setup V) (rho : NamedRun V)
    (hnodup : rho.events.Nodup) {i : Nat} {a : NamedAttestation V}
    (hi : rho.events[i]? = some (.tick a.val_index ((S.node a.val_index).act a.round)))
    (hem : NamedObject.attest a ∈ NamedRun.emittedAt S rho i a.val_index
      ((S.node a.val_index).act a.round))
    {h : Height} {root : BlockId} {timeout : Bool}
    (hp : a.height_pair = .vote h root timeout) :
    ∃ source entry, WindowSignedSourceAt S rho i a source entry ∧
      (derive_named S.E S.cfg source).h = h ∧ entry.root = root := by
  obtain ⟨j, source, entry, hs, hh, hr⟩ :=
    emitted_height_signed_source S rho ⟨i, hi, hem⟩ hp
  obtain ⟨hiLen, hiGet⟩ := List.getElem?_eq_some_iff.mp hi
  obtain ⟨hjLen, hjGet⟩ := List.getElem?_eq_some_iff.mp hs.1
  have hij : i = j := (List.Nodup.getElem_inj_iff hnodup).mp (by rw [hiGet, hjGet])
  exact ⟨source, entry, hij ▸ hs, hh, hr⟩

/-- The extracted source belongs to the run even when it was proposed in
the same tick. The pre-tick store alone need not contain it. -/
theorem signed_source_entry_scope (S : Setup V) (rho : NamedRun V)
    {i : Nat} {a : NamedAttestation V} {source entry : NamedBlock V}
    (ha : a.val_index ∈ rho.honest)
    (hs : WindowSignedSourceAt S rho i a source entry) :
    NamedRun.blockInRun S rho source ∧ NamedRun.blockInRun S rho entry := by
  obtain ⟨hi, hem, _, hsource, _, hentry, _⟩ := hs
  have hawake := (WindowAction.run_emission_fields S
    (show NamedRun.emits S rho a.val_index (.attest a) _ from ⟨i, hi, hem⟩)).2.1
  have hpost : source ∈ (NamedRun.stateBefore S rho (i + 1) a.val_index).st.bodies := by
    rw [NamedRuntime.stateBefore_tick S rho hi]
    rw [WindowAction.tick_store_at_action S a.val_index _ a.round hawake]
    simpa only [NamedDuties.attest_with, NamedAdmission.admit_row_bodies] using hsource
  have hscope := NamedRuntime.blockInRun_of_direct S rho
    (NamedRuntime.directBlock_of_prefix S rho ha (i + 1) hpost)
  exact ⟨hscope, NamedRuntime.blockInRun_of_ancestor S rho hscope hentry⟩

/-- Admitting the emitted row does not change the retained bodies or the
FG projection read by the attestation. -/
theorem emission_post_projection (S : Setup V) (rho : NamedRun V)
    {i : Nat} {a : NamedAttestation V}
    (hi : rho.events[i]? = some (.tick a.val_index ((S.node a.val_index).act a.round)))
    (hem : NamedObject.attest a ∈ NamedRun.emittedAt S rho i a.val_index
      ((S.node a.val_index).act a.round)) :
    let n := NamedActionReads.windowActionReadFrom S a.val_index
      (NamedRun.stateBefore S rho i a.val_index) a.round
    let post := NamedRun.stateBefore S rho (i + 1) a.val_index
    post.st.bodies = n.st.bodies ∧ post.st.core.F = n.st.core.F ∧
      get_fg_root post.st.core.toHealing.toFG = get_fg_root n.st.core.toHealing.toFG ∧
      get_filtered_block_tree post.st.core.toHealing.toFG =
        get_filtered_block_tree n.st.core.toHealing.toFG := by
  have hawake := (WindowAction.run_emission_fields S
    (show NamedRun.emits S rho a.val_index (.attest a) _ from ⟨i, hi, hem⟩)).2.1
  dsimp only
  rw [NamedRuntime.stateBefore_tick S rho hi]
  change (Execution.NamedNode.tick S a.val_index _ _).1.st.bodies = _ ∧ _
  rw [WindowAction.tick_store_at_action S a.val_index _ a.round hawake]
  dsimp only [NamedDuties.attest_with, NamedAdmission.admit_row, on_sg_vote]
  split_ifs <;> exact ⟨rfl, rfl, rfl, rfl⟩

/-- The signed-source specialization of the actual emission projection. -/
theorem signed_source_post_projection (S : Setup V) (rho : NamedRun V)
    {i : Nat} {a : NamedAttestation V} {source entry : NamedBlock V}
    (hs : WindowSignedSourceAt S rho i a source entry) :
    let n := NamedActionReads.windowActionReadFrom S a.val_index
      (NamedRun.stateBefore S rho i a.val_index) a.round
    let post := NamedRun.stateBefore S rho (i + 1) a.val_index
    post.st.bodies = n.st.bodies ∧ post.st.core.F = n.st.core.F ∧
      get_fg_root post.st.core.toHealing.toFG = get_fg_root n.st.core.toHealing.toFG ∧
      get_filtered_block_tree post.st.core.toHealing.toFG =
        get_filtered_block_tree n.st.core.toHealing.toFG :=
  emission_post_projection S rho hs.1 hs.2.1

/-- The original signed-source contract is recovered at the point instance. -/
theorem signed_source_at_point (S : Setup V) (rho : NamedRun V)
    (hpoint : ∀ v r, (S.node v).act r = S.a r)
    (i : Nat) (a : NamedAttestation V) (source entry : NamedBlock V) :
    WindowSignedSourceAt S rho i a source entry ↔ SignedSourceAt S rho i a source entry := by
  simp only [WindowSignedSourceAt, SignedSourceAt, NamedActionReads.windowActionReadFrom,
    hpoint, WindowAction.windowReadFrom_point]
  rfl

/-- The pre-boundary history clause applies to actual emitted entries. -/
theorem signed_entry_pre_boundary (S : Setup V) (rho : NamedRun V)
    (b0 : Time) (P : NamedBlock V) (hP : NamedRun.blockInRun S rho P)
    (hno : NoHonestConflictAbove S rho b0 P.erase)
    {i : Nat} {a : NamedAttestation V} {source entry : NamedBlock V}
    (ha : a.val_index ∈ rho.honest)
    (hs : WindowSignedSourceAt S rho i a source entry)
    (ht : (S.node a.val_index).act a.round < b0) :
    NamedBlock.compatible P entry = true := by
  have hentryScope := (signed_source_entry_scope S rho ha hs).2
  obtain ⟨hi, hem, _, _, _, _, _, _, timeout, hp⟩ := hs
  exact hno.1 P hP rfl a _ ha ⟨i, hi, hem⟩ ht
    _ entry.root timeout hp entry hentryScope rfl

/-- Initialize the causal history on any event prefix strictly before `b0`. -/
theorem initial_intrinsic_history (S : Setup V) (rho : NamedRun V)
    (b0 : Time) (P : NamedBlock V) (n : Nat)
    (hP : NamedRun.blockInRun S rho P)
    (hno : NoHonestConflictAbove S rho b0 P.erase)
    (hcut : ∀ i, i < n → ∀ e, rho.events[i]? = some e → e.time < b0) :
    IntrinsicHighEntryHistoryIdx S rho P n := by
  intro i hin a source entry ha hs
  exact signed_entry_pre_boundary S rho b0 P hP hno ha hs (hcut i hin _ hs.1)

/-- At the point instance, the strict paper-time prefix contains exactly
the original prior-round signed entries. -/
theorem intrinsic_history_point_iff (S : Setup V) (rho : NamedRun V)
    (sch : NamedScheduleWellFormed S rho)
    (hpoint : ∀ v r, (S.node v).act r = S.a r) (P : NamedBlock V) (r : Round) :
    IntrinsicHighEntryHistoryIdx S rho P (strictEventCut rho (S.a r)) ↔
      IntrinsicHighEntryHistory S rho P r := by
  constructor
  · intro hh h entry he
    obtain ⟨i, a, source, ha, har, hs, _⟩ := he
    have htime : S.a a.round < S.a r := by
      have hnext := S.act_deadline_lt_next_a a.val_index a.round
      rw [hpoint] at hnext
      have hm := Assembly.a_mono S har
      have hd := S.E.Δ_pos
      linarith
    have hin := NamedStrictEventCut.lt_strictEventCut_of_time_lt rho sch.sorted
      (S.a r) hs.1 htime
    exact hh i hin a source entry ha ((signed_source_at_point S rho hpoint i a source entry).2 hs)
  · intro hh i hin a source entry ha hs
    have htime := NamedStrictEventCut.time_lt_of_lt_strictEventCut rho sch.sorted
      (S.a r) hin hs.1
    change (S.node a.val_index).act a.round < S.a r at htime
    rw [hpoint] at htime
    have har : a.round < r := by
      by_contra hn
      exact (not_le_of_gt htime) (Assembly.a_mono S (Nat.le_of_not_gt hn))
    exact hh _ entry ⟨i, a, source, ha, har,
      (signed_source_at_point S rho hpoint i a source entry).1 hs, rfl⟩

/-- The original scalar-cut base follows through the causal producer at
the point instance; no post-boundary prior-round emissions remain. -/
theorem initial_intrinsic_history_point (S : Setup V) (rho : NamedRun V)
    (sch : NamedScheduleWellFormed S rho)
    (hpoint : ∀ v r, (S.node v).act r = S.a r)
    (b0 : Time) (P : NamedBlock V) (r : Round)
    (hP : NamedRun.blockInRun S rho P)
    (hno : NoHonestConflictAbove S rho b0 P.erase)
    (hcut : S.a (r - 1) < b0) : IntrinsicHighEntryHistory S rho P r := by
  apply (intrinsic_history_point_iff S rho sch hpoint P r).1
  intro i hin a source entry ha hs
  have htime := NamedStrictEventCut.time_lt_of_lt_strictEventCut rho sch.sorted
    (S.a r) hin hs.1
  change (S.node a.val_index).act a.round < S.a r at htime
  rw [hpoint] at htime
  have har : a.round < r := by
    by_contra hn
    exact (not_le_of_gt htime) (Assembly.a_mono S (Nat.le_of_not_gt hn))
  apply signed_entry_pre_boundary S rho b0 P hP hno ha hs
  rw [hpoint]
  exact (Assembly.a_mono S (Nat.le_sub_one_of_lt har)).trans_lt hcut

#print axioms emitted_height_signed_source
#print axioms emitted_height_signed_source_at
#print axioms signed_source_entry_scope
#print axioms emission_post_projection
#print axioms signed_source_post_projection
#print axioms signed_source_at_point
#print axioms initial_intrinsic_history
#print axioms intrinsic_history_point_iff
#print axioms initial_intrinsic_history_point

end DecoupledConsensusModel.Proofs.NamedWindowIntrinsicEntry
