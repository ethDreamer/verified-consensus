module
public import DecoupledConsensusProofs.Protocol.Handlers.EventNonInterference
public import DecoupledConsensusProofs.Protocol.Grades.StragglerFrame
public import DecoupledConsensusProofs.Protocol.Grades.Q10Frame
public import DecoupledConsensusProofs.Execution.NamedAncestry
public import DecoupledConsensusProofs.Execution.BodyRetention
public import DecoupledConsensusProofs.Protocol.Handlers.FinalityMonotoneCore

/-!
# Causal compatibility of first-round straggler entries

The emission arm uses earlier-entry noninterference and the emitter's
pre-boundary frame. The receipt arm uses the crossing quorum and strict
causal row history. Neither arm assumes the straggler's emitted-head floor.
-/
@[expose] public section
namespace DecoupledConsensusModel.Proofs.NamedStragglerEntryHistory
open Execution Protocol Internal.NamedJointOutage Internal.NamedStableChainOutage
open NamedOutageClosure Internal.NamedOutageEntry
variable {V : Type} [DecidableEq V] [Fintype V]

omit [Fintype V] in
/-- Two named ancestors of one named block are comparable. Structural, so it
needs neither root injectivity nor a run scope. -/
private theorem named_common (B : NamedBlock V) :
    ∀ A C : NamedBlock V, NamedBlock.Preceq A B → NamedBlock.Preceq C B →
      NamedBlock.compatible A C = true := by
  induction B with
  | genesis =>
    intro A C hA hC
    have hA' : A = NamedBlock.genesis := by
      simpa only [NamedBlock.Preceq, NamedBlock.preceq, decide_eq_true_eq] using hA
    have hC' : C = NamedBlock.genesis := by
      simpa only [NamedBlock.Preceq, NamedBlock.preceq, decide_eq_true_eq] using hC
    subst hA'
    subst hC'
    simp only [NamedBlock.compatible, Bool.or_eq_true]
    exact Or.inl (NamedAncestry.named_self _)
  | node parent s root votes support rows proposer ih =>
    intro A C hA hC
    have hA' : A = NamedBlock.node parent s root votes support rows proposer ∨
        NamedBlock.Preceq A parent := by
      simpa only [NamedBlock.Preceq, NamedBlock.preceq, Bool.or_eq_true,
        decide_eq_true_eq] using hA
    have hC' : C = NamedBlock.node parent s root votes support rows proposer ∨
        NamedBlock.Preceq C parent := by
      simpa only [NamedBlock.Preceq, NamedBlock.preceq, Bool.or_eq_true,
        decide_eq_true_eq] using hC
    rcases hA' with rfl | hAp
    · rcases hC' with rfl | hCp
      · simp only [NamedBlock.compatible, Bool.or_eq_true]
        exact Or.inl (NamedAncestry.named_self _)
      · simp only [NamedBlock.compatible, Bool.or_eq_true]
        exact Or.inr (NamedAncestry.named_extend s root votes support rows proposer hCp)
    · rcases hC' with rfl | hCp
      · simp only [NamedBlock.compatible, Bool.or_eq_true]
        exact Or.inl (NamedAncestry.named_extend s root votes support rows proposer hAp)
      · exact ih A C hAp hCp


omit [Fintype V] in
private theorem compatible_ancestor_right {P A B : Block V}
    (hc : Block.compatible P B = true) (hAB : Block.Preceq A B) :
    Block.compatible P A = true := by
  rcases (show Block.Preceq P B ∨ Block.Preceq B P by
    simpa only [Block.compatible, Bool.or_eq_true] using! hc) with hPB | hBP
  · exact Block.compatible_of_preceq_common hPB hAB
  · simp only [Block.compatible, Bool.or_eq_true]
    exact Or.inr (Block.preceq_trans hAB hBP)

/-- A nonempty source lies above the protected prefix if its frozen G2
root covers that prefix and the FG projection preserves it. -/
theorem source_above_of_frame (S : Setup V) (n : NamedNodeState V) (r : Round)
    (P source : Block V)
    (hfg : Block.Preceq P (get_fg_root n.st.core.toHealing.toFG) ∨
      P ∈ get_filtered_block_tree n.st.core.toHealing.toFG)
    (hframe : Block.Preceq P n.st.core.F ∨
      ∃ raw, (readFrame n.cache n.st.core.toHealing r).g2 = some (some raw) ∧
        Block.Preceq P raw)
    (hs : fg_source_with (NamedProfile.gradeContract n.cache) S.E S.hc n.st.core.toHealing r
      (grade2_block_with (NamedProfile.gradeContract n.cache) S.E S.hc n.st.core.toHealing r) =
        some source) : Block.Preceq P source := by
  unfold fg_source_with at hs
  cases hq : grade2_block_with (NamedProfile.gradeContract n.cache) S.E S.hc
      n.st.core.toHealing r with
  | none => simp only [hq, reduceCtorEq] at hs
  | some q =>
    have hactive : ∃ raw, (readFrame n.cache n.st.core.toHealing r).g2 = some (some raw) ∧
        activePrefix (get_filtered_block_tree n.st.core.toHealing.toFG) raw = some q := by
      change grade2Block _ _ = some q at hq
      unfold grade2Block at hq
      split_ifs at hq with hclosed
      · cases hg : (readFrame n.cache n.st.core.toHealing r).g2 with
        | none => simp [hg] at hq
        | some value =>
          cases value with
          | none => simp [hg] at hq
          | some raw => exact ⟨raw, rfl, by simpa only [hg, Option.bind_some, id_eq] using hq⟩
    obtain ⟨raw, hraw, hact⟩ := hactive
    have hqmem := NamedProposalParent.activePrefix_mem _ raw q hact
    have hPq : Block.Preceq P q := by
      rcases hframe with hPF | ⟨raw', hraw', hPraw⟩
      · exact Block.preceq_trans hPF (q10_filtered_F hqmem)
      · have hrr : raw' = raw := Option.some.inj (Option.some.inj (hraw'.symm.trans hraw))
        subst raw'
        rcases hfg with hProot | hPmem
        · have hrootq : Block.Preceq (get_fg_root n.st.core.toHealing.toFG) q :=
            (Finset.mem_filter.mp hqmem).2
          exact Block.preceq_trans hProot hrootq
        · obtain ⟨q', hq', hPq'⟩ := q10_activePrefix_dominates hPmem hPraw
          have heq : q' = q := Option.some.inj (hq'.symm.trans hact)
          exact heq ▸ hPq'
    simp only [hq] at hs
    cases hd : deepest_clear (some q) n.st.core.toHealing.live_confirmed
        ((NamedProfile.gradeContract n.cache).read S.E S.hc n.st.core.toHealing r).clear with
    | none =>
      rw [hd] at hs
      exact Option.some.inj hs ▸ hPq
    | some B =>
      rw [hd] at hs
      have hqB : Block.Preceq q B := (Finset.mem_filter.mp (Engine.deepest?_mem hd)).2.1
      exact Option.some.inj hs ▸ Block.preceq_trans hPq hqB

/-- The post-boundary straggler entry is compatible using only entries
strictly before its own emission event. -/
theorem straggler_entry_compatible
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time) (s r : Round) (P : NamedBlock V)
    (hexec : OutageExecution S rho b0 b1) (hmargin : FormationMargin S s b0)
    (hsleep : OutageSleepyThroughout S rho) (hP : NamedRun.blockInRun S rho P)
    (hmin : ∀ q : Round, 0 < q → b0 ≤ S.a q → r ≤ q)
    (hfirst : S.a (r - 1) < b0) (hframes : PreBoundaryFrames S rho b0 s P.erase)
    (hheld0 : ∀ v ∈ rho.honest, P ∈ (NamedRun.stateBeforeTime S rho b0 v).st.bodies)
    {i : Nat} {a : NamedAttestation V} {source entry : NamedBlock V}
    (hhistory : IntrinsicHighEntryHistoryIdx S rho P i) (ha : a.val_index ∈ rho.honest)
    (hs : WindowSignedSourceAt S rho i a source entry)
    (hb : b0 ≤ (S.node a.val_index).act a.round) (har : a.round < r) :
    NamedBlock.compatible P entry = true := by
  let n := NamedActionReads.windowActionReadFrom S a.val_index
    (NamedRun.stateBefore S rho i a.val_index) a.round
  have hproj := NamedWindowIntrinsicEntry.signed_source_post_projection S rho hs
  have hprefix := NamedRuntime.tick_prefix_eq_strict S rho hexec.core.sorted hexec.core.nodup hs.1
  have hboundary : strictEventCut rho b0 ≤ i := by
    by_contra hn
    have ht := NamedStrictEventCut.time_lt_of_lt_strictEventCut rho hexec.core.sorted b0
      (Nat.lt_of_not_ge hn) hs.1
    exact (not_lt_of_ge hb) ht
  have hheld : P ∈ (NamedRun.stateBefore S rho (i + 1) a.val_index).st.bodies := by
    have hh := hheld0 a.val_index ha
    rw [NamedStrictEventCut.stateBeforeTime_eq_idx S rho hexec.core.sorted] at hh
    exact NamedBodyRetention.stateBefore_bodies_mono S rho a.val_index
      (hboundary.trans (Nat.le_succ i)) hh
  obtain ⟨hfg, hcompat⟩ := NamedEventNonInterference.fg_noninterference_at_event
    S rho b0 b1 s i P hexec hmargin hsleep hhistory a.val_index ha hheld
  rw [hproj.2.1] at hcompat
  rw [hproj.2.2.1, hproj.2.2.2] at hfg
  have hmono : Block.Preceq (NamedRun.stateBefore S rho i a.val_index).st.core.F n.st.core.F := by
    rw [← hproj.2.1]
    exact Protocol.stateBefore_F_mono S rho a.val_index (Nat.le_succ i)
  have hbeforeCompat := compatible_ancestor_right hcompat hmono
  have hframe := straggler_frame_at_action S rho hexec.core b0 s r P hmargin hmin hfirst
    hframes ha (show NamedRun.emits S rho a.val_index (.attest a) _ from ⟨i, hs.1, hs.2.1⟩)
    hb har
  dsimp only at hframe
  rw [← hprefix] at hframe
  have hframeN : Block.Preceq P.erase n.st.core.F ∨
      ∃ raw, (readFrame n.cache n.st.core.toHealing a.round).g2 = some (some raw) ∧
        Block.Preceq P.erase raw := by
    rcases hframe with hF | ⟨raw, hPraw, hraw⟩
    · exact Or.inl (Block.preceq_trans hF hmono)
    · refine Or.inr ⟨_,
        FrameForward.frame_phase_window_eq S rho i a.val_index a.round .g2 _ hraw, ?_⟩
      exact (q10_retained_prefix _ _ _ hcompat).2
        ((q10_retained_prefix _ _ _ hbeforeCompat).2 hPraw)
  have hPsource := source_above_of_frame S n a.round P.erase source.erase hfg hframeN hs.2.2.2.2.1
  obtain ⟨A, hAsource, hAP⟩ := NamedAncestry.erased_ancestor_lift source hPsource
  have hsourceScope := (NamedWindowIntrinsicEntry.signed_source_entry_scope S rho ha hs).1
  have hroot : A.root = P.root := by
    rw [← NamedWire.erase_root A, ← NamedWire.erase_root P, hAP]
  have heq : A = P := hexec.core.root_injective source P hsourceScope hP A P
    (Or.inl hAsource) (Or.inr (NamedAncestry.named_self P)) hroot
  subst A
  exact named_common source P entry hAsource hs.2.2.2.2.2.1

#print axioms source_above_of_frame
#print axioms straggler_entry_compatible

/-- Every prior-round action lies strictly before the next round's G0
completion; in particular the causal base domain contains every straggler. -/
theorem action_before_completion_of_round_lt (S : Setup V) (v : V) {q r : Round}
    (hqr : q < r) : (S.node v).act q < domain S.E S.hc r .g0 := by
  have hend := S.act_before_round_end v q
  have hm := S.hc.domain_mono S.E .g1 hqr
  simp only [domain, Phase.domainOffset, zero_mul, add_zero] at hm
  have hd := S.E.Δ_pos
  simp only [domain, Phase.domainOffset, one_mul]
  linarith

/-- Before the first included round's G0 completion, honest entries and
the conflicting-carrier band follow jointly by strict event induction.
Pre-boundary events use the initial history; post-boundary emissions are
stragglers. A carrier at event `i` uses only entries strictly before `i`.
This is a causal base producer, not a replacement paper-checkpoint bound. -/
theorem first_round_event_history
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time) (s r : Round) (P : NamedBlock V)
    (hexec : OutageExecution S rho b0 b1) (hmargin : FormationMargin S s b0)
    (hsleep : OutageSleepyThroughout S rho) (hP : NamedRun.blockInRun S rho P)
    (hno : NoHonestConflictAbove S rho b0 P.erase)
    (hmin : ∀ q : Round, 0 < q → b0 ≤ S.a q → r ≤ q)
    (hfirst : S.a (r - 1) < b0) (hframes : PreBoundaryFrames S rho b0 s P.erase)
    (hheld0 : ∀ v ∈ rho.honest, P ∈ (NamedRun.stateBeforeTime S rho b0 v).st.bodies) :
    ∀ n, n ≤ strictEventCut rho (domain S.E S.hc r .g0) →
      IntrinsicHighEntryHistoryIdx S rho P n ∧ IntrinsicConflictingCarrierBandIdx S rho P n := by
  have hinit := NamedWindowIntrinsicEntry.initial_intrinsic_history S rho b0 P
    (strictEventCut rho b0) hP hno (fun i hi e he =>
      NamedStrictEventCut.time_lt_of_lt_strictEventCut rho hexec.core.sorted b0 hi he)
  have hall : IntrinsicHighEntryHistoryIdx S rho P
      (strictEventCut rho (domain S.E S.hc r .g0)) := by
    intro i
    induction i using Nat.strong_induction_on with
    | h i ih =>
      intro hi a source entry ha hs
      by_cases hb : (S.node a.val_index).act a.round < b0
      · exact hinit i (NamedStrictEventCut.lt_strictEventCut_of_time_lt rho hexec.core.sorted
          b0 hs.1 hb) a source entry ha hs
      · have hhistory : IntrinsicHighEntryHistoryIdx S rho P i := by
          intro j hj a' source' entry' ha' hs'
          exact ih j hj (hj.trans hi) a' source' entry' ha' hs'
        have ht := NamedStrictEventCut.time_lt_of_lt_strictEventCut rho hexec.core.sorted
          (domain S.E S.hc r .g0) hi hs.1
        have har := S.round_lt_of_act_lt_domain a.val_index ht
        exact straggler_entry_compatible S rho b0 b1 s r P hexec hmargin hsleep hP
          hmin hfirst hframes hheld0 hhistory ha hs (le_of_not_gt hb) har
  intro n hn
  have hh : IntrinsicHighEntryHistoryIdx S rho P n := by
    intro i hi a source entry ha hs
    exact hall i (lt_of_lt_of_le hi hn) a source entry ha hs
  exact ⟨hh, NamedEventConflictingCarrierBand.intrinsic_conflicting_carrier_band
    S rho b0 b1 s n P hexec hmargin hsleep hh⟩

/-- The event induction recovers both original first-round producers at
the point instance, without moving the paper checkpoint. -/
theorem first_round_event_history_point
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time) (s r : Round) (P : NamedBlock V)
    (hexec : OutageExecution S rho b0 b1) (hmargin : FormationMargin S s b0)
    (hsleep : OutageSleepyThroughout S rho) (hP : NamedRun.blockInRun S rho P)
    (hno : NoHonestConflictAbove S rho b0 P.erase)
    (hmin : ∀ q : Round, 0 < q → b0 ≤ S.a q → r ≤ q)
    (hfirst : S.a (r - 1) < b0) (hframes : PreBoundaryFrames S rho b0 s P.erase)
    (hheld0 : ∀ v ∈ rho.honest, P ∈ (NamedRun.stateBeforeTime S rho b0 v).st.bodies)
    (hpoint : ∀ v q, (S.node v).act q = S.a q) :
    IntrinsicHighEntryHistory S rho P r ∧ IntrinsicConflictingCarrierBand S rho P r := by
  have hh := (first_round_event_history S rho b0 b1 s r P hexec hmargin hsleep hP
    hno hmin hfirst hframes hheld0 _ le_rfl).1
  have hlegacy : IntrinsicHighEntryHistory S rho P r := by
    intro h entry he
    obtain ⟨i, a, source, ha, har, hs, _⟩ := he
    have hws := (NamedWindowIntrinsicEntry.signed_source_at_point S rho hpoint
      i a source entry).2 hs
    have hi := NamedStrictEventCut.lt_strictEventCut_of_time_lt rho hexec.core.sorted
      (domain S.E S.hc r .g0) hws.1 (action_before_completion_of_round_lt S a.val_index har)
    exact hh i hi a source entry ha hws
  exact ⟨hlegacy, NamedEventConflictingCarrierBand.intrinsic_conflicting_carrier_band_point
    S rho b0 b1 s r P hexec hmargin hsleep hpoint hlegacy⟩

#print axioms first_round_event_history
#print axioms first_round_event_history_point
#print axioms action_before_completion_of_round_lt

end DecoupledConsensusModel.Proofs.NamedStragglerEntryHistory
