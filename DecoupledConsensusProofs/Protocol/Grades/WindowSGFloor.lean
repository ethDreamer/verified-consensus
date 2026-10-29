module
public import DecoupledConsensusProofs.Protocol.Grades.StragglerEntryHistory
public import DecoupledConsensusProofs.Protocol.Grades.HonestArrival

/-!
# SG floors at actual action inputs

Connects the causal frame and FG result to the SG selector. The grade-2 to
anchor relation is evaluated after the action's earlier duties, and grade 0
may complete exactly at that action under P1.
-/
@[expose] public section
namespace DecoupledConsensusModel.Proofs.NamedWindowSGFloor
open Execution Protocol Internal.NamedJointOutage Internal.NamedStableChainOutage
open Internal.NamedOutageEntry NamedOutageClosure
variable {V : Type} [DecidableEq V] [Fintype V]

/-- All phases are closed at an actual honest action, and its active G2
candidate precedes its anchor. This includes the G0-completion endpoint. -/
theorem action_grade_geometry (S : Setup V) (rho : NamedRun V)
    (core : NamedAdmissibleCore S rho) {i : Nat} {a : NamedAttestation V}
    (ha : a.val_index ∈ rho.honest) (hr : 0 < a.round)
    (hi : rho.events[i]? = some (.tick a.val_index ((S.node a.val_index).act a.round)))
    (hem : NamedObject.attest a ∈ NamedRun.emittedAt S rho i a.val_index
      ((S.node a.val_index).act a.round)) :
    let n := NamedActionReads.windowActionReadFrom S a.val_index
      (NamedRun.stateBefore S rho i a.val_index) a.round
    let frame := readFrame n.cache n.st.core.toHealing a.round
    allClosed frame = true ∧
      ∀ q, grade2Block n.st.core.toHealing frame = some q →
        Block.Preceq q (anchor S.E S.hc n.st.core.toHealing a.round frame.g1) := by
  let n := NamedActionReads.windowActionReadFrom S a.val_index
    (NamedRun.stateBefore S rho i a.val_index) a.round
  have hproj := NamedWindowIntrinsicEntry.emission_post_projection S rho hi hem
  have hmono : Block.Preceq (NamedRun.stateBefore S rho i a.val_index).st.core.F n.st.core.F := by
    rw [← hproj.2.1]
    exact Protocol.stateBefore_F_mono S rho a.val_index (Nat.le_succ i)
  have hclosed : ∀ p, phaseResult (readFrame n.cache n.st.core.toHealing a.round) p ≠ none := by
    intro p
    rcases lt_or_eq_of_le (S.domain_le_act a.val_index a.round p) with hlt | heq
    · have hphase := FrameCompleted.frame_phase_completed_window S rho core a.val_index ha
        a.round hr p i hi hlt hmono
      dsimp only at hphase
      rw [hphase]
      exact Option.some_ne_none _
    · exact FrameCompleted.frame_phase_closed_at_window_domain S rho i a.val_index a.round p heq.symm
  refine ⟨?_, ?_⟩
  · have h0 := hclosed .g0
    have h1 := hclosed .g1
    have h2 := hclosed .g2
    simpa only [allClosed, Bool.and_eq_true, Option.isSome_iff_ne_none, phaseResult] using
      And.intro (And.intro h0 h1) h2
  · intro q hq
    have ht1 : domain S.E S.hc a.round .g1 < (S.node a.val_index).act a.round := by
      have hp := S.act_post_completion a.val_index a.round
      have hd := S.E.Δ_pos
      simp only [domain, Phase.domainOffset] at hp ⊢
      linarith
    have ht2 : domain S.E S.hc a.round .g2 < (S.node a.val_index).act a.round := by
      have hp := S.act_post_completion a.val_index a.round
      have hd := S.E.Δ_pos
      simp only [domain, Phase.domainOffset] at hp ⊢
      linarith
    have hprefix := NamedRuntime.tick_prefix_eq_strict S rho core.sorted core.nodup hi
    have hFdomain : Block.Preceq
        (NamedRun.stateBeforeTime S rho (domain S.E S.hc a.round .g1) a.val_index).st.core.F
        n.st.core.F := by
      rw [hprefix] at hmono
      exact Block.preceq_trans (stateBeforeTime_F_mono_of_le S rho core.sorted ht1.le) hmono
    exact q10_frame_core S rho core a.val_index ha a.round hr n.st.core.toHealing
      (readFrame n.cache n.st.core.toHealing a.round) hFdomain
      (FrameCompleted.frame_phase_completed_window S rho core a.val_index ha
        a.round hr .g2 i hi ht2 hmono)
      (FrameCompleted.frame_phase_completed_window S rho core a.val_index ha
        a.round hr .g1 i hi ht1 hmono) q hq

omit [Fintype V] in
private theorem grade2_mem {st : HealingStore V} {frame : Frame V} {q : Block V}
    (h : grade2Block st frame = some q) : q ∈ get_filtered_block_tree st.toFG := by
  unfold grade2Block at h
  split_ifs at h with hc
  obtain ⟨raw, _, hraw⟩ := Option.bind_eq_some_iff.mp h
  exact NamedProposalParent.activePrefix_mem _ raw q hraw

private theorem root_below_anchor (S : Setup V) (st : HealingStore V) (r : Round)
    (g1 : Option (Option (Block V))) :
    Block.Preceq (get_fg_root st.toFG) (anchor S.E S.hc st r g1) := by
  cases g1 with
  | none => exact Block.preceq_self _
  | some value =>
    cases value with
    | none => exact Block.preceq_self _
    | some raw =>
      change Block.Preceq _ ((activePrefix (get_filtered_block_tree st.toFG) raw).getD _)
      cases he : activePrefix (get_filtered_block_tree st.toFG) raw with
      | none => exact Block.preceq_self _
      | some q => exact (Finset.mem_filter.mp (NamedProposalParent.activePrefix_mem _ raw q he)).2

/-- The SG selector preserves a protected prefix in either FG arm once
the actual frame is closed and its G2-to-anchor relation holds. -/
theorem sg_above_of_frame (S : Setup V) (n : NamedNodeState V) (r : Round) (P : Block V)
    (hFroot : Block.Preceq n.st.core.F (get_fg_root n.st.core.toHealing.toFG))
    (hfg : Block.Preceq P (get_fg_root n.st.core.toHealing.toFG) ∨
      P ∈ get_filtered_block_tree n.st.core.toHealing.toFG)
    (hframe : Block.Preceq P n.st.core.F ∨
      ∃ raw, (readFrame n.cache n.st.core.toHealing r).g2 = some (some raw) ∧
        Block.Preceq P raw)
    (hclosed : allClosed (readFrame n.cache n.st.core.toHealing r) = true)
    (hqanchor : ∀ q, grade2Block n.st.core.toHealing (readFrame n.cache n.st.core.toHealing r) =
      some q → Block.Preceq q (anchor S.E S.hc n.st.core.toHealing r
        (readFrame n.cache n.st.core.toHealing r).g1)) :
    Block.Preceq P (currentSGVote n.st.core.toHealing
      (frameGradeRead n.cache S.E S.hc n.st.core.toHealing r)) := by
  have hrootCase (hroot : Block.Preceq P (get_fg_root n.st.core.toHealing.toFG)) :
      Block.Preceq P (currentSGVote n.st.core.toHealing
        (frameGradeRead n.cache S.E S.hc n.st.core.toHealing r)) := by
    have ha := Block.preceq_trans hroot
      (root_below_anchor S n.st.core.toHealing r (readFrame n.cache n.st.core.toHealing r).g1)
    unfold currentSGVote
    split
    · rename_i B hB
      exact Block.preceq_trans ha (Finset.mem_filter.mp (Engine.deepest?_mem hB)).2.1
    · split
      · rename_i q hq
        exact Block.preceq_trans hroot (Finset.mem_filter.mp (grade2_mem hq)).2
      · split_ifs <;> assumption
  rcases hfg with hroot | hmem
  · exact hrootCase hroot
  rcases hframe with hPF | ⟨raw, hraw, hPraw⟩
  · exact hrootCase (Block.preceq_trans hPF hFroot)
  obtain ⟨q, hq, hPq⟩ := q10_activePrefix_dominates hmem hPraw
  have hgrade : grade2Block n.st.core.toHealing (readFrame n.cache n.st.core.toHealing r) = some q := by
    simp only [grade2Block, hclosed, ite_true, hraw, Option.bind_some, id_eq, hq]
  have hanchor := hqanchor q hgrade
  unfold currentSGVote
  split
  · rename_i B hB
    exact Block.preceq_trans (Block.preceq_trans hPq hanchor)
      (Finset.mem_filter.mp (Engine.deepest?_mem hB)).2.1
  · change Block.Preceq P (match grade2Block n.st.core.toHealing
        (readFrame n.cache n.st.core.toHealing r) with
        | some q => q
        | none => _)
    rw [hgrade]
    exact hPq

#print axioms action_grade_geometry
#print axioms sg_above_of_frame

/-- The opening SG conclusion supplies the actual selector floor when
strictly earlier causal entries preserve its FG projection (PROTOCOL.md `sec:grades`). -/
theorem sg_floor_at_event_of_opening
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time) (s : Round) (P : NamedBlock V)
    (hexec : OutageExecution S rho b0 b1) (hmargin : FormationMargin S s b0)
    (hsleep : OutageSleepyThroughout S rho)
    (hheld0 : ∀ v ∈ rho.honest, P ∈ (NamedRun.stateBeforeTime S rho b0 v).st.bodies)
    {i : Nat} {a : NamedAttestation V}
    (hh : IntrinsicHighEntryHistoryIdx S rho P i)
    (ha : a.val_index ∈ rho.honest) (hr : 0 < a.round)
    (hi : rho.events[i]? = some (.tick a.val_index ((S.node a.val_index).act a.round)))
    (hem : NamedObject.attest a ∈ NamedRun.emittedAt S rho i a.val_index
      ((S.node a.val_index).act a.round))
    (hb : b0 ≤ (S.node a.val_index).act a.round)
    (hopening : let n := NamedRun.readAt S rho (domain S.E S.hc a.round .g1) a.val_index
      Block.Preceq P.erase n.st.core.F ∨
        ∃ raw, (readFrame n.cache n.st.core.toHealing a.round).g2 = some (some raw) ∧
          Block.Preceq P.erase raw) :
    let n := NamedActionReads.windowActionReadFrom S a.val_index
      (NamedRun.stateBefore S rho i a.val_index) a.round
    Block.Preceq P.erase (currentSGVote n.st.core.toHealing
      (frameGradeRead n.cache S.E S.hc n.st.core.toHealing a.round)) := by
  obtain ⟨hfg, _, hframe⟩ := NamedStragglerEntryHistory.action_frame_of_opening
    S rho b0 b1 s P hexec hmargin hsleep hheld0 hh ha hi hem hb hopening
  obtain ⟨hclosed, hqanchor⟩ := action_grade_geometry S rho hexec.core ha hr hi hem
  have hproj := NamedWindowIntrinsicEntry.emission_post_projection S rho hi hem
  have hFroot := Records.preceq_get_fg_root_of_F
    (st := (NamedRun.stateBefore S rho (i + 1) a.val_index).st.core.toHealing.toFG)
    (NamedStoreBridge.finalized_preceq_justified_stateBefore S rho (i + 1) a.val_index)
  change Block.Preceq (NamedRun.stateBefore S rho (i + 1) a.val_index).st.core.F
    (get_fg_root (NamedRun.stateBefore S rho (i + 1) a.val_index).st.core.toHealing.toFG) at hFroot
  rw [hproj.2.1, hproj.2.2.1] at hFroot
  exact sg_above_of_frame S _ a.round P.erase hFroot hfg hframe hclosed hqanchor

/-- Actual emitted heads inherit the opening SG floor. The history covers
late actions as well as actions before the paper cut (PROTOCOL.md `sec:grades`). -/
theorem confirmed_head_floor_of_opening
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time) (s : Round) (P : NamedBlock V)
    (hexec : OutageExecution S rho b0 b1) (hmargin : FormationMargin S s b0)
    (hsleep : OutageSleepyThroughout S rho)
    (hheld0 : ∀ v ∈ rho.honest, P ∈ (NamedRun.stateBeforeTime S rho b0 v).st.bodies)
    {a : NamedAttestation V} {t : Time}
    (hhistory : IntrinsicHighEntryHistoryIdx S rho P
      (strictEventCut rho (domain S.E S.hc (a.round + 1) .g0)))
    (ha : a.val_index ∈ rho.honest) (hr : 0 < a.round)
    (hem : NamedRun.emits S rho a.val_index (.attest a) t) (hb : b0 ≤ t)
    (hopening : let n := NamedRun.readAt S rho (domain S.E S.hc a.round .g1) a.val_index
      Block.Preceq P.erase n.st.core.F ∨
        ∃ raw, (readFrame n.cache n.st.core.toHealing a.round).g2 = some (some raw) ∧
          Block.Preceq P.erase raw)
    (key : BlockId) (hkey : a.confirmed = some key) (K : NamedBlock V)
    (hK : NamedRun.blockInRun S rho K) (hKroot : K.root = key) :
    Block.Preceq P.erase K.erase := by
  obtain ⟨i, hi, hemit, hrow, _, hro, htime, _⟩ := WindowAction.run_emission_stages S rho hem
  subst t
  let n := NamedActionReads.windowActionReadFrom S a.val_index
    (NamedRun.stateBefore S rho i a.val_index) a.round
  let gc := NamedProfile.gradeContract n.cache
  let Bsg := get_sg_vote_with gc S.E S.hc n.st.core.toHealing a.round
    (grade2_block_with gc S.E S.hc n.st.core.toHealing a.round)
  have hic := NamedStrictEventCut.lt_strictEventCut_of_time_lt rho hexec.core.sorted
    (domain S.E S.hc (a.round + 1) .g0) hi
    (NamedStragglerEntryHistory.action_before_completion_of_round_lt S a.val_index
      (Nat.lt_succ_self a.round))
  have hh : IntrinsicHighEntryHistoryIdx S rho P i := by
    intro j hj b source entry ha hs
    exact hhistory j (hj.trans hic) b source entry ha hs
  have hfloor : Block.Preceq P.erase Bsg := sg_floor_at_event_of_opening S rho b0 b1 s P
    hexec hmargin hsleep hheld0 hh ha hr hi hemit hb hopening
  change (NamedDuties.attest_with gc S.E S.hc (S.node a.val_index) n.st n.record).2.2 = a at hrow
  change a.round = S.hc.round_of n.st.core.s at hro
  have hconf : a.confirmed = some Bsg.root := by
    rw [← hrow]
    change some (get_sg_vote_with gc S.E S.hc n.st.core.toHealing (S.hc.round_of n.st.core.s)
      (grade2_block_with gc S.E S.hc n.st.core.toHealing (S.hc.round_of n.st.core.s))).root = _
    rw [← hro]
  have hkeyB : key = Bsg.root := Option.some.inj (hkey.symm.trans hconf)
  have hinv : NamedConfirmationMembership.Invariant S.E S.cfg n.st :=
    WindowAction.windowRead_invariant S a.val_index
    (NamedRun.stateBefore S rho i a.val_index) ((S.node a.val_index).act a.round)
    (NamedRuntime.stateBefore_invariants S rho i a.val_index).1
  have hmem : Bsg ∈ n.st.core.T := by
    have hm := NamedConfirmationMembership.sg_head_mem n.cache S.E S.hc S.cfg n.st hinv
    rw [← hro] at hm
    exact hm
  rw [hinv.1.1.1] at hmem
  obtain ⟨H, hH, hHe⟩ := Finset.mem_image.mp hmem
  have hproj := NamedWindowIntrinsicEntry.emission_post_projection S rho hi hemit
  have hHpost : H ∈ (NamedRun.stateBefore S rho (i + 1) a.val_index).st.bodies := by
    rw [hproj.1]
    exact hH
  have hHrun := NamedRuntime.blockInRun_of_direct S rho
    (NamedRuntime.directBlock_of_prefix S rho ha (i + 1) hHpost)
  have hroot : H.root = K.root := by
    rw [hKroot, hkeyB, ← hHe, NamedWire.erase_root]
  have heq : H = K := hexec.core.root_injective H K hHrun hK H K
    (Or.inl (NamedAncestry.named_self H)) (Or.inr (NamedAncestry.named_self K)) hroot
  rw [← heq, hHe]
  exact hfloor

#print axioms sg_floor_at_event_of_opening
#print axioms confirmed_head_floor_of_opening

/-- The straggler SG floor is derived from the causal induction and the
existing pre-boundary frames; it is not an outage premise. -/
theorem straggler_sg_floor_at_event
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time) (s r : Round) (P : NamedBlock V)
    (hexec : OutageExecution S rho b0 b1) (hmargin : FormationMargin S s b0)
    (hsleep : OutageSleepyThroughout S rho) (hP : NamedRun.blockInRun S rho P)
    (hno : NoHonestConflictAbove S rho b0 P.erase)
    (hmin : ∀ q : Round, 0 < q → b0 ≤ S.a q → r ≤ q)
    (hfirst : S.a (r - 1) < b0) (hframes : PreBoundaryFrames S rho b0 s P.erase)
    (hheld0 : ∀ v ∈ rho.honest, P ∈ (NamedRun.stateBeforeTime S rho b0 v).st.bodies)
    {i : Nat} {a : NamedAttestation V} (ha : a.val_index ∈ rho.honest)
    (hi : rho.events[i]? = some (.tick a.val_index ((S.node a.val_index).act a.round)))
    (hem : NamedObject.attest a ∈ NamedRun.emittedAt S rho i a.val_index
      ((S.node a.val_index).act a.round))
    (hb : b0 ≤ (S.node a.val_index).act a.round) (har : a.round < r) :
    let n := NamedActionReads.windowActionReadFrom S a.val_index
      (NamedRun.stateBefore S rho i a.val_index) a.round
    Block.Preceq P.erase (currentSGVote n.st.core.toHealing
      (frameGradeRead n.cache S.E S.hc n.st.core.toHealing a.round)) := by
  have hic := NamedStrictEventCut.lt_strictEventCut_of_time_lt rho hexec.core.sorted
    (domain S.E S.hc r .g0) hi
    (NamedStragglerEntryHistory.action_before_completion_of_round_lt S a.val_index har)
  have hh := (NamedStragglerEntryHistory.first_round_event_history S rho b0 b1 s r P
    hexec hmargin hsleep hP hno hmin hfirst hframes hheld0 i ((Nat.le_succ i).trans hic)).1
  obtain ⟨hfg, _, hframe⟩ := NamedStragglerEntryHistory.straggler_action_frame S rho b0 b1 s r P
    hexec hmargin hsleep hmin hfirst hframes hheld0 hh ha hi hem hb har
  have hr : 0 < a.round := lt_of_lt_of_le (Nat.succ_pos s)
    (straggler_preBoundary_round S rho b0 s r hmargin hmin hfirst ⟨i, hi, hem⟩ hb har).1
  obtain ⟨hclosed, hqanchor⟩ := action_grade_geometry S rho hexec.core ha hr hi hem
  have hproj := NamedWindowIntrinsicEntry.emission_post_projection S rho hi hem
  have hFroot := Records.preceq_get_fg_root_of_F
    (st := (NamedRun.stateBefore S rho (i + 1) a.val_index).st.core.toHealing.toFG)
    (NamedStoreBridge.finalized_preceq_justified_stateBefore S rho (i + 1) a.val_index)
  change Block.Preceq (NamedRun.stateBefore S rho (i + 1) a.val_index).st.core.F
    (get_fg_root (NamedRun.stateBefore S rho (i + 1) a.val_index).st.core.toHealing.toFG) at hFroot
  rw [hproj.2.1, hproj.2.2.1] at hFroot
  exact sg_above_of_frame S _ a.round P.erase hFroot hfg hframe hclosed hqanchor

/-- Every named confirmed head of an honest prior-round straggler covers
the protected prefix. No delivery timing or nonempty height pair is required. -/
theorem straggler_confirmed_head_floor
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time) (s r : Round) (P : NamedBlock V)
    (hexec : OutageExecution S rho b0 b1) (hmargin : FormationMargin S s b0)
    (hsleep : OutageSleepyThroughout S rho) (hP : NamedRun.blockInRun S rho P)
    (hno : NoHonestConflictAbove S rho b0 P.erase)
    (hmin : ∀ q : Round, 0 < q → b0 ≤ S.a q → r ≤ q)
    (hfirst : S.a (r - 1) < b0) (hframes : PreBoundaryFrames S rho b0 s P.erase)
    (hheld0 : ∀ v ∈ rho.honest, P ∈ (NamedRun.stateBeforeTime S rho b0 v).st.bodies)
    {a : NamedAttestation V} {t : Time} (ha : a.val_index ∈ rho.honest)
    (hem : NamedRun.emits S rho a.val_index (.attest a) t)
    (hb : b0 ≤ t) (har : a.round < r)
    (key : BlockId) (hkey : a.confirmed = some key) (K : NamedBlock V)
    (hK : NamedRun.blockInRun S rho K) (hKroot : K.root = key) :
    Block.Preceq P.erase K.erase := by
  obtain ⟨i, hi, hemit, hrow, _, hro, htime, _⟩ := WindowAction.run_emission_stages S rho hem
  subst t
  let n := NamedActionReads.windowActionReadFrom S a.val_index
    (NamedRun.stateBefore S rho i a.val_index) a.round
  let gc := NamedProfile.gradeContract n.cache
  let Bsg := get_sg_vote_with gc S.E S.hc n.st.core.toHealing a.round
    (grade2_block_with gc S.E S.hc n.st.core.toHealing a.round)
  have hfloor : Block.Preceq P.erase Bsg := straggler_sg_floor_at_event S rho b0 b1 s r P
    hexec hmargin hsleep hP hno hmin hfirst hframes hheld0 ha hi hemit hb har
  change (NamedDuties.attest_with gc S.E S.hc (S.node a.val_index) n.st n.record).2.2 = a at hrow
  change a.round = S.hc.round_of n.st.core.s at hro
  have hconf : a.confirmed = some Bsg.root := by
    rw [← hrow]
    change some (get_sg_vote_with gc S.E S.hc n.st.core.toHealing (S.hc.round_of n.st.core.s)
      (grade2_block_with gc S.E S.hc n.st.core.toHealing (S.hc.round_of n.st.core.s))).root = _
    rw [← hro]
  have hkeyB : key = Bsg.root := Option.some.inj (hkey.symm.trans hconf)
  have hinv : NamedConfirmationMembership.Invariant S.E S.cfg n.st :=
    WindowAction.windowRead_invariant S a.val_index
    (NamedRun.stateBefore S rho i a.val_index) ((S.node a.val_index).act a.round)
    (NamedRuntime.stateBefore_invariants S rho i a.val_index).1
  have hmem : Bsg ∈ n.st.core.T := by
    have hm := NamedConfirmationMembership.sg_head_mem n.cache S.E S.hc S.cfg n.st hinv
    rw [← hro] at hm
    exact hm
  rw [hinv.1.1.1] at hmem
  obtain ⟨H, hH, hHe⟩ := Finset.mem_image.mp hmem
  have hproj := NamedWindowIntrinsicEntry.emission_post_projection S rho hi hemit
  have hHpost : H ∈ (NamedRun.stateBefore S rho (i + 1) a.val_index).st.bodies := by
    rw [hproj.1]
    exact hH
  have hHrun := NamedRuntime.blockInRun_of_direct S rho
    (NamedRuntime.directBlock_of_prefix S rho ha (i + 1) hHpost)
  have hroot : H.root = K.root := by
    rw [hKroot, hkeyB, ← hHe, NamedWire.erase_root]
  have heq : H = K := hexec.core.root_injective H K hHrun hK H K
    (Or.inl (NamedAncestry.named_self H)) (Or.inr (NamedAncestry.named_self K)) hroot
  rw [← heq, hHe]
  exact hfloor

#print axioms straggler_sg_floor_at_event
#print axioms straggler_confirmed_head_floor

/-- Additional ready straggler tokens preserve support and introduce no
opposition. The local view supplies their actual emission origins and resolved
bodies; the head-coverage condition is derived, not assumed. Receipt times
need no bound beyond the execution model. -/
theorem straggler_arrival_preserves
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time) (s r : Round) (P : NamedBlock V)
    (hexec : OutageExecution S rho b0 b1) (hmargin : FormationMargin S s b0)
    (hsleep : OutageSleepyThroughout S rho) (hP : NamedRun.blockInRun S rho P)
    (hno : NoHonestConflictAbove S rho b0 P.erase)
    (hmin : ∀ q : Round, 0 < q → b0 ≤ S.a q → r ≤ q)
    (hfirst : S.a (r - 1) < b0) (hframes : PreBoundaryFrames S rho b0 s P.erase)
    (hheld0 : ∀ v ∈ rho.honest, P ∈ (NamedRun.stateBeforeTime S rho b0 v).st.bodies)
    (gv : GradeView V)
    {early late raw early' late' raw' : Finset (Token (Option BlockId))}
    (he : early ⊆ early') (hel : early' ⊆ late') (her : early' ⊆ raw')
    (hnew : ∀ x ∈ late', x ∉ late →
      ∃ (a : NamedAttestation V) (t : Time) (key : BlockId) (K : NamedBlock V),
        a.val_index ∈ rho.honest ∧ NamedRun.emits S rho a.val_index (.attest a) t ∧
        b0 ≤ t ∧ a.round < r ∧ a.confirmed = some key ∧ x.key = some key ∧
        NamedRun.blockInRun S rho K ∧ K.root = key ∧ Block.find? gv.T key = some K.erase)
    (hclean : CleanFrom raw' 0) :
    (Supports (fun k B => localCovers gv k B = true) early late raw P.erase →
      Supports (fun k B => localCovers gv k B = true) early' late' raw' P.erase) ∧
    (Opposes (fun k B => localCovers gv k B = true) early' late' raw' P.erase →
      Opposes (fun k B => localCovers gv k B = true) early late raw P.erase) := by
  have hcovers : ∀ x ∈ late', x ∉ late → localCovers gv x.key P.erase = true := by
    intro x hx hn
    obtain ⟨a, t, key, K, ha, hem, hb, har, hconf, hkey, hK, hKroot, hfind⟩ := hnew x hx hn
    have hfloor := straggler_confirmed_head_floor S rho b0 b1 s r P hexec hmargin hsleep
      hP hno hmin hfirst hframes hheld0 ha hem hb har key hconf K hK hKroot
    simpa only [localCovers, head_covers, hkey, hfind, Block.Preceq] using hfloor
  exact ⟨HonestArrival.supports_of_covering_arrivals _ he hel her hcovers hclean,
    HonestArrival.opposes_before_of_covering_arrivals _ he hcovers hclean⟩

#print axioms straggler_arrival_preserves

end DecoupledConsensusModel.Proofs.NamedWindowSGFloor
