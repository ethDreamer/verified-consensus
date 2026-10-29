module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Handlers.NonInterference
public import DecoupledConsensusProofs.Protocol.Grades.SupportCarry
public import DecoupledConsensusProofs.Protocol.Duties.Inputs.IntrinsicEntry
public import DecoupledConsensusProofs.Protocol.ChainState.MatchingProgress
public import DecoupledConsensusProofs.Protocol.ChainState.EntryHeight
public import DecoupledConsensusProofs.Execution.ConflictingCarrierBand
public import DecoupledConsensusProofs.Protocol.Handlers.CheckpointRows
public import DecoupledConsensusProofs.Execution.OutageInputs
public import DecoupledConsensusProofs.Protocol.ChainState.JustificationCertificates
public import DecoupledConsensusProofs.Protocol.Grades.ProposalParent
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.ActionSourceCore
public import DecoupledConsensusProofs.Protocol.Grades.VoteBelowSource
public import DecoupledConsensusInternal.Definitions.NamedJointOutage

@[expose] public section

/-!
# Round invariant assembly from completed opening certificates

The causal history before the next G0 completion suffices for reads within the
current round. To read the next paper checkpoint, first extend that history
using the next round's completed opening SG certificate. This includes honest
actions before that paper instant (PROTOCOL.md `sec:healing-schedule`).
-/

namespace DecoupledConsensusModel.Proofs.NamedOutageClosure
open Execution Internal.NamedOutageEntry Internal.NamedStableChainOutage
open Internal.NamedJointOutage Protocol DecoupledConsensusModel.Protocol
variable {V : Type} [DecidableEq V] [Fintype V]


/-! ## Named-ancestry helpers (private elsewhere, copied verbatim in spirit). -/

omit [Fintype V] in
private theorem step_named_self (B : NamedBlock V) : NamedBlock.Preceq B B := by
  cases B <;> simp [NamedBlock.Preceq, NamedBlock.preceq]

omit [Fintype V] in
private theorem step_named_extend {A parent : NamedBlock V} (s : Slot) (root : BlockId)
    (votes support : List (GoldfishVote V)) (rows : List (NamedAttestation V)) (proposer : V)
    (h : NamedBlock.Preceq A parent) :
    NamedBlock.Preceq A (.node parent s root votes support rows proposer) := by
  simp only [NamedBlock.Preceq, NamedBlock.preceq, Bool.or_eq_true]
  exact Or.inr h

omit [Fintype V] in
/-- Existence inside the full recursive chain; no injectivity of `erase`. -/
private theorem step_erased_ancestor_lift (B : NamedBlock V) {raw : Block V}
    (h : Block.Preceq raw B.erase) :
    ∃ A : NamedBlock V, NamedBlock.Preceq A B ∧ A.erase = raw := by
  induction B with
  | genesis =>
    have hr : raw = Block.genesis := by
      simpa only [Block.Preceq, Block.preceq, NamedBlock.erase, decide_eq_true_eq] using h
    subst raw
    exact ⟨.genesis, step_named_self _, rfl⟩
  | node parent s root votes support rows proposer ih =>
    let B := NamedBlock.node parent s root votes support rows proposer
    have hcases : raw = B.erase ∨ Block.Preceq raw parent.erase := by
      simpa only [B, NamedBlock.erase, Block.Preceq, Block.preceq,
        Bool.or_eq_true, decide_eq_true_eq] using h
    rcases hcases with heq | hp
    · exact ⟨B, step_named_self B, heq.symm⟩
    · obtain ⟨A, hA, hErase⟩ := ih hp
      exact ⟨A, step_named_extend s root votes support rows proposer hA, hErase⟩

omit [Fintype V] in
/-- Two named ancestors of one named block are comparable. Structural, so it
needs neither root injectivity nor a run scope. -/
private theorem step_named_common (B : NamedBlock V) :
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
    exact Or.inl (step_named_self _)
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
        exact Or.inl (step_named_self _)
      · simp only [NamedBlock.compatible, Bool.or_eq_true]
        exact Or.inr (step_named_extend s root votes support rows proposer hCp)
    · rcases hC' with rfl | hCp
      · simp only [NamedBlock.compatible, Bool.or_eq_true]
        exact Or.inl (step_named_extend s root votes support rows proposer hAp)
      · exact ih A C hAp hCp

/-! ## Selector projections. -/

omit [Fintype V] in
/-- `deepest_clear` respects its floor: it ranges over blocks above it. -/
private theorem step_deepest_clear_floor {floor C B : Block V} {test : Block V → Bool}
    (h : Protocol.deepest_clear (some floor) C test = some B) : Block.Preceq floor B := by
  unfold Protocol.deepest_clear at h
  exact (Finset.mem_filter.mp (Proofs.Engine.deepest?_mem h)).2.1

omit [Fintype V] in
/-- Every filtered-tree member sits above the FG root. -/
private theorem step_filtered_root_preceq {st : Protocol.FGStore V} {B : Block V}
    (h : B ∈ Protocol.get_filtered_block_tree st) :
    Block.Preceq (Protocol.get_fg_root st) B := by
  simp only [Protocol.get_filtered_block_tree, Protocol.get_filtered_block_tree_from,
    Finset.mem_filter] at h
  exact h.2

/-! ## The round-`r` case of the entry step. -/

/-- The honest signer of a round-`r` height row names an entry compatible with
the protected prefix. The premises used are exactly `hexec` (sorting, node
uniqueness, root injectivity), `hinv.sg` and `hinv.prefix_scope`. -/
private theorem round_entry_compatible (S : Setup V) (rho : NamedRun V)
    (b0 b1 : Time) (r : Round) (Pn : NamedBlock V)
    (hexec : OutageExecution S rho b0 b1)
    (hinv : RoundInvariant S rho b0 Pn r)
    {i : Nat} {a : NamedAttestation V} {source entry : NamedBlock V}
    (ha : a.val_index ∈ rho.honest) (hround : a.round = r)
    (hs : SignedSourceAt S rho i a source entry) :
    NamedBlock.compatible Pn entry = true := by
  subst hround
  obtain ⟨hi, _hem, _hrow, hsrcMem, hfgsrc, hentrySrc, _, _, _timeout, _hpair⟩ := hs
  -- the action tick is a run event, so the action time is inside the horizon:
  
  have hmemEv : NamedEvent.tick a.val_index (S.a a.round) ∈ rho.events :=
    List.mem_iff_getElem?.mpr ⟨i, hi⟩
  have hhor : S.a a.round ≤ rho.horizon :=
    (hexec.core.toNamedScheduleWellFormed.in_horizon _ hmemEv).2
  -- the signer's action read is the checkpoint plus `update_confirmation_with`
  have hprefix : NamedRun.stateBefore S rho i a.val_index =
      NamedRun.stateBeforeTime S rho (S.a a.round) a.val_index :=
    Proofs.NamedRuntime.tick_prefix_eq_strict S rho hexec.core.sorted hexec.core.nodup hi
  have hck : checkpoint S rho a.val_index a.round =
      confirmationReadFrom S (NamedRun.stateBefore S rho i a.val_index) (S.a a.round) := by
    rw [hprefix]
    rfl
  set before := NamedRun.stateBefore S rho i a.val_index with hbefore
  set n := actionReadFrom S before a.round with hn
  set gc := NamedProfile.gradeContract n.cache with hgc
  
  -- opening, `6Δ` before this read; `sg_field_at_checkpoint` carries the frame
  -- arm forward inside the round.
  have hsg := sg_field_at_checkpoint S rho b0 Pn a.round hexec.core hinv hhor a.val_index ha
  rw [hck] at hsg
  -- the round the frame is read at
  have hro : S.hc.round_of (confirmationReadFrom S before (S.a a.round)).st.core.s = a.round :=
    Proofs.HealingLemmas.round_of_slotOf_a S a.round
  -- the grade-2 block exists, because the row was signed
  unfold Protocol.fg_source_with at hfgsrc
  cases hQ : Protocol.grade2_block_with gc S.E S.hc n.st.core.toHealing a.round with
  | none => simp [hQ] at hfgsrc
  | some q =>
    simp only [hQ] at hfgsrc
    -- `q ⪯ source.erase`
    have hqsrc : Block.Preceq q source.erase := by
      cases hd : Protocol.deepest_clear (some q) n.st.core.toHealing.live_confirmed
          ((gc.read S.E S.hc n.st.core.toHealing a.round).clear) with
      | none =>
        rw [hd] at hfgsrc
        rw [← Option.some.inj hfgsrc]
        exact Block.preceq_self _
      | some B =>
        rw [hd] at hfgsrc
        rw [← Option.some.inj hfgsrc]
        exact step_deepest_clear_floor hd
    -- `activeG2` at the checkpoint is `some q`
    have hbind : ((DecoupledConsensusModel.Protocol.readFrame n.cache n.st.core.toHealing
          a.round).g2.bind id).bind
        (DecoupledConsensusModel.Protocol.activePrefix
          (Protocol.get_filtered_block_tree n.st.core.toHealing.toFG)) = some q := by
      have hQ' : (if DecoupledConsensusModel.Protocol.allClosed
            (DecoupledConsensusModel.Protocol.readFrame n.cache n.st.core.toHealing a.round) then
          ((DecoupledConsensusModel.Protocol.readFrame n.cache n.st.core.toHealing a.round).g2.bind id).bind
            (DecoupledConsensusModel.Protocol.activePrefix
              (Protocol.get_filtered_block_tree n.st.core.toHealing.toFG))
        else none) = some q := hQ
      by_cases hclosed : DecoupledConsensusModel.Protocol.allClosed
          (DecoupledConsensusModel.Protocol.readFrame n.cache n.st.core.toHealing a.round) = true
      · rwa [ite_eq_left hclosed] at hQ'
      · rw [ite_eq_right hclosed] at hQ'
        exact absurd hQ' (by simp)
    have hact : activeG2 S (confirmationReadFrom S before (S.a a.round)) = some q := by
      show ((DecoupledConsensusModel.Protocol.readFrame
          (confirmationReadFrom S before (S.a a.round)).cache
          (confirmationReadFrom S before (S.a a.round)).st.core.toHealing
          (S.hc.round_of (confirmationReadFrom S before (S.a a.round)).st.core.s)).g2.bind
          id).bind
        (DecoupledConsensusModel.Protocol.activePrefix (Protocol.get_filtered_block_tree
          (confirmationReadFrom S before (S.a a.round)).st.core.toHealing.toFG)) = some q
      rw [hro]
      exact hbind
    -- `Pn.erase ⪯ q`, from either arm of the SG field
    have hPq : Block.Preceq Pn.erase q := by
      rcases hsg with hroot | ⟨_raw, G, _hframe, hG, hPG⟩
      · obtain ⟨x, _hx, hax⟩ := Option.bind_eq_some_iff.mp hbind
        have hmemtree : q ∈ Protocol.get_filtered_block_tree n.st.core.toHealing.toFG :=
          NamedProposalParent.activePrefix_mem _ x q hax
        exact Block.preceq_trans hroot (step_filtered_root_preceq hmemtree)
      · have hGq : G = q := Option.some.inj (hG.symm.trans hact)
        rw [hGq] at hPG
        exact hPG
    -- lift to named ancestry and compare with the entry
    have hPsrc : Block.Preceq Pn.erase source.erase := Block.preceq_trans hPq hqsrc
    obtain ⟨A, hAsrc, hAe⟩ := step_erased_ancestor_lift source hPsrc
    have hPre : source ∈ (NamedRun.stateBefore S rho i a.val_index).st.bodies := hsrcMem
    have hsrcScope : NamedRun.blockInRun S rho source :=
      Proofs.NamedRuntime.blockInRun_of_direct S rho
        (Proofs.NamedRuntime.directBlock_of_prefix S rho ha i hPre)
    have hroots : A.root = Pn.root := by
      rw [← Proofs.NamedWire.erase_root A, ← Proofs.NamedWire.erase_root Pn, hAe]
    have hAP : A = Pn :=
      hexec.core.toNamedRootCollisionFree.root_injective source Pn hsrcScope hinv.prefix_scope
        A Pn (Or.inl hAsrc) (Or.inr (step_named_self Pn)) hroots
    rw [hAP] at hAsrc
    exact step_named_common source Pn entry hAsrc hentrySrc

/-- An honest entry named in round `r` is compatible with the protected block
when every honest round-`r` SG carrier covers that block. The SG carrier and
the FG source use the same prepared action read. The frame selector puts the
carrier below the source, and the named entry is an ancestor of that source. -/
theorem entry_compatible_of_carrierAbove
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time) (r : Round)
    (Pn : NamedBlock V) (hexec : OutageExecution S rho b0 b1)
    (hscope : NamedRun.blockInRun S rho Pn) (hr : 0 < r)
    (hcarriers : ∀ u ∈ honestRoundVoters S rho r,
      Block.Preceq Pn.erase (Proofs.HealingSurface.actionSGBlockAt S rho u r))
    {i : Nat} {a : NamedAttestation V} {source entry : NamedBlock V}
    (ha : a.val_index ∈ rho.honest) (hround : a.round = r)
    (hs : SignedSourceAt S rho i a source entry) :
    NamedBlock.compatible Pn entry = true := by
  subst hround
  obtain ⟨hi, hem, _hrow, hsrcMem, hfgsrc, hentrySrc, _, _, _timeout, _hpair⟩ := hs
  have hmemEv : NamedEvent.tick a.val_index (S.a a.round) ∈ rho.events :=
    List.mem_iff_getElem?.mpr ⟨i, hi⟩
  have hhor : S.a a.round ≤ rho.horizon :=
    (hexec.core.toNamedScheduleWellFormed.in_horizon _ hmemEv).2
  have hprefix : NamedRun.stateBefore S rho i a.val_index =
      NamedRun.stateBeforeTime S rho (S.a a.round) a.val_index :=
    Proofs.NamedRuntime.tick_prefix_eq_strict S rho hexec.core.sorted hexec.core.nodup hi
  set before := NamedRun.stateBefore S rho i a.val_index with hbefore
  set n := actionReadFrom S before a.round with hn
  set gc := NamedProfile.gradeContract n.cache with hgc
  have hnAction : n = Proofs.HealingSurface.actionReadAt S rho a.val_index a.round := by
    simp only [n, before, Proofs.HealingSurface.actionReadAt,
      NamedActionReads.actionReadAt, Internal.NamedOutageEntry.actionReadFrom, hprefix]
  have hvoter : a.val_index ∈ honestRoundVoters S rho a.round := by
    apply (Proofs.NamedOutageInputs.honestRoundVoters_iff S rho a.val_index a.round).2
    have ht := (WindowAction.run_emission_fields S ⟨i, hi, hem⟩).1
    exact ⟨ha, a, rfl, rfl, ht ▸ ⟨i, hi, hem⟩⟩
  have hPcarrier := hcarriers a.val_index hvoter
  have hfgsrc0 := hfgsrc
  unfold Protocol.fg_source_with at hfgsrc
  cases hQ : Protocol.grade2_block_with gc S.E S.hc n.st.core.toHealing a.round with
  | none => simp [hQ] at hfgsrc
  | some q =>
    simp only [hQ] at hfgsrc
    have hQnode : Internal.PhaseGrades.nodeQ2 S
        (Proofs.HealingSurface.actionReadAt S rho a.val_index a.round) a.round = some q := by
      rw [← hnAction]
      simpa only [Internal.PhaseGrades.nodeQ2, Internal.PhaseGrades.nodeRead,
        Protocol.grade2_block_with, gc] using hQ
    have hQA0 := Proofs.HealingSurface.actionQ2_preceq_actionAnchor S hexec.core ha hr hhor hQnode
    have hQA : Block.Preceq q
        (DecoupledConsensusModel.Protocol.frameGradeRead n.cache S.E S.hc
          n.st.core.toHealing a.round).anchor := by
      rw [hnAction]
      simpa only [Internal.PhaseGrades.nodeAnchor, Internal.PhaseGrades.nodeRead] using! hQA0
    have hcarrierSource0 := Proofs.HealingSurface.frame_sg_vote_preceq_source
      S n a.round (by simpa only [gc] using hQ) hQA
        (by simpa only [gc] using hfgsrc0)
    have hroundAt : S.hc.round_of n.st.core.toHealing.s = a.round := by
      rw [hnAction]
      exact Proofs.HealingLemmas.round_of_slotOf_a S a.round
    have hcarrierSource : Block.Preceq
        (Proofs.HealingSurface.actionSGBlockAt S rho a.val_index a.round) source.erase := by
      rw [Proofs.HealingSurface.actionSGBlockAt, ← hnAction, hroundAt]
      exact hcarrierSource0
    have hPsrc : Block.Preceq Pn.erase source.erase :=
      Block.preceq_trans hPcarrier hcarrierSource
    obtain ⟨A, hAsrc, hAe⟩ := step_erased_ancestor_lift source hPsrc
    have hsrcScope : NamedRun.blockInRun S rho source :=
      Proofs.NamedRuntime.blockInRun_of_direct S rho
        (Proofs.NamedRuntime.directBlock_of_prefix S rho ha i hsrcMem)
    have hroots : A.root = Pn.root := by
      rw [← Proofs.NamedWire.erase_root A, ← Proofs.NamedWire.erase_root Pn, hAe]
    have hAP : A = Pn :=
      hexec.core.toNamedRootCollisionFree.root_injective source Pn hsrcScope
        hscope
        A Pn (Or.inl hAsrc) (Or.inr (step_named_self Pn)) hroots
    rw [hAP] at hAsrc
    exact step_named_common source Pn entry hAsrc hentrySrc



/-- The completed invariant supplies causal entry history through all actions
of round `r`, up to the next G0 completion (PROTOCOL.md `sec:grades`). -/
theorem entry_history_step
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time) (s r : Round) (Pn : NamedBlock V)
    (hexec : OutageExecution S rho b0 b1) (hslash : Internal.NamedOutageEntry.SlashableBound S rho)
    (hmargin : FormationMargin S s b0) (hsleep : OutageSleepyThroughout S rho)
    (hno : NoHonestConflictAbove S rho b0 Pn.erase)
    (hinv : RoundInvariant S rho b0 Pn r) :
    IntrinsicHighEntryHistoryIdx S rho Pn
      (strictEventCut rho (domain S.E S.hc (r + 1) .g0)) :=
  hinv.entry_history




theorem band_step
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time) (s r : Round) (Pn : NamedBlock V)
    (hexec : OutageExecution S rho b0 b1) (hslash : Internal.NamedOutageEntry.SlashableBound S rho)
    (hmargin : FormationMargin S s b0) (hsleep : OutageSleepyThroughout S rho)
    (hno : NoHonestConflictAbove S rho b0 Pn.erase)
    (hinv : RoundInvariant S rho b0 Pn r) :
    IntrinsicConflictingCarrierBandIdx S rho Pn
      (strictEventCut rho (domain S.E S.hc (r + 1) .g0)) :=
  hinv.conflicting_band





/-- At the point instance, the causal next-G0 cut recovers the original
strict prior-round entry and carrier producers (PROTOCOL.md `sec:grades`). -/
theorem history_step_point
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time) (s r : Round) (Pn : NamedBlock V)
    (hexec : OutageExecution S rho b0 b1) (hmargin : FormationMargin S s b0)
    (hsleep : OutageSleepyThroughout S rho)
    (hinv : RoundInvariant S rho b0 Pn r)
    (hpoint : ∀ v q, (S.node v).act q = S.a q) :
    IntrinsicHighEntryHistory S rho Pn (r + 1) ∧
      IntrinsicConflictingCarrierBand S rho Pn (r + 1) := by
  have hh : IntrinsicHighEntryHistory S rho Pn (r + 1) := by
    intro h entry he
    obtain ⟨i, a, source, ha, har, hs, _⟩ := he
    have hws := (NamedWindowIntrinsicEntry.signed_source_at_point S rho hpoint
      i a source entry).2 hs
    have hi := NamedStrictEventCut.lt_strictEventCut_of_time_lt rho hexec.core.sorted
      (domain S.E S.hc (r + 1) .g0) hws.1
      (NamedStragglerEntryHistory.action_before_completion_of_round_lt S a.val_index har)
    exact hinv.entry_history i hi a source entry ha hws
  exact ⟨hh, NamedEventConflictingCarrierBand.intrinsic_conflicting_carrier_band_point
    S rho b0 b1 s (r + 1) Pn hexec hmargin hsleep hpoint hh⟩

/-- The next opening certificate closes the history before the unchanged next
paper read (PROTOCOL.md `sec:healing-schedule`). -/
theorem fg_step
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time) (s r : Round) (Pn : NamedBlock V)
    (hexec : OutageExecution S rho b0 b1) (hslash : Internal.NamedOutageEntry.SlashableBound S rho)
    (hmargin : FormationMargin S s b0) (hsleep : OutageSleepyThroughout S rho)
    (hno : NoHonestConflictAbove S rho b0 Pn.erase)
    (hheld0 : ∀ w ∈ rho.honest, Pn ∈ (NamedRun.stateBeforeTime S rho b0 w).st.bodies)
    (hinv : RoundInvariant S rho b0 Pn r) (hnext : DomainIncluded S rho b0 (r + 1))
    (hsg : ∀ v ∈ rho.honest,
      let n := NamedRun.readAt S rho (domain S.E S.hc (r + 1) .g1) v
      Block.Preceq Pn.erase n.st.core.F ∨
        ∃ raw : Block V,
          (readFrame n.cache n.st.core.toHealing (r + 1)).g2 = some (some raw) ∧
          Block.Preceq Pn.erase raw) :
    ∀ v ∈ rho.honest, JointAt S rho Pn (r + 1) v := by
  intro v hv
  have hext := NamedWindowRoundHistory.extend_round_event_history S rho b0 b1 s (r + 1)
    Pn hexec hmargin hsleep hinv.prefix_scope hno hheld0 hinv.entry_history hsg
  obtain ⟨hentry, hband⟩ := NamedWindowRoundHistory.checkpoint_event_history
    S rho b0 b1 s (r + 1) Pn hexec hmargin hsleep hext
  have hL4 := fg_noninterference_after_boundary S rho b0 b1 s (r + 1) Pn hexec hslash hmargin
    hsleep hinv.prefix_scope hno hband hentry hheld0 v hv (S.a (r + 1)) hnext.2.1
    (le_refl _)
  exact ⟨hL4.2.1, hL4.2.2⟩



theorem roundInvariant_step_of_support
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time) (s r : Round) (Pn : NamedBlock V)
    (hexec : OutageExecution S rho b0 b1) (hslash : Internal.NamedOutageEntry.SlashableBound S rho)
    (hmargin : FormationMargin S s b0) (hsleep : OutageSleepyThroughout S rho)
    (hno : NoHonestConflictAbove S rho b0 Pn.erase)
    (hheld0 : ∀ w ∈ rho.honest, Pn ∈ (NamedRun.stateBeforeTime S rho b0 w).st.bodies)
    (hinv : RoundInvariant S rho b0 Pn r) (hnext : DomainIncluded S rho b0 (r + 1))
    (hsupport : ∃ supportBoundary : Time, ∃ supportRound : Round,
      supportBoundary = min b0 (DecoupledConsensusModel.Protocol.early S.E S.hc (r + 1) DecoupledConsensusModel.Protocol.Phase.g2) ∧
      supportRound ≤ r + 1 ∧
      (∀ v ∈ rho.honest,
        S.hc.round_of (NamedRun.stateBeforeTime S rho supportBoundary v).st.core.s =
          supportRound) ∧
      S.E.electorate.weightOf
          ((Finset.univ \ rho.honest) ∪
            commonStaleRisks S rho supportBoundary Pn supportRound (r + 1)) <
        S.E.electorate.weightOf
          (commonSupporters S rho supportBoundary Pn supportRound (r + 1)))
    (hsg : ∀ v ∈ rho.honest,
      let n := NamedRun.readAt S rho (domain S.E S.hc (r + 1) .g1) v
      Block.Preceq Pn.erase n.st.core.F ∨
        ∃ raw : Block V,
          (DecoupledConsensusModel.Protocol.readFrame n.cache n.st.core.toHealing (r + 1)).g2 =
            some (some raw) ∧
          Block.Preceq Pn.erase raw) :
    RoundInvariant S rho b0 Pn (r + 1) where
  included := hnext
  prefix_scope := hinv.prefix_scope
  sg := hsg
  common_support := hsupport
  fg := fun _hhor => fg_step S rho b0 b1 s r Pn hexec hslash hmargin hsleep hno hheld0 hinv hnext hsg
  source_history := NamedCheckpointRows.window_signed_source_history S rho
    hexec.core.toNamedScheduleWellFormed _
  old_rows := fun _hhor v _hv _B hB =>
    NamedCheckpointRows.prior_carrier_rows_at_checkpoint S rho
      hexec.core.toNamedScheduleWellFormed hexec.core.toNamedUnforgeable v (r + 1) hB
  entry_history :=
    NamedWindowRoundHistory.extend_round_event_history S rho b0 b1 s (r + 1) Pn
      hexec hmargin hsleep hinv.prefix_scope hno hheld0 hinv.entry_history hsg
  conflicting_band :=
    NamedEventConflictingCarrierBand.intrinsic_conflicting_carrier_band S rho b0 b1 s _ Pn
      hexec hmargin hsleep
      (NamedWindowRoundHistory.extend_round_event_history S rho b0 b1 s (r + 1) Pn
        hexec hmargin hsleep hinv.prefix_scope hno hheld0 hinv.entry_history hsg)

/-- The support-based successor constructor recovers every original checkpoint
field at the point instance (PROTOCOL.md `sec:healing-schedule`). -/
theorem roundInvariant_step_of_support_point
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time) (s r : Round) (Pn : NamedBlock V)
    (hexec : OutageExecution S rho b0 b1) (hslash : Internal.NamedOutageEntry.SlashableBound S rho)
    (hmargin : FormationMargin S s b0) (hsleep : OutageSleepyThroughout S rho)
    (hno : NoHonestConflictAbove S rho b0 Pn.erase)
    (hheld0 : ∀ w ∈ rho.honest, Pn ∈ (NamedRun.stateBeforeTime S rho b0 w).st.bodies)
    (hinv : RoundInvariant S rho b0 Pn r) (hnext : DomainIncluded S rho b0 (r + 1))
    (hsupport : ∃ supportBoundary : Time, ∃ supportRound : Round,
      supportBoundary = min b0 (DecoupledConsensusModel.Protocol.early S.E S.hc (r + 1) DecoupledConsensusModel.Protocol.Phase.g2) ∧
      supportRound ≤ r + 1 ∧
      (∀ v ∈ rho.honest,
        S.hc.round_of (NamedRun.stateBeforeTime S rho supportBoundary v).st.core.s =
          supportRound) ∧
      S.E.electorate.weightOf
          ((Finset.univ \ rho.honest) ∪
            commonStaleRisks S rho supportBoundary Pn supportRound (r + 1)) <
        S.E.electorate.weightOf
          (commonSupporters S rho supportBoundary Pn supportRound (r + 1)))
    (hsg : ∀ v ∈ rho.honest,
      let n := NamedRun.readAt S rho (domain S.E S.hc (r + 1) .g1) v
      Block.Preceq Pn.erase n.st.core.F ∨
        ∃ raw : Block V,
          (DecoupledConsensusModel.Protocol.readFrame n.cache n.st.core.toHealing (r + 1)).g2 =
            some (some raw) ∧
          Block.Preceq Pn.erase raw)
    (hpoint : ∀ v q, (S.node v).act q = S.a q) :
    PointRoundInvariant S rho b0 Pn (r + 1) :=
  roundInvariant_point S rho b0 b1 s (r + 1) Pn hexec hmargin hsleep hpoint
    (roundInvariant_step_of_support S rho b0 b1 s r Pn hexec hslash hmargin hsleep
      hno hheld0 hinv hnext hsupport hsg)

/-! ## Post-GST support assembly -/


#print axioms history_step_point
#print axioms roundInvariant_step_of_support_point
#print axioms entry_history_step
#print axioms entry_compatible_of_carrierAbove
#print axioms band_step
#print axioms fg_step
#print axioms roundInvariant_step_of_support

end DecoupledConsensusModel.Proofs.NamedOutageClosure

end
