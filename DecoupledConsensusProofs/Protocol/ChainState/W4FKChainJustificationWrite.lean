module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ChainState.CarrierActionCoverage
public import DecoupledConsensusProofs.Protocol.ChainState.RawHeightCoverage
public import DecoupledConsensusInternal.Definitions.NamedDerived
public import DecoupledConsensusProofs.Protocol.ChainState.EntryHeight
public import DecoupledConsensusProofs.Protocol.ChainState.TargetedTimeoutBinding

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation



namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Protocol
open Protocol (ChainState HeightConfig derive_named fold_rows
  process_attestation_with TimeoutBinding)

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## 1. The targeted row fold and target participation -/

omit [Fintype V] in
/-- The targeted fold never removes a target-participation bit. -/
private theorem w4fkFold_targetParticipation_subset
    (rows : List (NamedAttestation V)) (sigma : ChainState V) :
    sigma.target_participation ⊆
      (rows.foldl (process_attestation_with (TimeoutBinding.targeted V))
        sigma).target_participation := by
  induction rows generalizing sigma with
  | nil => exact Finset.Subset.refl _
  | cons row rows ih =>
      rw [List.foldl_cons]
      refine Finset.Subset.trans ?_ (ih _)
      intro i hi
      rw [(TargetedTimeoutBinding.process_height_fields sigma row).2]
      split_ifs
      · exact Finset.mem_insert_of_mem hi
      · exact hi

omit [Fintype V] in
/-- An exact proper target row at the state's own entry enters the fold's
target participation. -/
private theorem w4fkFold_mem_targetParticipation_of_target
    {a : NamedAttestation V} :
    ∀ (rows : List (NamedAttestation V)) (sigma : ChainState V),
      a ∈ rows →
      a.height_pair = .vote sigma.h sigma.T_h.root false →
      a.val_index ∈
        (rows.foldl (process_attestation_with (TimeoutBinding.targeted V))
          sigma).target_participation := by
  intro rows
  induction rows with
  | nil => intro sigma ha _; simp at ha
  | cons row rows ih =>
      intro sigma ha hpair
      rw [List.foldl_cons]
      rcases List.mem_cons.mp ha with rfl | htail
      · apply w4fkFold_targetParticipation_subset
        rw [(TargetedTimeoutBinding.process_height_fields sigma a).2]
        simp [hpair, NamedHeightPair.matchesEntry, NamedHeightPair.properTarget]
      · apply ih _ htail
        have hfields := TimeoutBindingDefaults.process_context_fields
          (TimeoutBinding.targeted V) sigma row
        rw [hfields.2.1, hfields.2.2.1]
        exact hpair

omit [Fintype V] in
/-- The targeted fold does not move the nonjustifiability latch. -/
private theorem w4fkFold_nj
    (rows : List (NamedAttestation V)) (sigma : ChainState V) :
    (rows.foldl (process_attestation_with (TimeoutBinding.targeted V))
      sigma).nj = sigma.nj := by
  induction rows generalizing sigma with
  | nil => rfl
  | cons row rows ih =>
      rw [List.foldl_cons, ih]
      exact NjGap.process_attestation_nj sigma _

omit [Fintype V] in
private theorem w4fkRows_h (sigma : ChainState V) (geometry : Block V)
    (rows : List (NamedAttestation V)) :
    (fold_rows (TimeoutBinding.targeted V) sigma geometry rows).h = sigma.h := by
  unfold fold_rows
  exact (NamedDerivationGeometry.fold_context_fields
    (TimeoutBinding.targeted V) rows { sigma with s := geometry.slot }).2.1

omit [Fintype V] in
private theorem w4fkRows_T_h (sigma : ChainState V) (geometry : Block V)
    (rows : List (NamedAttestation V)) :
    (fold_rows (TimeoutBinding.targeted V) sigma geometry rows).T_h = sigma.T_h := by
  unfold fold_rows
  exact (NamedDerivationGeometry.fold_context_fields
    (TimeoutBinding.targeted V) rows { sigma with s := geometry.slot }).2.2.1

omit [Fintype V] in
private theorem w4fkRows_nj (sigma : ChainState V) (geometry : Block V)
    (rows : List (NamedAttestation V)) :
    (fold_rows (TimeoutBinding.targeted V) sigma geometry rows).nj = sigma.nj := by
  unfold fold_rows
  exact w4fkFold_nj rows { sigma with s := geometry.slot }

omit [Fintype V] in
private theorem w4fkRows_targetParticipation (sigma : ChainState V)
    (geometry : Block V) (rows : List (NamedAttestation V)) :
    (fold_rows (TimeoutBinding.targeted V) sigma geometry rows).target_participation =
      (rows.foldl (process_attestation_with (TimeoutBinding.targeted V))
        { sigma with s := geometry.slot }).target_participation := rfl

/-! ## 2. Named target coverage and the justification write -/

/-- Named twin of `TargetQuorumCoveredByChild`
(`FinalityQuorumCore.lean:85`): every quorum member is already live in the
parent's target participation, or the child's own named rows carry that
member's exact proper target row at the parent's entry. -/
def NamedTargetQuorumCoveredByChild
    (E : Env V) (sigma : ChainState V) (B : NamedBlock V) : Prop :=
  ∃ Q : Finset V, E.electorate.IsQuorum Q ∧
    ∀ i ∈ Q,
      i ∈ sigma.target_participation ∨
      ∃ a ∈ B.attestations,
        a.val_index = i ∧
        a.height_pair = NamedHeightPair.vote sigma.h sigma.T_h.root false

/-- Honest exact target coverage is a named target quorum under the fault
bound. -/
theorem namedTargetQuorumCoveredByChild_of_honest
    (S : Setup V) {rho : Run V} (hfb : BelowOneThird S rho.honest)
    {sigma : ChainState V} {B : NamedBlock V}
    (hcovered : ∀ i ∈ rho.honest,
      i ∈ sigma.target_participation ∨
      ∃ a ∈ B.attestations,
        a.val_index = i ∧
        a.height_pair = NamedHeightPair.vote sigma.h sigma.T_h.root false) :
    NamedTargetQuorumCoveredByChild S.E sigma B :=
  ⟨rho.honest, AlignedRoundLemmas.honestQuorum_of_belowOneThird hfb, hcovered⟩

/-- Mixed live parent/child target coverage is a quorum after the targeted row
fold. -/
theorem namedTargetQuorum_after_fold
    (E : Env V) {sigma : ChainState V} {B : NamedBlock V}
    (hcovered : NamedTargetQuorumCoveredByChild E sigma B) :
    E.electorate.IsQuorum
      (fold_rows (TimeoutBinding.targeted V) sigma B.erase
        B.attestations).target_participation := by
  obtain ⟨Q, hQ, hcov⟩ := hcovered
  apply Protocol.isQuorum_of_subset hQ
  intro i hi
  rw [w4fkRows_targetParticipation]
  rcases hcov i hi with hold | ⟨a, ha, hai, hpair⟩
  · exact w4fkFold_targetParticipation_subset _ _ hold
  · rw [← hai]
    exact w4fkFold_mem_targetParticipation_of_target _ _ ha hpair

/-- With the latch clear, named target coverage makes the folded child
target-ready. -/
theorem namedTargetReady_of_covered
    (E : Env V) {sigma : ChainState V} {B : NamedBlock V}
    (hcovered : NamedTargetQuorumCoveredByChild E sigma B)
    (hnj : sigma.nj = false) :
    Protocol.targetReady E
      (fold_rows (TimeoutBinding.targeted V) sigma B.erase B.attestations) = true := by
  have hQ := namedTargetQuorum_after_fold E hcovered
  have hquorum :
      (fold_rows (TimeoutBinding.targeted V) sigma B.erase
        B.attestations).targetQuorum E = true := by
    exact decide_eq_true hQ
  simp only [Protocol.targetReady, Bool.and_eq_true]
  refine ⟨?_, hquorum⟩
  rw [w4fkRows_nj, hnj]
  rfl

/-- Named twin of `justifiedAt_of_targetQuorumCoveredByChild` and
`derived_state_h_of_targetQuorumCoveredByChild`
(`RecurringFinalityRun.lean:620,656`): live target coverage at a justifiable
parent entry performs the actual justification write and advances the height by
one. Target justification has priority over progress consumption, so no
timeout-delay maturity premise appears. -/
theorem namedJustifiedAt_of_targetQuorumCoveredByChild
    (E : Env V) (cfg : HeightConfig) {B : NamedBlock V}
    (hBne : B ≠ NamedBlock.genesis)
    (hcovered : NamedTargetQuorumCoveredByChild E (derive_named E cfg B.parent) B)
    (hjustifiable : (derive_named E cfg B.parent).nj = false) :
    NamedJustifiedAt E cfg B
        (derive_named E cfg B.parent).T_h (derive_named E cfg B.parent).h ∧
      (derive_named E cfg B).h = (derive_named E cfg B.parent).h + 1 := by
  cases B with
  | genesis => exact (hBne rfl).elim
  | node p s root gv gsv ats proposer =>
      have htarget := namedTargetReady_of_covered E hcovered hjustifiable
      have htargetAfter :
          Protocol.targetReady E (Protocol.afterFin E
            (fold_rows (TimeoutBinding.targeted V) (derive_named E cfg p)
              (NamedBlock.node p s root gv gsv ats proposer).erase
              (NamedBlock.node p s root gv gsv ats proposer).attestations)) = true := by
        unfold Protocol.afterFin
        split
        · simpa only [Protocol.targetReady] using! htarget
        · exact htarget
      have hderive : derive_named E cfg (.node p s root gv gsv ats proposer) =
          Protocol.process_height_events E cfg
            (fold_rows (TimeoutBinding.targeted V) (derive_named E cfg p)
              (NamedBlock.node p s root gv gsv ats proposer).erase
              (NamedBlock.node p s root gv gsv ats proposer).attestations) := rfl
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · rw [hderive, Protocol.process_height_events_eq, ite_eq_left htargetAfter,
          Protocol.advance_height_J, Protocol.afterFin_T_h, w4fkRows_T_h]
        rfl
      · rw [hderive, Protocol.process_height_events_eq, ite_eq_left htargetAfter,
          Protocol.advance_height_h_j, Protocol.afterFin_h, w4fkRows_h]
        rfl
      · rw [hderive, Protocol.process_height_events_eq, ite_eq_left htargetAfter,
          Protocol.advance_height_h, Protocol.afterFin_h, w4fkRows_h]
        rfl

/-! ## 3. Exact action rows supply the named target quorum -/

/-- Named twin of `targetQuorumCoveredByProposedBlock_of_actionCoverage`
(earlier `RawHeightCoverageRun.lean:1642`): if every covered honest action row is
the exact proper target at the parent's entry, the proposal's coverage is a
live target quorum, parent-carried rows included. -/
theorem namedTargetQuorumCoveredByChild_of_actionCoverage
    (S : Setup V) {rho : Run V} (hfb : BelowOneThird S rho.honest)
    {r : Round} {H : Height} {T : BlockId} {B : NamedBlock V}
    (hcoverage : NamedHonestActionProposalCoverageAt S rho r B H T)
    (hPheight : (derive_named S.E S.cfg B.parent).h = H)
    (hPtarget : (derive_named S.E S.cfg B.parent).T_h.root = T)
    (hexact : ∀ v ∈ rho.honest,
      (NamedActionReads.windowActionAttestationAt S rho v r).height_pair = .vote H T false) :
    NamedTargetQuorumCoveredByChild S.E (derive_named S.E S.cfg B.parent) B := by
  apply namedTargetQuorumCoveredByChild_of_honest S hfb
  intro v hv
  have hpair := hexact v hv
  rcases (hcoverage v hv).1 with hparent | hchild
  · exact Or.inl (hparent.2.2 hpair)
  · exact Or.inr ⟨NamedActionReads.windowActionAttestationAt S rho v r, hchild,
      (S.node_val_index v),
      by simpa only [hPheight, hPtarget] using hpair⟩


/-- Named twin of `ordinaryHeightTargetProposal_of_actionCoverage`
(earlier `RecurringFinalityRun.lean:725`): at an ordinary height, exact target
rows in the live proposal coverage both perform the named justification write
and cross the height. This is the producer the Open at
`CanonicalRegimeSecondCheckpointRun.lean:222-232` names as missing. -/
theorem namedOrdinaryHeightTargetProposal_of_actionCoverage
    (S : Setup V) {rho : Run V} (hfb : BelowOneThird S rho.honest)
    {r : Round} {s : Slot} {H : Height} {T : BlockId} {B : NamedBlock V}
    (hB : proposedBlockAt S rho s = some B)
    (hcoverage : NamedHonestActionProposalCoverageAt S rho r B H T)
    (hPheight : (derive_named S.E S.cfg B.parent).h = H)
    (hPtarget : (derive_named S.E S.cfg B.parent).T_h.root = T)
    (hPjustifiable : (derive_named S.E S.cfg B.parent).nj = false)
    (hexact : ∀ v ∈ rho.honest,
      (NamedActionReads.windowActionAttestationAt S rho v r).height_pair = .vote H T false) :
    NamedJustifiedAt S.E S.cfg B (derive_named S.E S.cfg B.parent).T_h H ∧
      (derive_named S.E S.cfg B).h = H + 1 := by
  have hne : B ≠ NamedBlock.genesis := by
    obtain ⟨p, hp, -⟩ := proposedBlockAt_parent S rho s hB
    intro hgen
    rw [hgen] at hp
    cases hp
  have hcov := namedTargetQuorumCoveredByChild_of_actionCoverage S hfb hcoverage
    hPheight hPtarget hexact
  obtain ⟨hjust, hheight⟩ :=
    namedJustifiedAt_of_targetQuorumCoveredByChild S.E S.cfg hne hcov hPjustifiable
  exact ⟨by simpa only [hPheight] using hjust, by simpa only [hPheight] using hheight⟩

/-- Point recovery of the original paper-row target-quorum consumer
(PROTOCOL.md `process_attestation`). -/
theorem namedTargetQuorumCoveredByChild_of_actionCoverage_point
    (S : Setup V) {rho : Run V} (hfb : BelowOneThird S rho.honest)
    {r : Round} {H : Height} {T : BlockId} {B : NamedBlock V}
    (hpoint : ∀ v, (S.node v).act r = S.a r)
    (hcoverage : NamedHonestRowProposalCoverageAt S rho
      (fun v => actionAttestationAt S rho v r) B H T)
    (hPheight : (derive_named S.E S.cfg B.parent).h = H)
    (hPtarget : (derive_named S.E S.cfg B.parent).T_h.root = T)
    (hexact : ∀ v ∈ rho.honest,
      (actionAttestationAt S rho v r).height_pair = .vote H T false) :
    NamedTargetQuorumCoveredByChild S.E (derive_named S.E S.cfg B.parent) B := by
  apply namedTargetQuorumCoveredByChild_of_actionCoverage S hfb
    ((namedHonestActionProposalCoverageAt_point S rho r B H T hpoint).mpr hcoverage)
    hPheight hPtarget
  intro v hv
  rw [WindowAction.windowActionAttestationAt_point S rho v r (hpoint v)]
  exact hexact v hv

/-- Point recovery of the original paper-row justification and height write
(PROTOCOL.md `process_height_events`). -/
theorem namedOrdinaryHeightTargetProposal_of_actionCoverage_point
    (S : Setup V) {rho : Run V} (hfb : BelowOneThird S rho.honest)
    {r : Round} {s : Slot} {H : Height} {T : BlockId} {B : NamedBlock V}
    (hpoint : ∀ v, (S.node v).act r = S.a r)
    (hB : proposedBlockAt S rho s = some B)
    (hcoverage : NamedHonestRowProposalCoverageAt S rho
      (fun v => actionAttestationAt S rho v r) B H T)
    (hPheight : (derive_named S.E S.cfg B.parent).h = H)
    (hPtarget : (derive_named S.E S.cfg B.parent).T_h.root = T)
    (hPjustifiable : (derive_named S.E S.cfg B.parent).nj = false)
    (hexact : ∀ v ∈ rho.honest,
      (actionAttestationAt S rho v r).height_pair = .vote H T false) :
    NamedJustifiedAt S.E S.cfg B (derive_named S.E S.cfg B.parent).T_h H ∧
      (derive_named S.E S.cfg B).h = H + 1 := by
  apply namedOrdinaryHeightTargetProposal_of_actionCoverage S hfb hB
    ((namedHonestActionProposalCoverageAt_point S rho r B H T hpoint).mpr hcoverage)
    hPheight hPtarget hPjustifiable
  intro v hv
  rw [WindowAction.windowActionAttestationAt_point S rho v r (hpoint v)]
  exact hexact v hv

#print axioms namedTargetQuorumCoveredByChild_of_actionCoverage_point
#print axioms namedOrdinaryHeightTargetProposal_of_actionCoverage_point

/-! ## 4. The nonjustifiability latch along a named plateau -/

private theorem w4fkNamedNj_eq_node_of_same_height
    (E : Env V) (cfg : HeightConfig)
    (p : NamedBlock V) (s : Slot) (root : BlockId)
    (gv gsv : List (GoldfishVote V)) (ats : List (NamedAttestation V)) (proposer : V)
    (hh : (derive_named E cfg (.node p s root gv gsv ats proposer)).h =
      (derive_named E cfg p).h) :
    (derive_named E cfg (.node p s root gv gsv ats proposer)).nj =
      (derive_named E cfg p).nj := by
  have hderive : derive_named E cfg (.node p s root gv gsv ats proposer) =
      Protocol.process_height_events E cfg
        (fold_rows (TimeoutBinding.targeted V) (derive_named E cfg p)
          (NamedBlock.node p s root gv gsv ats proposer).erase
          (NamedBlock.node p s root gv gsv ats proposer).attestations) := rfl
  rw [hderive, Protocol.process_height_events_eq]
  split_ifs with htarget hprogress
  · exfalso
    have hh' := hh
    rw [hderive, Protocol.process_height_events_eq, ite_eq_left htarget,
      Protocol.advance_height_h, Protocol.afterFin_h, w4fkRows_h] at hh'
    exact (Nat.ne_of_lt (Nat.lt_succ_self _)) hh'.symm
  · exfalso
    have hh' := hh
    rw [hderive, Protocol.process_height_events_eq, ite_eq_right htarget, ite_eq_left hprogress,
      Protocol.advance_height_h, Protocol.afterFin_h, w4fkRows_h] at hh'
    exact (Nat.ne_of_lt (Nat.lt_succ_self _)) hh'.symm
  · rw [Protocol.afterFin_nj, w4fkRows_nj]

/-- Named twin of `derivedNj_eq_of_preceq_same_height`
(`RawHeightCoverageRun.lean:137`): on a height plateau the latch is the
ancestor's. -/
theorem namedNj_eq_of_preceq_same_height
    (E : Env V) (cfg : HeightConfig) {C P : NamedBlock V}
    (hCP : NamedBlock.Preceq C P)
    (hh : (derive_named E cfg P).h = (derive_named E cfg C).h) :
    (derive_named E cfg P).nj = (derive_named E cfg C).nj := by
  induction P with
  | genesis =>
      simp only [NamedBlock.Preceq, NamedBlock.preceq, decide_eq_true_eq] at hCP
      subst C
      rfl
  | node p s root gv gsv ats proposer ih =>
      simp only [NamedBlock.Preceq, NamedBlock.preceq, Bool.or_eq_true,
        decide_eq_true_eq] at hCP
      rcases hCP with rfl | hCp
      · rfl
      · have hmono := Proofs.NamedEntryHeight.derive_height_mono E cfg hCp
        rcases Proofs.NamedEntryHeight.derive_node_height_cases E cfg p s root gv gsv
          ats proposer with hc | hc
        · have hpHeight : (derive_named E cfg p).h = (derive_named E cfg C).h := by
            rw [← hc]; exact hh
          exact (w4fkNamedNj_eq_node_of_same_height E cfg p s root gv gsv ats proposer
            (by rw [hh, hpHeight])).trans (ih hCp hpHeight)
        · exfalso
          rw [hc] at hh
          rw [← hh] at hmono
          exact Nat.not_succ_le_self _ hmono


#print axioms namedTargetQuorumCoveredByChild_of_honest
#print axioms namedTargetQuorum_after_fold
#print axioms namedTargetReady_of_covered
#print axioms namedJustifiedAt_of_targetQuorumCoveredByChild
#print axioms namedTargetQuorumCoveredByChild_of_actionCoverage
#print axioms namedOrdinaryHeightTargetProposal_of_actionCoverage
#print axioms namedNj_eq_of_preceq_same_height

end HealingSurface
end Proofs
end DecoupledConsensusModel
end
