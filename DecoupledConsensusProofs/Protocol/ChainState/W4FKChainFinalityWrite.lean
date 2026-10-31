module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ChainState.ProposalBridge
public import DecoupledConsensusProofs.Protocol.ChainState.AlignedRoundLemmas
public import DecoupledConsensusProofs.Protocol.ChainState.FinalityQuorumCore
public import DecoupledConsensusProofs.Protocol.Schedule.WindowActionPoint
public import DecoupledConsensusProofs.Protocol.ChainState.W4NamedJustificationMonotone
public import DecoupledConsensusProofs.Protocol.ChainState.EntryHeight
public import DecoupledConsensusProofs.Protocol.ChainState.TargetedTimeoutBinding

/-!
# Finality writes from actual rows and live parent participation

The row fold combines exact own-payload finality pairs with participation
already live at the parent's checkpoint. Finality bits persist along ancestry
with unchanged justification; entering a bit requires matching the checkpoint
at its carrier. The final write uses actual action rows, and the point instance
recovers the paper-row contract (PROTOCOL.md `alg:state-transition`).
-/
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

/-! ## 1. Finality bits through the targeted row fold -/

omit [Fintype V] in
/-- The targeted fold never removes a finality bit. -/
private theorem w4fwFold_finalize_subset
    (rows : List (NamedAttestation V)) (sigma : ChainState V) :
    sigma.finalize ⊆
      (rows.foldl (process_attestation_with (TimeoutBinding.targeted V))
        sigma).finalize := by
  induction rows generalizing sigma with
  | nil => exact Finset.Subset.refl _
  | cons row rows ih =>
      rw [List.foldl_cons]
      refine Finset.Subset.trans ?_ (ih _)
      intro i hi
      rw [TargetedTimeoutBinding.process_finality_eq sigma row,
        Protocol.process_attestation_finalize]
      split_ifs
      · exact Finset.mem_insert_of_mem hi
      · exact hi

omit [Fintype V] in
/-- An exact finality row for the state's own live checkpoint enters the fold's
finality set while the debt is positive. -/
private theorem w4fwFold_mem_finalize_of_finality
    {a : NamedAttestation V} :
    ∀ (rows : List (NamedAttestation V)) (sigma : ChainState V),
      a ∈ rows →
      sigma.h_F < sigma.h_j →
      a.finality_pair = some ⟨sigma.h_j, sigma.J.root⟩ →
      a.val_index ∈
        (rows.foldl (process_attestation_with (TimeoutBinding.targeted V))
          sigma).finalize := by
  intro rows
  induction rows with
  | nil => intro _ ha _ _; simp at ha
  | cons row rows ih =>
      intro sigma ha hlt hpair
      rw [List.foldl_cons]
      rcases List.mem_cons.mp ha with rfl | hmem
      · apply w4fwFold_finalize_subset
        rw [TargetedTimeoutBinding.process_finality_eq sigma a,
          Protocol.process_attestation_finalize]
        simp [hlt, hpair, NamedAttestation.erase]
      · apply ih _ hmem
        · have hfields := TimeoutBindingDefaults.process_context_fields
            (TimeoutBinding.targeted V) sigma row
          rw [hfields.2.2.2.2.1, hfields.2.2.2.2.2.2]
          exact hlt
        · have hfields := TimeoutBindingDefaults.process_context_fields
            (TimeoutBinding.targeted V) sigma row
          rw [hfields.2.2.2.2.1, hfields.2.2.2.1]
          exact hpair

omit [Fintype V] in
private theorem w4fwRows_h_j (sigma : ChainState V) (geometry : Block V)
    (rows : List (NamedAttestation V)) :
    (fold_rows (TimeoutBinding.targeted V) sigma geometry rows).h_j = sigma.h_j := by
  unfold fold_rows
  exact (NamedDerivationGeometry.fold_context_fields
    (TimeoutBinding.targeted V) rows { sigma with s := geometry.slot }).2.2.2.2.1

omit [Fintype V] in
private theorem w4fwRows_J (sigma : ChainState V) (geometry : Block V)
    (rows : List (NamedAttestation V)) :
    (fold_rows (TimeoutBinding.targeted V) sigma geometry rows).J = sigma.J := by
  unfold fold_rows
  exact (NamedDerivationGeometry.fold_context_fields
    (TimeoutBinding.targeted V) rows { sigma with s := geometry.slot }).2.2.2.1

omit [Fintype V] in
private theorem w4fwRows_h_F (sigma : ChainState V) (geometry : Block V)
    (rows : List (NamedAttestation V)) :
    (fold_rows (TimeoutBinding.targeted V) sigma geometry rows).h_F = sigma.h_F := by
  unfold fold_rows
  exact (NamedDerivationGeometry.fold_context_fields
    (TimeoutBinding.targeted V) rows { sigma with s := geometry.slot }).2.2.2.2.2.2

omit [Fintype V] in
private theorem w4fwRows_finalize (sigma : ChainState V) (geometry : Block V)
    (rows : List (NamedAttestation V)) :
    (fold_rows (TimeoutBinding.targeted V) sigma geometry rows).finalize =
      (rows.foldl (process_attestation_with (TimeoutBinding.targeted V))
        { sigma with s := geometry.slot }).finalize := rfl

/-! ## Live finality bits along a fixed justification -/

/-- Only a new justification can clear finality participation; a progress
advance and the finality write retain it (PROTOCOL.md `alg:state-transition`). -/
theorem finalize_subset_of_same_justification
    (E : Env V) (cfg : HeightConfig) (sigma : ChainState V)
    (hstrict : sigma.h_j < sigma.h)
    (hstable : (process_height_events E cfg sigma).h_j = sigma.h_j) :
    sigma.finalize ⊆ (process_height_events E cfg sigma).finalize := by
  unfold process_height_events at hstable ⊢
  split_ifs at hstable ⊢ <;> simp_all [advance_height]
  all_goals split_ifs at hstable ⊢ <;> simp_all

/-- Along a parent edge with unchanged justification height, all live finality
bits survive. Chain membership by itself is not used as a finality bit. -/
theorem namedFinalize_subset_of_parent_same_justification
    (E : Env V) (cfg : HeightConfig)
    (parent : NamedBlock V) (s : Slot) (root : BlockId)
    (votes support : List (GoldfishVote V)) (rows : List (NamedAttestation V))
    (proposer : V)
    (hstable : (derive_named E cfg (.node parent s root votes support rows proposer)).h_j =
      (derive_named E cfg parent).h_j) :
    (derive_named E cfg parent).finalize ⊆
      (derive_named E cfg (.node parent s root votes support rows proposer)).finalize := by
  let B := NamedBlock.node parent s root votes support rows proposer
  let folded := fold_rows (TimeoutBinding.targeted V) (derive_named E cfg parent)
    B.erase rows
  have hf := NamedDerivationGeometry.fold_context_fields
    (TimeoutBinding.targeted V) rows
    { derive_named E cfg parent with s := B.erase.slot }
  have hstrict : folded.h_j < folded.h := by
    change (fold_rows _ _ _ _).h_j < (fold_rows _ _ _ _).h
    rw [w4fwRows_h_j]
    exact hf.2.1 ▸ (NamedDerivationGeometry.chainOrder_derive_named E cfg
      parent).justified_below_height
  have hs : (process_height_events E cfg folded).h_j = folded.h_j := by
    rw [show folded.h_j = (derive_named E cfg parent).h_j from w4fwRows_h_j ..]
    exact hstable
  exact Finset.Subset.trans
    (w4fwFold_finalize_subset rows { derive_named E cfg parent with s := B.erase.slot })
    (finalize_subset_of_same_justification E cfg folded hstrict hs)

/-- Along a named chain, a live finality bit persists while the justification
height remains fixed (PROTOCOL.md `alg:state-transition`). -/
theorem namedFinalize_subset_of_preceq_same_justification
    (E : Env V) (cfg : HeightConfig) {A B : NamedBlock V}
    (hAB : NamedBlock.Preceq A B)
    (hstable : (derive_named E cfg B).h_j = (derive_named E cfg A).h_j) :
    (derive_named E cfg A).finalize ⊆ (derive_named E cfg B).finalize := by
  induction B with
  | genesis =>
      simp only [NamedBlock.Preceq, NamedBlock.preceq, decide_eq_true_eq] at hAB
      subst A
      exact Finset.Subset.refl _
  | node p s root votes support rows proposer ih =>
      simp only [NamedBlock.Preceq, NamedBlock.preceq, Bool.or_eq_true,
        decide_eq_true_eq] at hAB
      rcases hAB with rfl | hAp
      · exact Finset.Subset.refl _
      · have hparent := namedJustification_le_of_preceq E cfg hAp
        have hedge := namedJustification_strict_or_eq_of_parent E cfg p s root
          votes support rows proposer
        have hle : (derive_named E cfg p).h_j ≤
            (derive_named E cfg (.node p s root votes support rows proposer)).h_j :=
          hedge.elim Nat.le_of_lt (fun h => h.1.le)
        have hpEq : (derive_named E cfg p).h_j = (derive_named E cfg A).h_j :=
          Nat.le_antisymm (hle.trans_eq hstable) hparent
        exact Finset.Subset.trans (ih hAp hpEq)
          (namedFinalize_subset_of_parent_same_justification E cfg p s root
            votes support rows proposer (hstable.trans hpEq.symm))

/-- A carried row enters the live finality set when it matches the carrier
parent's checkpoint and that justification is retained by the child.
This is the entry condition needed before ancestry can transport its bit. -/
theorem namedFinalize_mem_of_row_same_justification
    (E : Env V) (cfg : HeightConfig) {B : NamedBlock V} {a : NamedAttestation V}
    (ha : a ∈ B.attestations)
    (hdebt : (derive_named E cfg B.parent).h_F < (derive_named E cfg B.parent).h_j)
    (hpair : a.finality_pair = some
      ⟨(derive_named E cfg B.parent).h_j, (derive_named E cfg B.parent).J.root⟩)
    (hstable : (derive_named E cfg B).h_j = (derive_named E cfg B.parent).h_j) :
    a.val_index ∈ (derive_named E cfg B).finalize := by
  cases B with
  | genesis => exact False.elim (List.not_mem_nil ha)
  | node p s root votes support rows proposer =>
      let B := NamedBlock.node p s root votes support rows proposer
      let folded := fold_rows (TimeoutBinding.targeted V) (derive_named E cfg p)
        B.erase rows
      have hf := NamedDerivationGeometry.fold_context_fields
        (TimeoutBinding.targeted V) rows
        { derive_named E cfg p with s := B.erase.slot }
      have hstrict : folded.h_j < folded.h := by
        change (fold_rows _ _ _ _).h_j < (fold_rows _ _ _ _).h
        rw [w4fwRows_h_j]
        exact hf.2.1 ▸ (NamedDerivationGeometry.chainOrder_derive_named E cfg
          p).justified_below_height
      have hs : (process_height_events E cfg folded).h_j = folded.h_j := by
        rw [show folded.h_j = (derive_named E cfg p).h_j from w4fwRows_h_j ..]
        exact hstable
      apply finalize_subset_of_same_justification E cfg folded hstrict hs
      exact w4fwFold_mem_finalize_of_finality rows
        { derive_named E cfg p with s := B.erase.slot } ha hdebt hpair

/-- A row processed at a live checkpoint remains a live finality contribution
on a descendant with the same justification. The checkpoint conditions are
explicit; membership somewhere on the chain alone does not discharge them. -/
theorem namedFinalize_mem_of_ancestor_row_same_justification
    (E : Env V) (cfg : HeightConfig) {A B : NamedBlock V} {a : NamedAttestation V}
    (hAB : NamedBlock.Preceq A B) (ha : a ∈ A.attestations)
    (hdebt : (derive_named E cfg A.parent).h_F < (derive_named E cfg A.parent).h_j)
    (hpair : a.finality_pair = some
      ⟨(derive_named E cfg A.parent).h_j, (derive_named E cfg A.parent).J.root⟩)
    (hentry : (derive_named E cfg A).h_j = (derive_named E cfg A.parent).h_j)
    (hstable : (derive_named E cfg B).h_j = (derive_named E cfg A).h_j) :
    a.val_index ∈ (derive_named E cfg B).finalize :=
  namedFinalize_subset_of_preceq_same_justification E cfg hAB hstable
    (namedFinalize_mem_of_row_same_justification E cfg ha hdebt hpair hentry)

/-! ## 2. Named finality coverage -/

/-- Named twin of `FinalityQuorumCoveredByChild` (`FinalityQuorumCore.lean:185`):
the checkpoint is named explicitly, and each quorum member is already in the
parent's finality set or carries an exact row for that same checkpoint among
the child's named rows. -/
def NamedFinalityQuorumCoveredByChild
    (E : Env V) (sigma : ChainState V) (B : NamedBlock V)
    (h_j : Height) (J : Block V) : Prop :=
  sigma.h_j = h_j ∧ sigma.J = J ∧
    ∃ Q : Finset V, E.electorate.IsQuorum Q ∧
      ∀ i ∈ Q,
        i ∈ sigma.finalize ∨
        ∃ a ∈ B.attestations,
          a.val_index = i ∧
          a.finality_pair = some ⟨h_j, J.root⟩

/-- Honest finality coverage is a named finality quorum under the fault
bound. -/
theorem namedFinalityQuorumCoveredByChild_of_honest
    (S : Setup V) {rho : Run V} (hfb : BelowOneThird S rho.honest)
    {sigma : ChainState V} {B : NamedBlock V} {h_j : Height} {J : Block V}
    (hhj : sigma.h_j = h_j) (hJ : sigma.J = J)
    (hcovered : ∀ i ∈ rho.honest,
      i ∈ sigma.finalize ∨
      ∃ a ∈ B.attestations,
        a.val_index = i ∧
        a.finality_pair = some ⟨h_j, J.root⟩) :
    NamedFinalityQuorumCoveredByChild S.E sigma B h_j J :=
  ⟨hhj, hJ, rho.honest,
    AlignedRoundLemmas.honestQuorum_of_belowOneThird hfb, hcovered⟩

/-- Positive debt and named finality coverage make the folded child
finality-ready at the preserved checkpoint. -/
theorem namedFinalityReady_of_covered
    (E : Env V) {sigma : ChainState V} {B : NamedBlock V}
    {h_j : Height} {J : Block V}
    (hcovered : NamedFinalityQuorumCoveredByChild E sigma B h_j J)
    (hlt : sigma.h_F < h_j) :
    Protocol.finalityReady E
      (fold_rows (TimeoutBinding.targeted V) sigma B.erase B.attestations) = true := by
  obtain ⟨hhj, hJ, Q, hQ, hcov⟩ := hcovered
  have hltSigma : sigma.h_F < sigma.h_j := by simpa only [hhj] using hlt
  have hquorumSet : E.electorate.IsQuorum
      (fold_rows (TimeoutBinding.targeted V) sigma B.erase B.attestations).finalize := by
    apply Protocol.isQuorum_of_subset hQ
    intro i hi
    rw [w4fwRows_finalize]
    rcases hcov i hi with hold | ⟨a, ha, hai, hpair⟩
    · exact w4fwFold_finalize_subset _ _ hold
    · rw [← hai]
      refine w4fwFold_mem_finalize_of_finality _ _ ha hltSigma ?_
      simpa only [hhj, hJ] using hpair
  have hquorum :
      (fold_rows (TimeoutBinding.targeted V) sigma B.erase
        B.attestations).finalityQuorum E = true := by
    exact decide_eq_true hquorumSet
  simp only [Protocol.finalityReady, Bool.and_eq_true]
  refine ⟨?_, hquorum⟩
  simp only [decide_eq_true_eq]
  rw [w4fwRows_h_F, w4fwRows_h_j, hhj]
  exact hlt

/-- Named twin of `finalizedAt_of_finalityQuorumCoveredByChild`
(`RecurringFinalityRun.lean:682`): live parent-or-child finality coverage
performs the actual named finality write. -/
theorem namedFinalizedAt_of_finalityQuorumCoveredByChild
    (E : Env V) (cfg : HeightConfig) {B : NamedBlock V} {J : Block V} {h : Height}
    (hBne : B ≠ NamedBlock.genesis)
    (hcovered : NamedFinalityQuorumCoveredByChild E (derive_named E cfg B.parent) B h J)
    (hdebt : (derive_named E cfg B.parent).h_F < h) :
    NamedFinalizedAt E cfg B J h := by
  cases B with
  | genesis => exact (hBne rfl).elim
  | node p s root gv gsv ats proposer =>
      have hready := namedFinalityReady_of_covered E hcovered hdebt
      have hderive : derive_named E cfg (.node p s root gv gsv ats proposer) =
          Protocol.process_height_events E cfg
            (fold_rows (TimeoutBinding.targeted V) (derive_named E cfg p)
              (NamedBlock.node p s root gv gsv ats proposer).erase
              (NamedBlock.node p s root gv gsv ats proposer).attestations) := rfl
      have hwrite := process_height_events_actual_F E cfg
        (fold_rows (TimeoutBinding.targeted V) (derive_named E cfg p)
          (NamedBlock.node p s root gv gsv ats proposer).erase
          (NamedBlock.node p s root gv gsv ats proposer).attestations) hready
      obtain ⟨hhj, hJ, -⟩ := hcovered
      refine ⟨?_, ?_⟩
      · rw [hderive, hwrite.1, w4fwRows_J]
        exact hJ
      · rw [hderive, hwrite.2, w4fwRows_h_j]
        exact hhj

/-! ## 3. Exact honest action rows perform the write -/

/-- A selected proposal performs the exact finality write once every honest
actual round row is live in its parent or carried in its own payload.
Parent-chain membership retains the live finality-bit condition
(PROTOCOL.md `process_attestation`, `process_height_events`). -/
theorem namedFinalizedAt_of_actionRows
    (S : Setup V) {rho : Run V} (hbot : BelowOneThird S rho.honest)
    {r : Round} {s : Slot} {hJ : Height} {TJ : BlockId} {J : Block V}
    {B : NamedBlock V}
    (hB : proposedBlockAt S rho s = some B)
    (hcoverage : ∀ v ∈ rho.honest,
      let a := NamedActionReads.windowActionAttestationAt S rho v r
      (a ∈ Protocol.named_chain_attestations B.parent ∧
          v ∈ (derive_named S.E S.cfg B.parent).finalize) ∨
        a ∈ B.attestations)
    (hparentHJ : (derive_named S.E S.cfg B.parent).h_j = hJ)
    (hparentJ : (derive_named S.E S.cfg B.parent).J = J)
    (hroot : J.root = TJ)
    (hdebt : (derive_named S.E S.cfg B.parent).h_F < hJ)
    (hfinality : ∀ v ∈ rho.honest,
      (NamedActionReads.windowActionAttestationAt S rho v r).finality_pair = some ⟨hJ, TJ⟩) :
    NamedFinalizedAt S.E S.cfg B J hJ := by
  have hne : B ≠ NamedBlock.genesis := by
    obtain ⟨p, hp, -⟩ := proposedBlockAt_parent S rho s hB
    intro hgen
    rw [hgen] at hp
    cases hp
  refine namedFinalizedAt_of_finalityQuorumCoveredByChild S.E S.cfg hne ?_ hdebt
  refine namedFinalityQuorumCoveredByChild_of_honest S hbot hparentHJ hparentJ ?_
  intro v hv
  have hcovered := hcoverage v hv
  dsimp only at hcovered
  rcases hcovered with hparent | hchild
  · exact Or.inl hparent.2
  · refine Or.inr ⟨NamedActionReads.windowActionAttestationAt S rho v r, hchild,
      S.node_val_index v, ?_⟩
    rw [hfinality v hv, hroot]

/-- The point instance recovers the original paper-row finality-write contract
without changing its checkpoint, debt or live-accumulator premises. -/
theorem namedFinalizedAt_of_actionRows_point
    (S : Setup V) {rho : Run V}
    (hpoint : ∀ v r, (S.node v).act r = S.a r)
    (hbot : BelowOneThird S rho.honest)
    {r : Round} {s : Slot} {hJ : Height} {TJ : BlockId} {J : Block V}
    {B : NamedBlock V}
    (hB : proposedBlockAt S rho s = some B)
    (hcoverage : ∀ v ∈ rho.honest,
      let a := actionAttestationAt S rho v r
      (a ∈ Protocol.named_chain_attestations B.parent ∧
          v ∈ (derive_named S.E S.cfg B.parent).finalize) ∨ a ∈ B.attestations)
    (hparentHJ : (derive_named S.E S.cfg B.parent).h_j = hJ)
    (hparentJ : (derive_named S.E S.cfg B.parent).J = J)
    (hroot : J.root = TJ)
    (hdebt : (derive_named S.E S.cfg B.parent).h_F < hJ)
    (hfinality : ∀ v ∈ rho.honest,
      (actionAttestationAt S rho v r).finality_pair = some ⟨hJ, TJ⟩) :
    NamedFinalizedAt S.E S.cfg B J hJ := by
  refine namedFinalizedAt_of_actionRows S hbot (r := r) hB ?_
    hparentHJ hparentJ hroot hdebt ?_
  · intro v hv
    simpa only [WindowAction.windowActionAttestationAt_point S rho v r (hpoint v r)]
      using hcoverage v hv
  · intro v hv
    simpa only [WindowAction.windowActionAttestationAt_point S rho v r (hpoint v r)]
      using hfinality v hv

#print axioms namedFinalityQuorumCoveredByChild_of_honest
#print axioms finalize_subset_of_same_justification
#print axioms namedFinalize_subset_of_parent_same_justification
#print axioms namedFinalize_subset_of_preceq_same_justification
#print axioms namedFinalize_mem_of_row_same_justification
#print axioms namedFinalize_mem_of_ancestor_row_same_justification
#print axioms namedFinalityReady_of_covered
#print axioms namedFinalizedAt_of_finalityQuorumCoveredByChild
#print axioms namedFinalizedAt_of_actionRows
#print axioms namedFinalizedAt_of_actionRows_point

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
