module
public import DecoupledConsensusProofs.Protocol.ChainState.W4FKChainJustificationWrite
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ChainState.CarrierFinalityFirstHalf
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

/-! ## 5. The carrier's own justification -/

omit [Fintype V] in
private theorem w4fkParentPreceq (B : NamedBlock V) : NamedBlock.Preceq B.parent B := by
  cases B with
  | genesis => exact Proofs.NamedAncestry.named_self _
  | node parent slot root votes support rows proposer =>
      simp only [NamedBlock.Preceq, NamedBlock.preceq, NamedBlock.parent,
        Bool.or_eq_true]
      exact Or.inr (Proofs.NamedAncestry.named_self parent)

private theorem w4fkRunBlock_unique
    {S : Setup V} {rho : Run V} (adm : Admissible S rho)
    {A D : NamedBlock V} (hA : RunBlock S rho A) (hD : RunBlock S rho D)
    (herase : A.erase = D.erase) : A = D :=
  adm.toNamedAdmissibleCore.toNamedRootCollisionFree.root_injective A D hA hD A D
    (Or.inl (Proofs.NamedAncestry.named_self A)) (Or.inr (Proofs.NamedAncestry.named_self D))
    (by rw [← Proofs.NamedWire.erase_root A, ← Proofs.NamedWire.erase_root D, herase])

/-- The named parent of the slot-`s+1` proposal is the slot-`s` proposal.
earlier reads this off `parent_eq_of_parent?` because its blocks are erased; here
the two blocks are named, `proposedParent` only pins the erasures, and the
identification is run-wide root collision freedom. Both proposers must be
honest inside the horizon, which is exactly what `ProposerCarrierAt` gives at a
carrier round. -/
theorem namedProposalParent_eq_of_honest
    (S : Setup V) {rho : Run V} (adm : Admissible S rho) {s : Slot}
    (hs : 0 < s)
    (hprev : S.E.proposer s ∈ rho.honest)
    (hnext : S.E.proposer (s + 1) ∈ rho.honest)
    (hhor : Protocol.proposal_time S.E (s + 1) ≤ rho.horizon)
    {P Q : NamedBlock V}
    (hP : proposedBlockAt S rho s = some P)
    (hQ : proposedBlockAt S rho (s + 1) = some Q)
    (hparent : proposedParent S rho (s + 1) = P.erase) :
    Q.parent = P := by
  have hhorP : Protocol.proposal_time S.E s ≤ rho.horizon :=
    (proposal_time_mono S.E (Nat.le_succ s)).trans hhor
  have hrunP := proposedBlockAt_blockInRun_of_admissible S adm.toNamedAdmissibleCore
    s hs hprev hhorP hP
  have hrunQ := proposedBlockAt_blockInRun_of_admissible S adm.toNamedAdmissibleCore
    (s + 1) (Nat.zero_lt_succ s) hnext hhor hQ
  obtain ⟨p, hp, hpe⟩ := proposedBlockAt_parent S rho (s + 1) hQ
  have hQp : Q.parent = p := by
    cases Q with
    | genesis => cases hp
    | node parent slot root votes support rows proposer =>
        simpa only [NamedBlock.parent] using Option.some.inj hp
  have hrunp : RunBlock S rho p :=
    Proofs.NamedRuntime.blockInRun_of_ancestor S rho hrunQ (hQp ▸ w4fkParentPreceq Q)
  have hpP : p = P := w4fkRunBlock_unique adm hrunp hrunP (by rw [hpe, hparent])
  rw [hQp, hpP]

/-- An opening-aligned first half justifies the opening height on its common
carrier chain. The live branch keeps the parent target-participation test;
the other branch supplies an already-justified ancestor
(PROTOCOL.md `process_height_events`). -/
theorem namedCarrierJustificationHeight_of_firstHalf
    (S : Setup V) {rho : Run V} (hbot : BelowOneThird S rho.honest)
    {r : Round} {C : Block V} {P0 B : NamedBlock V} {s : Slot}
    (hP0 : proposedBlockAt S rho (S.hc.opening_slot r) = some P0)
    (hhalf : CarrierFinalityFirstHalfAtProposal S rho r C s B)
    (hnj : (derive_named S.E S.cfg P0).nj = false) :
    ∃ X : NamedBlock V, NamedBlock.Preceq X B ∧
      (derive_named S.E S.cfg X).h_j = (derive_named S.E S.cfg P0).h := by
  rcases hhalf.checkpointReady P0 hP0 with hearly | ⟨hheight, htarget⟩
  · exact hearly
  · have hnjParent : (derive_named S.E S.cfg B.parent).nj = false :=
      (namedNj_eq_of_preceq_same_height S.E S.cfg
        (hhalf.openingBelowParent P0 hP0) hheight).trans hnj
    have hwrite := namedOrdinaryHeightTargetProposal_of_actionCoverage S hbot
      hhalf.carrierProposal (hhalf.actionCoverage P0 hP0 hheight)
      hheight (congrArg Block.root htarget) hnjParent (hhalf.targetRows P0 hP0)
    exact ⟨B, Proofs.NamedAncestry.named_self B, hwrite.1.2⟩

#print axioms namedTargetQuorumCoveredByChild_of_honest
#print axioms namedTargetQuorum_after_fold
#print axioms namedTargetReady_of_covered
#print axioms namedJustifiedAt_of_targetQuorumCoveredByChild
#print axioms namedTargetQuorumCoveredByChild_of_actionCoverage
#print axioms namedOrdinaryHeightTargetProposal_of_actionCoverage
#print axioms namedNj_eq_of_preceq_same_height
#print axioms namedProposalParent_eq_of_honest
#print axioms namedCarrierJustificationHeight_of_firstHalf

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
