module
public import DecoupledConsensusProofs.Protocol.ChainState.CarrierActionCoverage
public import DecoupledConsensusProofs.Protocol.ChainState.OpeningAlignedCarrierCoverage
public import DecoupledConsensusInternal.Definitions.NamedLifecycle
public import DecoupledConsensusInternal.Definitions.NamedDerived

/-!
# First-half finality at a common carrier

The first opening's entry is unchanged. Coverage and causal finality anchors
refer to one proposal and its actual parent, including the already-justified
branch. The justification-write consumer reads this record next
(PROTOCOL.md `sec:healing-schedule`, `process_height_events`).
-/
@[expose] public section
namespace DecoupledConsensusModel.Proofs.HealingSurface
open Execution Internal Statements.Instantiation
variable {V : Type} [DecidableEq V] [Fintype V]

/-- First-carrier data at one common honest eligible proposal. The name
+2 on the row field records its point specialization; the slot is explicit
and shared by every parent and action observation
(PROTOCOL.md `sec:healing-schedule`, `proposal_attestations`). -/
structure CarrierFinalityFirstHalfAtProposal
    (S : Setup V) (rho : Run V) (r : Round) (C : Block V)
    (s : Slot) (B : NamedBlock V) : Prop where
  carrierHonest : S.E.proposer s ∈ rho.honest
  carrierWindow : Protocol.ProposalRows.inWindow S.hc
    (proposerReadAt S rho s).st.core r = true
  carrierHorizon : Protocol.proposal_time S.E s ≤ rho.horizon
  carrierDeadline : Protocol.confirmation_time S.E s ≤ S.a (r + 1)
  carrierProposal : proposedBlockAt S rho s = some B
  grade : NamedGradeFormsAt S rho r C
  gradeBelowOpening : ∀ P0 : NamedBlock V,
    proposedBlockAt S rho (S.hc.opening_slot r) = some P0 →
    Block.Preceq C P0.erase
  openingBelowParent : ∀ P0 : NamedBlock V,
    proposedBlockAt S rho (S.hc.opening_slot r) = some P0 →
    NamedBlock.Preceq P0 B.parent
  checkpointReady : ∀ P0 : NamedBlock V,
    proposedBlockAt S rho (S.hc.opening_slot r) = some P0 →
    (∃ X : NamedBlock V, NamedBlock.Preceq X B ∧
      (Protocol.derive_named S.E S.cfg X).h_j =
        (Protocol.derive_named S.E S.cfg P0).h) ∨
    ((Protocol.derive_named S.E S.cfg B.parent).h =
        (Protocol.derive_named S.E S.cfg P0).h ∧
      (Protocol.derive_named S.E S.cfg B.parent).T_h =
        (Protocol.derive_named S.E S.cfg P0).T_h)
  actionCoverage : ∀ P0 : NamedBlock V,
    proposedBlockAt S rho (S.hc.opening_slot r) = some P0 →
    (Protocol.derive_named S.E S.cfg B.parent).h =
      (Protocol.derive_named S.E S.cfg P0).h →
    NamedHonestActionProposalCoverageAt S rho r B
      (Protocol.derive_named S.E S.cfg P0).h
      (Protocol.derive_named S.E S.cfg P0).T_h.root
  rowsCarriedAtPlusTwo : ∀ v ∈ rho.honest,
    NamedActionReads.windowActionAttestationAt S rho v r ∈
      Protocol.NamedProposalRows.chainRows B.parent ∨
    NamedActionReads.windowActionAttestationAt S rho v r ∈ B.attestations
  targetRows : ∀ P0 : NamedBlock V,
    proposedBlockAt S rho (S.hc.opening_slot r) = some P0 →
    ∀ v ∈ rho.honest,
    (NamedActionReads.windowActionAttestationAt S rho v r).height_pair =
      .vote (Protocol.derive_named S.E S.cfg P0).h
        (Protocol.derive_named S.E S.cfg P0).T_h.root false
  actionHeadEq : ∀ v ∈ rho.honest, ∀ H T,
    (NamedActionReads.windowActionAttestationAt S rho v r).finality_pair = some ⟨H, T⟩ →
    ∃ (i : Nat) (D : NamedBlock V),
      rho.events[i]? = some (.tick v ((S.node v).act r)) ∧
      D ∈ (rho.stateBefore S (i + 1) v).st.bodies ∧
      NamedBlock.Preceq D B.parent ∧
      (Protocol.derive_named S.E S.cfg D).h_j = H ∧
      (Protocol.derive_named S.E S.cfg D).J.root = T

/-- A first-half carrier uses one common proposal, with confirmation by the
next paper action cut (PROTOCOL.md `sec:healing-schedule`). -/
def CarrierFinalityFirstHalfAt
    (S : Setup V) (rho : Run V) (r : Round) (C : Block V) : Prop :=
  ∃ s B, CarrierFinalityFirstHalfAtProposal S rho r C s B

end DecoupledConsensusModel.Proofs.HealingSurface
end
