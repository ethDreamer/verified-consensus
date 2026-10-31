module
public import DecoupledConsensusInternal.ModelVocabulary.Execution.WindowActionReads
public import DecoupledConsensusStatements.Instantiation.Proposals

/-!
# Honest carrier coverage

This internal interface records carriage of the actual combined attestation
by an honest proposal while its round is admissible. It separates the chain
reader's requirement from the SG pool's delivery deadline. It does not assert
that the proposal is the round's +2 proposal, that different rows use the same
proposal, or that chain membership remains in a live accumulator.
See the proposal selection rule (PROTOCOL.md `proposal_attestations`).
-/
@[expose] public section

namespace DecoupledConsensusModel.Proofs.HealingSurface

open Execution
open Statements.Instantiation

variable {V : Type} [DecidableEq V] [Fintype V]

/-- Every honest actual round row has an honest, eligible proposal witness
within the run horizon (PROTOCOL.md `proposal_attestations`). -/
def CarrierCoverage (S : Setup V) (rho : Run V) (q : Round) : Prop :=
  ∀ v ∈ rho.honest, ∃ (s : Slot) (B : NamedBlock V),
    S.E.proposer s ∈ rho.honest ∧
    Protocol.ProposalRows.inWindow S.hc (proposerReadAt S rho s).st.core q = true ∧
    Protocol.proposal_time S.E s ≤ rho.horizon ∧
    proposedBlockAt S rho s = some B ∧
    (NamedActionReads.windowActionAttestationAt S rho v q ∈
        Protocol.NamedProposalRows.chainRows B.parent ∨
      NamedActionReads.windowActionAttestationAt S rho v q ∈ B.attestations)

end DecoupledConsensusModel.Proofs.HealingSurface

end
