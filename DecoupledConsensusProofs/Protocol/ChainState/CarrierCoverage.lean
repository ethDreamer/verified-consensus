module
public import DecoupledConsensusInternal.ModelVocabulary.Execution.WindowActionReads
public import DecoupledConsensusStatements.Instantiation.Proposals

/-!
# Honest carrier coverage

This internal interface records carriage of the actual combined attestation
by an honest proposal while its round is admissible. It separates the chain
reader's requirement from the SG pool's delivery deadline. All rows use one
proposal whose confirmation is no later than the next paper action cut.
The slot is not fixed to +2, and chain membership does not assert membership
in a live accumulator.
See the proposal selection rule (PROTOCOL.md `proposal_attestations`).
-/
@[expose] public section

namespace DecoupledConsensusModel.Proofs.HealingSurface

open Execution
open Statements.Instantiation

variable {V : Type} [DecidableEq V] [Fintype V]

/-- One honest, eligible proposal covers all actual round rows, within the
run horizon and with confirmation by the next paper action cut
(PROTOCOL.md `proposal_attestations`, `sec:healing-schedule`). -/
def CarrierCoverage (S : Setup V) (rho : Run V) (q : Round) : Prop :=
  ∃ (s : Slot) (B : NamedBlock V),
    S.E.proposer s ∈ rho.honest ∧
    Protocol.ProposalRows.inWindow S.hc (proposerReadAt S rho s).st.core q = true ∧
    Protocol.proposal_time S.E s ≤ rho.horizon ∧
    Protocol.confirmation_time S.E s ≤ S.a (q + 1) ∧
    proposedBlockAt S rho s = some B ∧
    ∀ v ∈ rho.honest,
    (NamedActionReads.windowActionAttestationAt S rho v q ∈
        Protocol.NamedProposalRows.chainRows B.parent ∨
      NamedActionReads.windowActionAttestationAt S rho v q ∈ B.attestations)

/-- Common coverage implies the per-row existential carriage contract. -/
theorem CarrierCoverage.row {S : Setup V} {rho : Run V} {q : Round}
    (h : CarrierCoverage S rho q) {v : V} (hv : v ∈ rho.honest) :
    ∃ (s : Slot) (B : NamedBlock V),
      S.E.proposer s ∈ rho.honest ∧
      Protocol.ProposalRows.inWindow S.hc (proposerReadAt S rho s).st.core q = true ∧
      Protocol.proposal_time S.E s ≤ rho.horizon ∧
      proposedBlockAt S rho s = some B ∧
      (NamedActionReads.windowActionAttestationAt S rho v q ∈
          Protocol.NamedProposalRows.chainRows B.parent ∨
        NamedActionReads.windowActionAttestationAt S rho v q ∈ B.attestations) := by
  obtain ⟨s, B, hhonest, hwindow, hhor, _, hB, hrows⟩ := h
  exact ⟨s, B, hhonest, hwindow, hhor, hB, hrows v hv⟩

end DecoupledConsensusModel.Proofs.HealingSurface

end
