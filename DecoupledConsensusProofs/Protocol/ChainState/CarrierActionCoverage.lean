module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Schedule.WindowActionPoint

/-!
# Live height coverage at a proposal

Rows already on the parent chain must still contribute to its live progress
and target sets. Actual action rows instantiate this algebraic interface;
the point specialization recovers the paper observer
(PROTOCOL.md `process_attestation`, `proposal_attestations`).
-/
@[expose] public section
namespace DecoupledConsensusModel.Proofs.HealingSurface
open Execution Protocol
variable {V : Type} [DecidableEq V] [Fintype V]

/-- Live parent-or-own coverage for a specified family of signed rows. -/
def NamedHonestRowProposalCoverageAt
    (S : Setup V) (rho : Run V) (row : V → NamedAttestation V)
    (B : NamedBlock V) (H : Height) (T : BlockId) : Prop :=
  let sigma := derive_named S.E S.cfg B.parent
  ∀ v ∈ rho.honest,
    (((row v ∈
          Protocol.named_chain_attestations B.parent ∧
        v ∈ sigma.progress ∧
        ((row v).height_pair = .vote H T false →
          v ∈ sigma.target_participation)) ∨
      row v ∈ B.attestations) ∧
      ((row v).height_pair = .vote H T false ∨
        ∃ e : BlockId, (row v).height_pair = .vote H e true))

/-- Actual action rows supply the proposal's live height coverage. -/
def NamedHonestActionProposalCoverageAt
    (S : Setup V) (rho : Run V) (r : Round)
    (B : NamedBlock V) (H : Height) (T : BlockId) : Prop :=
  NamedHonestRowProposalCoverageAt S rho
    (fun v => NamedActionReads.windowActionAttestationAt S rho v r) B H T

/-- The original paper-row coverage is recovered at the point schedule. -/
theorem namedHonestActionProposalCoverageAt_point
    (S : Setup V) (rho : Run V) (r : Round)
    (B : NamedBlock V) (H : Height) (T : BlockId)
    (hpoint : ∀ v, (S.node v).act r = S.a r) :
    NamedHonestActionProposalCoverageAt S rho r B H T ↔
      NamedHonestRowProposalCoverageAt S rho
        (fun v => actionAttestationAt S rho v r) B H T := by
  have heq : (fun v => NamedActionReads.windowActionAttestationAt S rho v r) =
      (fun v => actionAttestationAt S rho v r) :=
    funext (fun v => WindowAction.windowActionAttestationAt_point S rho v r (hpoint v))
  unfold NamedHonestActionProposalCoverageAt
  rw [heq]

#print axioms namedHonestActionProposalCoverageAt_point
end DecoupledConsensusModel.Proofs.HealingSurface
end
