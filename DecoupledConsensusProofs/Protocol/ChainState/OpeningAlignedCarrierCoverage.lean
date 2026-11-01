module
public import DecoupledConsensusProofs.Protocol.ChainState.CarrierCoverage
public import DecoupledConsensusInternal.Legacy.Definitions.ActionSources

/-!
# Opening-aligned carrier rows

The FG reader requires both timely chain carriage and rows naming the entry
selected at the opening's confirmation. This internal interface records those
two facts without adding them to an execution regime. The source identifies
the emission anchor; the height-pair equation transports the paper reader's
proper-target or timeout classification to the actual row
(PROTOCOL.md `sec:healing-schedule`, `proposal_attestations`).
-/
@[expose] public section

namespace DecoupledConsensusModel.Proofs.HealingSurface
open Execution Statements.Instantiation

variable {V : Type} [DecidableEq V] [Fintype V]

/-- One common carrier covers actual rows whose FG sources and height pairs
agree with the first opening's entry. Live accumulator membership remains a
consumer obligation (PROTOCOL.md `sec:healing-schedule`). -/
structure OpeningAlignedCarrierCoverage (S : Setup V) (rho : Run V) (q : Round) : Prop where
  coverage : CarrierCoverage S rho q
  openingSource : ∀ v ∈ rho.honest, ∀ P : NamedBlock V,
    proposedBlockAt S rho (S.hc.opening_slot q) = some P →
    actionFGSource S (NamedActionReads.windowActionReadAt S rho v q) = some P.erase
  heightPair : ∀ v ∈ rho.honest,
    (NamedActionReads.windowActionAttestationAt S rho v q).height_pair =
      (actionAttestationAt S rho v q).height_pair

end DecoupledConsensusModel.Proofs.HealingSurface

end
