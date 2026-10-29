module
public import DecoupledConsensusInternal.Definitions.NamedJointOutage
public import DecoupledConsensusInternal.ModelVocabulary.Execution.WindowActionReads

/-!
# Causal entry and carrier histories

These histories use strict event prefixes and the actual attestation input,
including earlier duties in the same tick (PROTOCOL.md `sec:public-handlers`).
The round-indexed histories in `NamedJointOutage` describe the paper schedule;
their recovery is a separate proof obligation at that instance.
-/
@[expose] public section
namespace DecoupledConsensusModel.Internal.NamedJointOutage
open Execution Protocol
variable {V : Type} [DecidableEq V] [Fintype V]

/-- Length of the strict time prefix used by an event-index history. -/
def strictEventCut (rho : NamedRun V) (t : Time) : Nat :=
  (rho.events.filter (fun e => decide (e.time < t))).length

/-- Exact source and entry at the emitter's actual attestation duty. -/
def WindowSignedSourceAt (S : Setup V) (rho : NamedRun V) (i : Nat)
    (a : NamedAttestation V) (source entry : NamedBlock V) : Prop :=
  rho.events[i]? = some (.tick a.val_index ((S.node a.val_index).act a.round)) ∧
  let n := NamedActionReads.windowActionReadFrom S a.val_index
    (NamedRun.stateBefore S rho i a.val_index) a.round
  let gc := NamedProfile.gradeContract n.cache
  NamedObject.attest a ∈ NamedRun.emittedAt S rho i a.val_index
    ((S.node a.val_index).act a.round) ∧
  (NamedDuties.attest_with gc S.E S.hc (S.node a.val_index) n.st n.record).2.2 = a ∧
  source ∈ n.st.bodies ∧
  fg_source_with gc S.E S.hc n.st.core.toHealing a.round
    (grade2_block_with gc S.E S.hc n.st.core.toHealing a.round) = some source.erase ∧
  NamedBlock.Preceq entry source ∧
  entry.erase = (derive_named S.E S.cfg source).T_h ∧
  (derive_named S.E S.cfg entry).h = (derive_named S.E S.cfg source).h ∧
  ∃ timeout : Bool, a.height_pair = .vote
    (derive_named S.E S.cfg source).h entry.root timeout

/-- Honest entries emitted strictly before the event prefix `n`. -/
def IntrinsicHighEntryHistoryIdx (S : Setup V) (rho : NamedRun V)
    (P : NamedBlock V) (n : Nat) : Prop :=
  ∀ i, i < n → ∀ a source entry, a.val_index ∈ rho.honest →
    WindowSignedSourceAt S rho i a source entry → NamedBlock.compatible P entry = true

/-- Every honest ancestral row has an emission strictly before `n`.
The carrier's own round guard is independent of this causal bound. -/
def CausalCarrierRowsBefore (S : Setup V) (rho : NamedRun V)
    (n : Nat) (B : NamedBlock V) : Prop :=
  ∀ A, NamedBlock.Preceq A B → ∀ a ∈ A.attestations, a.val_index ∈ rho.honest →
    ∃ i, i < n ∧
      rho.events[i]? = some (.tick a.val_index ((S.node a.val_index).act a.round)) ∧
      NamedObject.attest a ∈ NamedRun.emittedAt S rho i a.val_index
        ((S.node a.val_index).act a.round)

/-- Run-scoped conflicting carriers whose honest rows precede `n` stay
within one height of the protected prefix. -/
def IntrinsicConflictingCarrierBandIdx (S : Setup V) (rho : NamedRun V)
    (P : NamedBlock V) (n : Nat) : Prop :=
  ∀ B, NamedRun.blockInRun S rho B → CausalCarrierRowsBefore S rho n B →
    NamedBlock.compatible P B = false →
      (derive_named S.E S.cfg B).h ≤ (derive_named S.E S.cfg P).h + 1

end DecoupledConsensusModel.Internal.NamedJointOutage
