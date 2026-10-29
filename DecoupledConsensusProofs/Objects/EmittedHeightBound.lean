module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ValidatorClient.WeakHeightBounds
public import DecoupledConsensusProofs.Protocol.Handlers.StoreBridge
public import DecoupledConsensusProofs.Execution.EmissionShape
public import DecoupledConsensusProofs.Execution.Runtime
public import DecoupledConsensusProofs.Protocol.Handlers.HMaxCore

@[expose] public section

/-! # Height bounds at strict emission reads

The selected height source is already held before the emitting tick, including
when a proposal shares that tick. The core bound supplies the strict-time
conclusion; retention extends it to later event and time frontiers.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Protocol (derive_named)

variable {V : Type} [DecidableEq V] [Fintype V]

/-- A row sent by an actual tick is no higher than its emitter's strict
pre-action frontier (PROTOCOL.md `sec:public-handlers`). -/
theorem honestEmittedHeight_le_localHMaxBeforeTime
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v : V} {a : NamedAttestation V} {t : Time} {h : Height}
    (hemit : rho.emits S v (Object.attest a) t)
    (hh : a.height_pair.erase.height? = some h) :
    h ≤ (rho.storeBeforeTime S v t).h_max := by
  exact WeakFG.honestEmittedHeight_le_localHMaxBeforeTime
    S adm.toNamedAdmissibleCore hemit hh

/-- Preserve the inclusive emission-time bound. -/
theorem honestEmittedHeight_le_localHMax
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v : V} {a : NamedAttestation V} {t : Time} {h : Height}
    (hemit : rho.emits S v (Object.attest a) t)
    (hh : a.height_pair.erase.height? = some h) :
    h ≤ (rho.storeAt S v t).h_max :=
  (honestEmittedHeight_le_localHMaxBeforeTime S adm hemit hh).trans
    (storeBeforeTime_hMax_le_storeAt S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed v t)

/-- Every honest row sent by a time is below the honest strict-time frontier
there. This also covers rows sent exactly at that time. -/
theorem honestEmittedHeight_le_honestHMaxBeforeTime
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v : V} (hv : v ∈ rho.honest) {a : NamedAttestation V}
    {u t : Time} {h : Height}
    (hemit : rho.emits S v (Object.attest a) u)
    (hh : a.height_pair.erase.height? = some h) (hut : u ≤ t) :
    h ≤ honestHMaxBeforeIndex S rho (strictEventIndex rho t) := by
  have sch : ScheduleWellFormed S rho := adm.toNamedAdmissibleCore.toNamedScheduleWellFormed
  have hlocal := (honestEmittedHeight_le_localHMaxBeforeTime S adm hemit hh).trans
    (storeBeforeTime_hMax_mono S sch v hut)
  rw [storeBeforeTime_eq_stateBefore_strictEventIndex S sch] at hlocal
  exact hlocal.trans (localHMax_le_honestHMaxBeforeIndex S rho _ hv)

/-- A height-pair attestation emitted by event `i` is below the emitter's
local maximum at every strict event prefix `n` beyond that event. Named twin
of earlier's `attestationHeight_le_stateBeforeIndex`. -/
theorem attestationHeight_le_stateBeforeIndex
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {i n : Nat} {v : V} {t : Time} {a : NamedAttestation V} {h : Height}
    (hi : rho.events[i]? = some (.tick v t))
    (hmem : Object.attest a ∈ (NamedNode.tick S v (rho.stateBefore S i v) t).2)
    (hin : i < n)
    (hh : a.height_pair.erase.height? = some h) :
    h ≤ (rho.stateBefore S n v).st.h_max := by
  have sch : ScheduleWellFormed S rho := adm.toNamedAdmissibleCore.toNamedScheduleWellFormed
  have hemit : rho.emits S v (Object.attest a) t := ⟨i, hi, hmem⟩
  have hlocal := honestEmittedHeight_le_localHMaxBeforeTime S adm hemit hh
  have heqst : rho.storeBeforeTime S v t = (rho.stateBefore S i v).st :=
    congrArg NamedNodeState.st
      (Proofs.NamedRuntime.tick_prefix_eq_strict S rho sch.sorted
        (NamedScheduleWellFormed.nodup sch) hi).symm
  rw [heqst] at hlocal
  exact hlocal.trans (stateBefore_hMax_mono S rho v (Nat.le_of_lt hin))

/-- An honest height-pair emission made by event `i` is below the honest
frontier at every strict event prefix `n` beyond that event. -/
theorem honestEmittedHeight_le_honestHMaxBeforeIndex
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {i n : Nat} {v : V} (hv : v ∈ rho.honest)
    {t : Time} {a : NamedAttestation V} {h : Height}
    (hi : rho.events[i]? = some (.tick v t))
    (hmem : Object.attest a ∈ (NamedNode.tick S v (rho.stateBefore S i v) t).2)
    (hin : i < n)
    (hh : a.height_pair.erase.height? = some h) :
    h ≤ honestHMaxBeforeIndex S rho n :=
  (attestationHeight_le_stateBeforeIndex S adm hi hmem hin hh).trans
    (localHMax_le_honestHMaxBeforeIndex S rho n hv)

/-- An honest height-pair emission made by time `t` is at most the moving
honest frontier at `t`. Named twin of earlier's
`honestEmittedHeight_le_honestHMaxAt`. -/
theorem honestEmittedHeight_le_honestHMaxAt
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v : V} (hv : v ∈ rho.honest) {a : NamedAttestation V}
    {u t : Time} {h : Height}
    (hemit : rho.emits S v (Object.attest a) u)
    (hh : a.height_pair.erase.height? = some h) (hut : u ≤ t) :
    h ≤ honestHMaxAt S rho t := by
  have sch : ScheduleWellFormed S rho := adm.toNamedAdmissibleCore.toNamedScheduleWellFormed
  exact (honestEmittedHeight_le_localHMax S adm hemit hh).trans
    ((stateAt_h_max_mono S sch v hut).trans
      (localHMax_le_honestHMaxAt S rho t hv))

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
