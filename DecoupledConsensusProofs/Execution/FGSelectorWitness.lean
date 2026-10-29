module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ValidatorClient.HeightPairCases
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.ActionSourceCore
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.GradePersistence
public import DecoupledConsensusProofs.Protocol.Duties.Proposals.RecoverySourceProgress
public import DecoupledConsensusProofs.Protocol.Duties.Inputs.WindowHeightSources
public import DecoupledConsensusProofs.Execution.NamedAncestry
public import DecoupledConsensusProofs.Protocol.ChainState.EntryHeight
public import DecoupledConsensusProofs.Execution.Wire
public import DecoupledConsensusProofs.Protocol.Duties.Proposals.Actions
public import DecoupledConsensusProofs.Execution.EmissionShape

@[expose] public section

/-!
# Exact FG-selector witness for emitted height rows

The emitted row is named. The selector source and its height are read from
the named action duty, and the retained body is supplied by the named action
source witness.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface

variable {V : Type} [DecidableEq V] [Fintype V]

/-- An honest emitted nonempty height row has its exact named selector body.

The erasure appears only at the geometric wire boundary. -/
theorem honestEmittedHeightRow_exactFGSelectorWitness
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {a : NamedAttestation V} {ta : Time} {h : Height}
    (haHon : a.val_index ∈ rho.honest)
    (hemit : rho.emits S a.val_index (Object.attest a) ta)
    (hh : a.height_pair.erase.height? = some h) :
    ∃ D : NamedBlock V, ∃ J : Block V,
      ta = (S.node a.val_index).act a.round ∧
        a = NamedActionReads.windowActionAttestationAt S rho a.val_index a.round ∧
        actionFGSource S (NamedActionReads.windowActionReadAt S rho a.val_index a.round) =
          some D.erase ∧
        D ∈ (NamedActionReads.windowActionReadAt S rho a.val_index a.round).st.bodies ∧
        ((NamedActionReads.windowActionReadAt S rho a.val_index a.round).st.core.σ D.erase).h = h ∧
        (Protocol.derive_named S.E S.cfg D).h = h ∧
        J = (Protocol.derive_named S.E S.cfg D).T_h ∧
        (a.height_pair.erase = HeightPair.target h J.root ∨
          a.height_pair.erase = HeightPair.timeout h) := by
  have ht := (WindowAction.run_emission_fields S hemit).1
  have haEq := ((WindowAction.run_emission_iff S rho
    adm.toNamedScheduleWellFormed a.val_index a.round a).mp
    (by simpa only [ht] using hemit)).2.2
  cases hp : a.height_pair with
  | empty => simp [hp, NamedHeightPair.erase, HeightPair.height?] at hh
  | vote h' root timeout =>
    have hh' : h' = h := by
      cases timeout <;> simpa [hp, NamedHeightPair.erase, HeightPair.height?] using hh
    subst h'
    obtain ⟨i, D, entry, hs, hheight, hentryRoot⟩ :=
      NamedWindowIntrinsicEntry.emitted_height_signed_source S rho hemit hp
    have hinput := NamedRuntime.tick_prefix_eq_strict S rho
      adm.toNamedScheduleWellFormed.sorted adm.toNamedScheduleWellFormed.nodup hs.1
    let n := NamedActionReads.windowActionReadAt S rho a.val_index a.round
    have hn : NamedActionReads.windowActionReadFrom S a.val_index
        (NamedRun.stateBefore S rho i a.val_index) a.round = n := by
      rw [hinput]
      rfl
    have hD : D ∈ n.st.bodies := by rw [← hn]; exact hs.2.2.2.1
    have hround : S.hc.round_of n.st.core.s = a.round := by
      exact WindowAction.actionRead_round S a.val_index _ a.round
    have hsource : actionFGSource S n = some D.erase := by
      change Protocol.fg_source_with (NamedProfile.gradeContract n.cache) S.E S.hc
        n.st.core.toHealing (S.hc.round_of n.st.core.s)
        (Protocol.grade2_block_with (NamedProfile.gradeContract n.cache)
          S.E S.hc n.st.core.toHealing (S.hc.round_of n.st.core.s)) = _
      rw [hround, ← hn]
      exact hs.2.2.2.2.1
    have hinv := WindowAction.windowRead_invariant S a.val_index
      (NamedRun.stateBeforeTime S rho ((S.node a.val_index).act a.round) a.val_index)
      ((S.node a.val_index).act a.round)
      (NamedRuntime.stateBeforeTime_invariants S rho _ a.val_index).1
    have hsigma : n.st.core.σ D.erase = Protocol.derive_named S.E S.cfg D :=
      hinv.1.1.2.2.2.2 D hD
    have hentry : entry.erase = (Protocol.derive_named S.E S.cfg D).T_h := hs.2.2.2.2.2.2.1
    have hroot : (Protocol.derive_named S.E S.cfg D).T_h.root = root := by
      rw [← hentry, NamedWire.erase_root]
      exact hentryRoot
    refine ⟨D, (Protocol.derive_named S.E S.cfg D).T_h, ht, haEq,
      hsource, hD, by rw [hsigma]; exact hheight, hheight, rfl, ?_⟩
    cases timeout <;> simp [hp, NamedHeightPair.erase, hroot]

/-- The point instance recovers the original exact selector witness
(PROTOCOL.md `sec:healing-schedule`). -/
theorem honestEmittedHeightRow_exactFGSelectorWitness_point
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hpoint : ∀ v r, (S.node v).act r = S.a r)
    {a : NamedAttestation V} {ta : Time} {h : Height}
    (haHon : a.val_index ∈ rho.honest)
    (hemit : rho.emits S a.val_index (Object.attest a) ta)
    (hh : a.height_pair.erase.height? = some h) :
    ∃ D : NamedBlock V, ∃ J : Block V,
      ta = S.a a.round ∧
        a = actionAttestationAt S rho a.val_index a.round ∧
        actionFGSource S (actionStoreAt S rho a.val_index a.round) =
          some D.erase ∧
        D ∈ (actionStoreAt S rho a.val_index a.round).st.bodies ∧
        ((actionStoreAt S rho a.val_index a.round).st.core.σ D.erase).h = h ∧
        (Protocol.derive_named S.E S.cfg D).h = h ∧
        J = (Protocol.derive_named S.E S.cfg D).T_h ∧
        (a.height_pair.erase = HeightPair.target h J.root ∨
          a.height_pair.erase = HeightPair.timeout h) := by
  have h := honestEmittedHeightRow_exactFGSelectorWitness S adm haHon hemit hh
  rw [WindowAction.windowActionAttestationAt_point S rho a.val_index a.round
    (hpoint _ _), WindowAction.windowActionReadAt_point S rho a.val_index a.round
    (hpoint _ _), hpoint] at h
  exact h

#print axioms honestEmittedHeightRow_exactFGSelectorWitness_point

#print axioms honestEmittedHeightRow_exactFGSelectorWitness

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
