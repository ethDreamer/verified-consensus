module
public import DecoupledConsensusProofs.Protocol.ChainState.CarrierFinalityFirstHalf
public import DecoupledConsensusProofs.Protocol.ChainState.RawHeightCoverage

/-!
# Actual emission anchors for the first carrier

Opening alignment identifies a retained named source at each action event.
On the live height branch, its ancestry and the parent plateau convert bare
carriage into the first-half record's live progress and target coverage
(PROTOCOL.md `process_attestation`, `proposal_attestations`).
-/
@[expose] public section
namespace DecoupledConsensusModel.Proofs.HealingSurface
open Execution Protocol Internal Statements.Instantiation
variable {V : Type} [DecidableEq V] [Fintype V]

/-- The actual source's named body is held after the action tick. This uses
the actual input and root uniqueness, not a paper-time body identification. -/
theorem openingAligned_source_mem_at_action_event
    (S : Setup V) {rho : Run V} (core : NamedAdmissibleCore S rho)
    {q : Round} {v : V} {i : Nat} {P0 : NamedBlock V}
    (hv : v ∈ rho.honest)
    (hi : rho.events[i]? = some (.tick v ((S.node v).act q)))
    (hP0run : RunBlock S rho P0)
    (hsource : actionFGSource S (NamedActionReads.windowActionReadAt S rho v q) =
      some P0.erase) :
    P0 ∈ (rho.stateBefore S (i + 1) v).st.bodies := by
  let n := NamedActionReads.windowActionReadAt S rho v q
  have hn : n = NamedActionReads.windowActionReadFrom S v (rho.stateBefore S i v) q := by
    dsimp only [n, NamedActionReads.windowActionReadAt]
    exact congrArg (fun st => NamedActionReads.windowActionReadFrom S v st q)
      (NamedRuntime.tick_prefix_eq_strict S rho core.sorted core.nodup hi).symm
  have hinv : NamedConfirmationMembership.Invariant S.E S.cfg n.st := by
    rw [hn]
    exact WindowAction.windowRead_invariant S v _ _
      (NamedRuntime.stateBefore_invariants S rho i v).1
  have hmem : P0.erase ∈ n.st.core.T :=
    NamedActionSources.frame_fg_source_mem S n.cache n.st
      (S.hc.round_of n.st.core.s) hinv hsource
  rw [hinv.1.1.1] at hmem
  obtain ⟨D, hD, he⟩ := Finset.mem_image.mp hmem
  have hpost : (rho.stateBefore S (i + 1) v).st.bodies = n.st.bodies := by
    change (NamedRun.stateBefore S rho (i + 1) v).st.bodies = n.st.bodies
    rw [NamedRuntime.stateBefore_tick S rho hi, hn]
    exact (WindowAction.tick_input_projection S v _ q).1
  have hDpost : D ∈ (rho.stateBefore S (i + 1) v).st.bodies := hpost ▸ hD
  have hDrun : RunBlock S rho D := NamedRuntime.blockInRun_of_direct S rho
    (NamedRuntime.directBlock_of_prefix S rho hv (i + 1) hDpost)
  have hDP : D = P0 := core.root_injective D P0 hDrun hP0run D P0
    (Or.inl (NamedAncestry.named_self D)) (Or.inr (NamedAncestry.named_self P0))
    (by rw [← NamedWire.erase_root D, ← NamedWire.erase_root P0, he])
  exact hDP ▸ hDpost

/-- The first-half live coverage field follows from aligned actual rows and
the consumer's parent plateau. Historical chain membership retains both live
progress and target-participation requirements. -/
theorem openingAligned_actionCoverage_of_plateau
    (S : Setup V) {rho : Run V} (core : NamedAdmissibleCore S rho)
    {q : Round} {P0 B : NamedBlock V}
    (haligned : OpeningAlignedCarrierCoverage S rho q)
    (hP0 : proposedBlockAt S rho (S.hc.opening_slot q) = some P0)
    (hP0run : RunBlock S rho P0)
    (hrows : ∀ v ∈ rho.honest,
      NamedActionReads.windowActionAttestationAt S rho v q ∈
        NamedProposalRows.chainRows B.parent ∨
      NamedActionReads.windowActionAttestationAt S rho v q ∈ B.attestations)
    (hticks : ∀ v ∈ rho.honest, ∃ i : Nat,
      rho.events[i]? = some (NamedEvent.tick v ((S.node v).act q)))
    (htargets : ∀ v ∈ rho.honest,
      (actionAttestationAt S rho v q).height_pair =
        .vote (derive_named S.E S.cfg P0).h (derive_named S.E S.cfg P0).T_h.root false)
    (hparent : NamedBlock.Preceq P0 B.parent)
    (hplateau : (derive_named S.E S.cfg B.parent).h =
      (derive_named S.E S.cfg P0).h) :
    NamedHonestActionProposalCoverageAt S rho q B
      (derive_named S.E S.cfg P0).h (derive_named S.E S.cfg P0).T_h.root := by
  intro v hv
  let a := NamedActionReads.windowActionAttestationAt S rho v q
  obtain ⟨i, hi⟩ := hticks v hv
  have hbody := openingAligned_source_mem_at_action_event S core hv hi hP0run
    (haligned.openingSource v hv P0 hP0)
  have hpair : a.height_pair = .vote (derive_named S.E S.cfg P0).h
      (derive_named S.E S.cfg P0).T_h.root false :=
    (haligned.heightPair v hv).trans (htargets v hv)
  have hval : a.val_index = v := S.node_val_index v
  have hround : a.round = q := by
    exact WindowAction.actionRead_round S v _ q
  have hi' : rho.events[i]? = some (.tick a.val_index ((S.node a.val_index).act a.round)) := by
    simpa only [hval, hround] using hi
  have hcov := emittedAttestation_coveredAtProposal_of_plateau S core
    (by simpa only [hval] using hv) hi' hbody hparent hplateau (Or.inl hpair) (hrows v hv)
  exact ⟨by simpa only [hval] using hcov, Or.inl hpair⟩

#print axioms openingAligned_source_mem_at_action_event
#print axioms openingAligned_actionCoverage_of_plateau
end DecoupledConsensusModel.Proofs.HealingSurface
end
