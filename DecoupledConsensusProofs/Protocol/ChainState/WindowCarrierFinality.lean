module
public import DecoupledConsensusProofs.Protocol.ChainState.RawHeightCoverage
public import DecoupledConsensusProofs.Protocol.ChainState.W4FKChainFinalityWrite

/-!
# Live finality coverage from actual emission anchors

The causal inventory at each emission excludes its own row from the anchor's
chain. An unchanged justification from that anchor to the proposal parent
then gives checkpoint alignment at every intermediate carrier, and preserves
the row's finality bit. Read the actual-row finality-write kernel next
(PROTOCOL.md `process_attestation`, `process_height_events`).
-/
@[expose] public section

namespace DecoupledConsensusModel.Proofs.HealingSurface
open Execution Protocol Internal
open Statements.Instantiation

variable {V : Type} [DecidableEq V] [Fintype V]

/-- An actually emitted row covered by a proposal is live in its parent or
in its own payload, when the emitter's held checkpoint survives to the parent.
The parent-chain arm retains the finality membership requirement. -/
theorem emittedAttestation_finalityCoverage_of_anchor
    (S : Setup V) {rho : Run V} (core : NamedAdmissibleCore S rho)
    {i : Nat} {a : NamedAttestation V} {C B : NamedBlock V} {reader : V}
    (ha : a.val_index ∈ rho.honest)
    (hi : rho.events[i]? = some (.tick a.val_index ((S.node a.val_index).act a.round)))
    (hC : C ∈ (rho.stateBefore S (i + 1) reader).st.bodies)
    (hCP : NamedBlock.Preceq C B.parent)
    (hstable : (derive_named S.E S.cfg B.parent).h_j = (derive_named S.E S.cfg C).h_j)
    (hdebt : (derive_named S.E S.cfg B.parent).h_F < (derive_named S.E S.cfg B.parent).h_j)
    (hpair : a.finality_pair = some
      ⟨(derive_named S.E S.cfg C).h_j, (derive_named S.E S.cfg C).J.root⟩)
    (hcoverage : a ∈ NamedProposalRows.chainRows B.parent ∨ a ∈ B.attestations) :
    (a ∈ named_chain_attestations B.parent ∧
        a.val_index ∈ (derive_named S.E S.cfg B.parent).finalize) ∨
      a ∈ B.attestations := by
  rcases hcoverage with hchain | hown
  · have hchain' := chainRows_iff_named_chain.mp hchain
    exact Or.inl ⟨hchain', namedFinalize_mem_of_suffix_same_justification S.E S.cfg
      hCP hchain' (emittedAttestation_not_mem_named_chain_at_emission S core ha hi hC)
      hstable hdebt hpair⟩
  · exact Or.inr hown

/-- Actual row coverage plus causal emission anchors supplies the live arm
of the finality-write kernel. Each anchor's justification height agrees with
the parent; equality of its checkpoint block follows along the named chain. -/
theorem namedFinalizedAt_of_actionRows_at_emissionAnchors
    (S : Setup V) {rho : Run V} (core : NamedAdmissibleCore S rho)
    (hbot : BelowOneThird S rho.honest)
    {r : Round} {s : Slot} {B : NamedBlock V} {hJ : Height} {J : Block V}
    (hB : proposedBlockAt S rho s = some B)
    (hcoverage : ∀ v ∈ rho.honest,
      NamedActionReads.windowActionAttestationAt S rho v r ∈
          NamedProposalRows.chainRows B.parent ∨
        NamedActionReads.windowActionAttestationAt S rho v r ∈ B.attestations)
    (hparentHJ : (derive_named S.E S.cfg B.parent).h_j = hJ)
    (hparentJ : (derive_named S.E S.cfg B.parent).J = J)
    (hdebt : (derive_named S.E S.cfg B.parent).h_F < hJ)
    (hfinality : ∀ v ∈ rho.honest,
      (NamedActionReads.windowActionAttestationAt S rho v r).finality_pair = some ⟨hJ, J.root⟩)
    (hanchors : ∀ v ∈ rho.honest,
      let a := NamedActionReads.windowActionAttestationAt S rho v r
      ∃ (i : Nat) (C : NamedBlock V),
        rho.events[i]? = some (.tick a.val_index ((S.node a.val_index).act a.round)) ∧
        C ∈ (rho.stateBefore S (i + 1) v).st.bodies ∧
        NamedBlock.Preceq C B.parent ∧ (derive_named S.E S.cfg C).h_j = hJ) :
    NamedFinalizedAt S.E S.cfg B J hJ := by
  refine namedFinalizedAt_of_actionRows S hbot (r := r) hB ?_
    hparentHJ hparentJ rfl hdebt hfinality
  intro v hv
  obtain ⟨i, C, hi, hC, hCP, hCJ⟩ := hanchors v hv
  have hstable := hparentHJ.trans hCJ.symm
  have hCblock : (derive_named S.E S.cfg C).J = J := by
    rcases namedJustification_strict_or_eq_of_preceq S.E S.cfg hCP with hlt | heq
    · exact False.elim ((Nat.ne_of_lt hlt) hstable.symm)
    · exact heq.2.trans hparentJ
  have ha : (NamedActionReads.windowActionAttestationAt S rho v r).val_index ∈ rho.honest := by
    change (S.node v).val_index ∈ rho.honest
    simpa only [S.node_val_index] using hv
  have hcov := emittedAttestation_finalityCoverage_of_anchor S core ha hi hC hCP
    hstable (by simpa only [hparentHJ] using hdebt)
    (by simpa only [hCJ, hCblock] using hfinality v hv) (hcoverage v hv)
  simpa only [show (NamedActionReads.windowActionAttestationAt S rho v r).val_index = v
    from S.node_val_index v] using hcov

#print axioms emittedAttestation_finalityCoverage_of_anchor
#print axioms namedFinalizedAt_of_actionRows_at_emissionAnchors

end DecoupledConsensusModel.Proofs.HealingSurface

end
