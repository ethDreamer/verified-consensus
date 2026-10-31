module
public import DecoupledConsensusProofs.Protocol.Duties.Inputs.WindowHistoryFields
public import DecoupledConsensusProofs.Protocol.Duties.Inputs.JustificationHistoryIndices
public import DecoupledConsensusProofs.Protocol.Handlers.FinalityCarrier

/-!
# Checkpoints at actual action inputs

Post-tick checkpoint carriers use only rows emitted strictly before that tick.
This supplies the SG selector's fallback without consuming current-event
history (PROTOCOL.md `sec:healing-schedule`).
-/
@[expose] public section
namespace DecoupledConsensusModel.Proofs.NamedWindowHistoryState
open Execution Protocol Internal.NamedOutageEntry.History
open NamedOutageHistory NamedWindowHistoryFields
variable {V : Type} [DecidableEq V] [Fintype V]

/-- A finality carrier's certificate is bounded by its causal emission history
(PROTOCOL.md#on_block). -/
theorem causal_finalized_c1
    (S : Setup V) (rho : NamedRun V) (core : NamedAdmissibleCore S rho)
    (m : Nat) (C : NamedBlock V) (hCrun : NamedRun.blockInRun S rho C)
    (hc1 : Clause1Idx S rho m C)
    (i : Nat) (v : V) (hv : v ∈ rho.honest)
    (hbad : S.E.electorate.weightOf (Finset.univ \ rho.honest) < S.E.q)
    (D : NamedBlock V) (hD : D ∈ (NamedRun.stateBefore S rho i v).st.bodies)
    (hcausal : Internal.NamedJointOutage.CausalCarrierRowsBefore S rho m D) :
    ∃ F : NamedBlock V, NamedBlock.Preceq F D ∧
      F.erase = (derive_named S.E S.cfg D).F ∧ NamedBlock.Preceq F C := by
  have hDscope := Proofs.NamedRuntime.blockInRun_of_direct S rho
    (Proofs.NamedRuntime.directBlock_of_prefix S rho hv i hD)
  by_cases hz : (derive_named S.E S.cfg D).h_F = 0
  · have hgen := NamedFinalityCertificates.finalized_zero_is_genesis S.E S.cfg D hz
    exact ⟨.genesis, ViabilityHistoryTime.genesis_preceq D, hgen.symm,
      ViabilityHistoryTime.genesis_preceq C⟩
  · obtain ⟨F, hFD, hFE, Q, hQ, hrows⟩ :=
      NamedFinalityCertificates.finality_certificate S.E S.cfg D hz
    obtain ⟨signer, hsignerQ, hsignerHon⟩ :=
      ViabilityHistoryTime.quorum_honest_member S rho Q hQ hbad
    obtain ⟨carrier, a, hcarrier, hrow, hsigner, hp⟩ := hrows signer hsignerQ
    have ha : a.val_index ∈ rho.honest := by simpa only [hsigner] using hsignerHon
    obtain ⟨k, hkn, hk, hemit⟩ := hcausal carrier hcarrier a hrow ha
    obtain ⟨H, K, hHscope, hHheld, hHhead, hKscope, hKheld, hKJ,
      hval, htime, hcreate, hheight, htarget, hhj, hJ, hhF, hroot, hKC⟩ :=
      hc1 k a.val_index ((S.node a.val_index).act a.round) a ha hk hemit hkn
        ⟨(derive_named S.E S.cfg D).h_F, F.root⟩ hp
    have hKF : K.root = F.root := hroot.symm
    have heq : K = F := core.root_injective C D hCrun hDscope
      K F (Or.inl hKC) (Or.inr hFD) hKF
    subst K
    exact ⟨F, hFD, hFE, hKC⟩

/-- Both action-input checkpoints lie on the history chain using only earlier
emissions, including at a proposal tick (PROTOCOL.md `sec:healing-schedule`). -/
theorem checkpoints_at_action
    (S : Setup V) (rho : NamedRun V) (core : NamedAdmissibleCore S rho)
    (m : Nat) (C : NamedBlock V) (hhist : LayerAHistoryIdx S rho m C)
    (i : Nat) (v : V) (r : Round) (hv : v ∈ rho.honest) (him : i ≤ m)
    (hi : rho.events[i]? = some (.tick v ((S.node v).act r)))
    (hbad : S.E.electorate.weightOf (Finset.univ \ rho.honest) < S.E.q) :
    let input := NamedActionReads.windowActionReadFrom S v (NamedRun.stateBefore S rho i v) r
    (∃ J : NamedBlock V, NamedRun.blockInRun S rho J ∧ J ∈ input.st.bodies ∧
      J.erase = input.st.core.J ∧ NamedBlock.Preceq J C) ∧
    (∃ F : NamedBlock V, NamedRun.blockInRun S rho F ∧ F ∈ input.st.bodies ∧
      F.erase = input.st.core.F ∧ NamedBlock.Preceq F C) := by
  intro input
  have hproj := WindowAction.tick_input_projection S v (NamedRun.stateBefore S rho i v) r
  have hpost : (NamedRun.stateBefore S rho (i + 1) v).st.bodies = input.st.bodies ∧
      (NamedRun.stateBefore S rho (i + 1) v).st.core.J = input.st.core.J ∧
      (NamedRun.stateBefore S rho (i + 1) v).st.core.F = input.st.core.F := by
    rw [NamedRuntime.stateBefore_tick S rho hi]
    exact hproj
  have hcausal (D : NamedBlock V)
      (hD : D ∈ (NamedRun.stateBefore S rho (i + 1) v).st.bodies) :
      Internal.NamedJointOutage.CausalCarrierRowsBefore S rho m D := by
    intro A hAD a ha hhon
    obtain ⟨k, hk, he, hem⟩ :=
      NamedCausalCarrierHistory.held_carrier_rows_before S rho core i v hD A hAD a ha hhon
    exact ⟨k, lt_of_lt_of_le hk him, he, hem⟩
  constructor
  · obtain ⟨D, hD, hDJ, _⟩ := PrefixCarrier.justification_carrier_stateBefore S rho (i + 1) v
    obtain ⟨J, hJrun, hJmem, _, hJe, hJC, _⟩ :=
      GuardProofs.causal_justification_checkpoint_on_history S rho core m C hhist
        (i + 1) v hv hbad D hD (hcausal D hD)
    exact ⟨J, hJrun, hpost.1 ▸ hJmem, hJe.trans (hDJ.trans hpost.2.1), hJC⟩
  · obtain ⟨D, hD, hDF⟩ := FinalityCarrier.finality_carrier_stateBefore S rho (i + 1) v
    obtain ⟨F, hFD, hFe, hFC⟩ := causal_finalized_c1 S rho core m C hhist.1 hhist.2.1
      (i + 1) v hv hbad D hD (hcausal D hD)
    have hFmem := ViabilityHistoryTime.ancestor_body_mem
      (NamedRuntime.stateBefore_invariants S rho (i + 1) v).1.1.1.2.2.1 hD hFD
    exact ⟨F, NamedRuntime.blockInRun_of_direct S rho
      (NamedRuntime.directBlock_of_prefix S rho hv (i + 1) hFmem),
      hpost.1 ▸ hFmem, hFe.trans (hDF.trans hpost.2.2), hFC⟩

#print axioms causal_finalized_c1
#print axioms checkpoints_at_action
end DecoupledConsensusModel.Proofs.NamedWindowHistoryState
