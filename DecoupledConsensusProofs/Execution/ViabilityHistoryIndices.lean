module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Duties.Inputs.LayerAHistoryIndices
public import DecoupledConsensusProofs.Execution.EventIndexBridge
public import DecoupledConsensusProofs.Execution.CausalCarrierHistory
public import DecoupledConsensusProofs.Execution.ViabilityHistory
public import DecoupledConsensusProofs.Protocol.ChainState.FinalityCertificates
public import DecoupledConsensusProofs.Execution.OutageProvenance

@[expose] public section

/-!
# Index-bounded viability history

A quorum crossing uses an honest signed row emitted strictly before its
carrier acceptance, including self-proposals at the same time. The actual
input history then places its entry on the history chain
(PROTOCOL.md `sec:healing-schedule`).
-/


namespace DecoupledConsensusModel.Proofs.NamedOutageHistory.ViabilityHistory
open Execution Protocol
open Internal.NamedOutageEntry.History
open DecoupledConsensusModel.Proofs.NamedOutageHistory.ViabilityHistoryTime
variable {V : Type} [DecidableEq V] [Fintype V]


/-- The causal carrier ordering also supplies the non-strict index bound
used by retained-body consumers (PROTOCOL.md#on_block). -/
theorem row_emission_index_le_block_acceptance
    (S : Setup V) (rho : NamedRun V) (core : NamedAdmissibleCore S rho)
    (v : V) (carrier : NamedBlock V) (j : Nat) (received : Time)
    (hacc : NamedRun.acceptsAt S rho j v (.block carrier) received)
    (a : NamedAttestation V) (hrow : a ∈ carrier.attestations) (ha : a.val_index ∈ rho.honest)
    (k : Nat) {sent : Time} (hk : rho.events[k]? = some (.tick a.val_index sent))
    (hemit : NamedObject.attest a ∈ NamedRun.emittedAt S rho k a.val_index sent)
    (hsend : sent ≤ received) : k ≤ j :=
  (NamedCausalCarrierHistory.row_emission_index_lt_block_acceptance
    S rho core v carrier j received hacc a hrow ha k sent hk hemit hsend).le


/-- The exact progress crossing, with either timeout flag, is on the history
chain, index-bounded version. -/
theorem held_crossing_on_history
    (S : Setup V) (rho : NamedRun V) (core : NamedAdmissibleCore S rho)
    (n : Nat) (C : NamedBlock V) (hhistory : LayerAHistoryIdx S rho n C)
    (i : Nat) (v : V) (hv : v ∈ rho.honest) (hi : i ≤ n)
    (hbad : S.E.electorate.weightOf (Finset.univ \ rho.honest) < S.E.q)
    (D : NamedBlock V) (hD : D ∈ (NamedRun.stateBefore S rho i v).st.bodies)
    (h : Height) (hpos : 1 ≤ h) (hlt : h < (derive_named S.E S.cfg D).h) :
    ∃ X : NamedBlock V, NamedBlock.Preceq X D ∧
      (derive_named S.E S.cfg X).h = h ∧ NamedBlock.Preceq X C := by
  have hDscope := Proofs.NamedRuntime.blockInRun_of_direct S rho
    (Proofs.NamedRuntime.directBlock_of_prefix S rho hv i hD)
  obtain ⟨X, hXD, hXheight, Q, hQ, hrows⟩ :=
    NamedFinalityCertificates.height_crossing S.E S.cfg D h hpos hlt
  obtain ⟨signer, hsignerQ, hsignerHon⟩ := quorum_honest_member S rho Q hQ hbad
  obtain ⟨carrier, a, hcarrier, hrow, hsigner, hp⟩ := hrows signer hsignerQ
  have ha : a.val_index ∈ rho.honest := by simpa only [hsigner] using hsignerHon
  have hvote : ∃ timeout : Bool, a.height_pair = .vote h X.root timeout := by
    cases heq : a.height_pair with
    | empty => simp only [heq, NamedHeightPair.matchesEntry, Bool.false_eq_true] at hp
    | vote height target timeout =>
      have he : height = h ∧ target = X.root := by
        simpa only [heq, NamedHeightPair.matchesEntry, decide_eq_true_eq] using hp
      exact ⟨timeout, by rw [he.1, he.2]⟩
  obtain ⟨timeout, hvote⟩ := hvote
  obtain ⟨j, hj, received, hacc, hsend, hem⟩ :=
    NamedOutageProvenance.honest_held_ancestor_row_emission S rho
      core.toNamedUnforgeable i v hD hcarrier hrow ha
  obtain ⟨k, hk, hemit⟩ := hem
  have hjn : j < n := lt_of_lt_of_le hj hi
  have hkj : k ≤ j :=
    row_emission_index_le_block_acceptance S rho core v carrier j received hacc
      a hrow ha k hk hemit hsend
  have hkn : k < n := lt_of_le_of_lt hkj hjn
  obtain ⟨source, entry, hsourceScope, hsourceHeld, hentryScope, hentryHeld,
    hval, htime, hcreate, hselector, hfields, hheight, htarget, herase,
    hancestor, hsameHeight, hroot, hentryC⟩ :=
    hhistory.2.2.1 k a.val_index ((S.node a.val_index).act a.round) a ha hk hemit hkn
      h X.root timeout hvote
  have heq : entry = X := core.root_injective C D hhistory.1 hDscope
    entry X (Or.inl hentryC) (Or.inr hXD) hroot
  subst entry
  exact ⟨X, hXD, hXheight, hentryC⟩

end DecoupledConsensusModel.Proofs.NamedOutageHistory.ViabilityHistory

end
