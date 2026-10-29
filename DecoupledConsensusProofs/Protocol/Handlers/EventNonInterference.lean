module
public import DecoupledConsensusProofs.Execution.EventConflictingCarrierBand
public import DecoupledConsensusProofs.Protocol.ChainState.JustificationCertificates
public import DecoupledConsensusProofs.Protocol.Handlers.JustificationCarrier
public import DecoupledConsensusProofs.Protocol.Handlers.StoreBridge

/-!
# FG noninterference from strict event history

Both justification and height crossings use honest entries emitted before
an accepted carrier. Thus the post-event FG view needs only the strict prior
entry history, including when a tick proposes a carrier before attesting.
-/
@[expose] public section
namespace DecoupledConsensusModel.Proofs.NamedEventNonInterference
open Execution Internal.NamedOutageEntry Internal.NamedStableChainOutage
open Internal.NamedJointOutage Protocol
variable {V : Type} [DecidableEq V] [Fintype V]

omit [Fintype V] in
private theorem named_preceq_self (B : NamedBlock V) : NamedBlock.Preceq B B := by
  cases B <;> simp [NamedBlock.Preceq, NamedBlock.preceq]

omit [Fintype V] in
private theorem genesis_preceq (B : NamedBlock V) : NamedBlock.Preceq .genesis B := by
  induction B with
  | genesis => simp [NamedBlock.Preceq, NamedBlock.preceq]
  | node parent s root votes support rows proposer ih =>
    simp only [NamedBlock.Preceq, NamedBlock.preceq, Bool.or_eq_true]
    exact Or.inr ih



private theorem quorum_honest_member (S : Setup V) (rho : NamedRun V)
    (Q : Finset V) (hQ : S.E.electorate.IsQuorum Q)
    (hbad : S.E.electorate.weightOf (Finset.univ \ rho.honest) < S.E.q) :
    ∃ signer ∈ Q, signer ∈ rho.honest := by
  by_contra hn
  have hsub : Q ⊆ Finset.univ \ rho.honest := by
    intro signer hs
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hh => hn ⟨signer, hs, hh⟩⟩
  have hm := S.E.electorate.weightOf_mono hsub
  have hq : S.E.q ≤ S.E.electorate.weightOf Q := hQ
  omega

private theorem held_row_target_compatible (S : Setup V) (rho : NamedRun V)
    (b0 b1 : Time) (j : Nat) (Pn : NamedBlock V)
    (hexec : OutageExecution S rho b0 b1)
    (hentry : IntrinsicHighEntryHistoryIdx S rho Pn j)
    (reader : V)
    {D carrier X : NamedBlock V}
    (hD : D ∈ (NamedRun.stateBefore S rho (j + 1) reader).st.bodies)
    (hcarrier : NamedBlock.Preceq carrier D)
    {a : NamedAttestation V} (hrow : a ∈ carrier.attestations)
    (ha : a.val_index ∈ rho.honest)
    {h : Height} {root : BlockId} {timeout : Bool}
    (hp : a.height_pair = .vote h root timeout)
    (hXscope : NamedRun.blockInRun S rho X) (hXroot : X.root = root) :
    NamedBlock.compatible Pn X = true := by
  obtain ⟨i, hij, hi, hem⟩ :=
    NamedCausalCarrierHistory.held_carrier_rows_before S rho hexec.core j reader hD
      carrier hcarrier a hrow ha
  obtain ⟨source, entry, hSigned, hSourceHeight, hEntryRoot⟩ :=
    NamedWindowIntrinsicEntry.emitted_height_signed_source_at S rho hexec.core.nodup hi hem hp
  have hcompat : NamedBlock.compatible Pn entry = true :=
    hentry i hij a source entry ha hSigned
  have hSourceScope := (NamedWindowIntrinsicEntry.signed_source_entry_scope S rho ha hSigned).1
  have hEntrySource := hSigned.2.2.2.2.2.1
  have hRootEq : entry.root = X.root := hEntryRoot.trans hXroot.symm
  have hEntryEq : entry = X :=
    hexec.core.toNamedRootCollisionFree.root_injective source X hSourceScope hXscope
      entry X (Or.inl hEntrySource) (Or.inr (named_preceq_self X)) hRootEq
  exact hEntryEq ▸ hcompat


private theorem justified_compatible_at_event (S : Setup V) (rho : NamedRun V)
    (b0 b1 : Time) (s : Round) (j : Nat) (Pn : NamedBlock V)
    (hexec : OutageExecution S rho b0 b1) (hmargin : FormationMargin S s b0)
    (hsleep : OutageSleepyThroughout S rho)
    (hentry : IntrinsicHighEntryHistoryIdx S rho Pn j)
    (reader : V) (hreader : reader ∈ rho.honest) :
    Block.compatible Pn.erase
      (NamedRun.stateBefore S rho (j + 1) reader).st.core.J = true := by
  obtain ⟨D, hD, hDJ, _⟩ :=
    NamedJustificationCarrier.justification_carrier_stateBefore S rho (j + 1) reader
  by_cases hz : (derive_named S.E S.cfg D).h_j = 0
  · have hgen := NamedJustificationCertificates.justified_zero_is_genesis S.E S.cfg D hz
    rw [← hDJ, hgen]
    have hc : NamedBlock.compatible Pn .genesis = true := by
      simp only [NamedBlock.compatible, Bool.or_eq_true]
      exact Or.inr (genesis_preceq Pn)
    exact Proofs.NamedWire.erase_compatible hc
  · obtain ⟨J, hJD, hJE, Q, hQ, hrows⟩ :=
      NamedJustificationCertificates.justification_certificate S.E S.cfg D hz
    have hDscope := NamedRuntime.blockInRun_of_direct S rho
      (NamedRuntime.directBlock_of_prefix S rho hreader (j + 1) hD)
    have hJscope := Proofs.NamedRuntime.blockInRun_of_ancestor S rho hDscope hJD
    have hbad := Proofs.NamedOutageInputs.boundary_faulty_lt_quorum S rho b0 b1 s
      hexec hmargin hsleep
    obtain ⟨signer, hsignerQ, hsignerHon⟩ := quorum_honest_member S rho Q hQ hbad
    obtain ⟨carrier, a, hcarrier, hrow, hv, hp⟩ := hrows signer hsignerQ
    have ha : a.val_index ∈ rho.honest := by simpa only [hv] using hsignerHon
    have hcompatible := held_row_target_compatible S rho b0 b1 j Pn hexec hentry
      reader hD hcarrier hrow ha hp hJscope rfl
    have hraw := Proofs.NamedWire.erase_compatible hcompatible
    simpa only [hJE, hDJ] using hraw

/-- Finality is compatible with the prefix using only earlier honest entries. -/
theorem finalized_compatible_at_event (S : Setup V) (rho : NamedRun V)
    (b0 b1 : Time) (s : Round) (j : Nat) (Pn : NamedBlock V)
    (hexec : OutageExecution S rho b0 b1) (hmargin : FormationMargin S s b0)
    (hsleep : OutageSleepyThroughout S rho)
    (hentry : IntrinsicHighEntryHistoryIdx S rho Pn j)
    (reader : V) (hreader : reader ∈ rho.honest) :
    Block.compatible Pn.erase
      (NamedRun.stateBefore S rho (j + 1) reader).st.core.F = true := by
  have hJ := justified_compatible_at_event S rho b0 b1 s j Pn hexec hmargin hsleep
    hentry reader hreader
  have hFJ : Block.Preceq (NamedRun.stateBefore S rho (j + 1) reader).st.core.F
      (NamedRun.stateBefore S rho (j + 1) reader).st.core.J :=
    NamedStoreBridge.finalized_preceq_justified_stateBefore S rho (j + 1) reader
  rcases (show Block.Preceq Pn.erase (NamedRun.stateBefore S rho (j + 1) reader).st.core.J ∨
      Block.Preceq (NamedRun.stateBefore S rho (j + 1) reader).st.core.J Pn.erase by
    simpa only [Block.compatible, Bool.or_eq_true] using! hJ) with hPJ | hJP
  · exact Block.compatible_of_preceq_common hPJ hFJ
  · simp only [Block.compatible, Bool.or_eq_true]
    exact Or.inr (Block.preceq_trans hFJ hJP)

private theorem fg_root_compatible_at_event (S : Setup V) (rho : NamedRun V)
    (b0 b1 : Time) (s : Round) (j : Nat) (Pn : NamedBlock V)
    (hexec : OutageExecution S rho b0 b1) (hmargin : FormationMargin S s b0)
    (hsleep : OutageSleepyThroughout S rho)
    (hentry : IntrinsicHighEntryHistoryIdx S rho Pn j)
    (reader : V) (hreader : reader ∈ rho.honest) :
    Block.compatible Pn.erase
      (Protocol.get_fg_root
        (NamedRun.stateBefore S rho (j + 1) reader).st.core.toHealing.toFG) = true := by
  have hJ := justified_compatible_at_event S rho b0 b1 s j Pn hexec hmargin hsleep
    hentry reader hreader
  have hF := finalized_compatible_at_event S rho b0 b1 s j Pn hexec hmargin hsleep
    hentry reader hreader
  unfold Protocol.get_fg_root
  split_ifs <;> assumption



/-- A held prefix stays viable when all conflicting carriers obey the causal band. -/
theorem viable_at_event
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time) (s : Round) (j : Nat)
    (Pn : NamedBlock V) (hexec : OutageExecution S rho b0 b1)
    (hmargin : FormationMargin S s b0) (hsleep : OutageSleepyThroughout S rho)
    (hentry : IntrinsicHighEntryHistoryIdx S rho Pn j)
    (w : V) (hw : w ∈ rho.honest)
    (hheld : Pn ∈ (NamedRun.stateBefore S rho (j + 1) w).st.bodies)
    (hFP : Block.Preceq (NamedRun.stateBefore S rho (j + 1) w).st.core.F Pn.erase) :
    Pn.erase ∈ Protocol.V_tree
      (NamedRun.stateBefore S rho (j + 1) w).st.core.toHealing.toFG := by
  set st := (NamedRun.stateBefore S rho (j + 1) w).st with hst
  have hcoh : Proofs.NamedStore.Coherent S.E S.cfg st :=
    (Proofs.NamedRuntime.stateBefore_invariants S rho (j + 1) w).1.1.1
  have hPraw : Pn.erase ∈ st.core.T := by
    rw [hcoh.1]
    exact Finset.mem_image_of_mem NamedBlock.erase hheld
  have hWitness : ∃ W ∈ st.core.T, Block.Preceq Pn.erase W ∧
      st.core.h_max - 1 ≤ (st.core.σ W).h := by
    by_cases hLow : st.core.h_max ≤ (derive_named S.E S.cfg Pn).h + 1
    · refine ⟨Pn.erase, hPraw, Block.preceq_self _, ?_⟩
      rw [hcoh.2.2.2.2 Pn hheld]
      exact Nat.sub_le_iff_le_add.mpr hLow
    · obtain ⟨D, hD, hMax⟩ :=
        NamedMaximumCarrier.maximum_carrier_stateBefore S rho (j + 1) w
      have hDcompatible : NamedBlock.compatible Pn D = true := by
        by_contra hc
        have hBand := NamedEventConflictingCarrierBand.held_conflicting_carrier_band
          S rho b0 b1 s j Pn
          hexec hmargin hsleep hentry w hw hD (Bool.eq_false_of_not_eq_true hc)
        rw [hMax] at hBand
        exact hLow hBand
      have hPD : NamedBlock.Preceq Pn D := by
        rcases (show NamedBlock.Preceq Pn D ∨ NamedBlock.Preceq D Pn by
          simpa only [NamedBlock.compatible, Bool.or_eq_true] using! hDcompatible) with
            hAbove | hAncestor
        · exact hAbove
        · have hle := Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg hAncestor
          rw [hMax] at hle
          exact False.elim (hLow (hle.trans (Nat.le_succ _)))
      have hDraw : D.erase ∈ st.core.T := by
        rw [hcoh.1]
        exact Finset.mem_image_of_mem NamedBlock.erase hD
      refine ⟨D.erase, hDraw, Proofs.NamedWire.erase_preceq hPD, ?_⟩
      rw [hcoh.2.2.2.2 D hD, hMax]
      exact Nat.sub_le _ _
  change Pn.erase ∈ Protocol.viable_tree st.core.σ st.core.F st.core.h_max st.core.T
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_filter.mpr ⟨hPraw, hFP⟩, ?_⟩
  simpa only [Protocol.viable, decide_eq_true_eq] using hWitness

#print axioms viable_at_event

/-- Earlier honest-entry history preserves the FG choice and finality
compatibility after one event, including the proposal before an attestation.
Holding the prefix is a local input; no extra delivery or regime premise is used. -/
theorem fg_noninterference_at_event
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time) (s : Round) (j : Nat)
    (Pn : NamedBlock V) (hexec : OutageExecution S rho b0 b1)
    (hmargin : FormationMargin S s b0) (hsleep : OutageSleepyThroughout S rho)
    (hentry : IntrinsicHighEntryHistoryIdx S rho Pn j)
    (w : V) (hw : w ∈ rho.honest)
    (hheld : Pn ∈ (NamedRun.stateBefore S rho (j + 1) w).st.bodies) :
    (Block.Preceq Pn.erase
       (get_fg_root (NamedRun.stateBefore S rho (j + 1) w).st.core.toHealing.toFG) ∨
     Pn.erase ∈ get_filtered_block_tree
       (NamedRun.stateBefore S rho (j + 1) w).st.core.toHealing.toFG) ∧
    Block.compatible Pn.erase (NamedRun.stateBefore S rho (j + 1) w).st.core.F = true := by
  refine ⟨?_, finalized_compatible_at_event S rho b0 b1 s j Pn hexec
    hmargin hsleep hentry w hw⟩
  set st := (NamedRun.stateBefore S rho (j + 1) w).st with hst
  have hcoh : Proofs.NamedStore.Coherent S.E S.cfg st :=
    (Proofs.NamedRuntime.stateBefore_invariants S rho (j + 1) w).1.1.1
  have hcompatible := fg_root_compatible_at_event S rho b0 b1 s j Pn hexec
    hmargin hsleep hentry w hw
  rcases (show Block.Preceq Pn.erase (Protocol.get_fg_root st.core.toHealing.toFG) ∨
      Block.Preceq (Protocol.get_fg_root st.core.toHealing.toFG) Pn.erase by
    simpa only [Block.compatible, Bool.or_eq_true] using! hcompatible) with hPast | hRoot
  · exact Or.inl hPast
  · right
    have hFRoot : Block.Preceq st.core.F (Protocol.get_fg_root st.core.toHealing.toFG) :=
      Proofs.Records.preceq_get_fg_root_of_F (st := st.core.toHealing.toFG)
        (NamedStoreBridge.finalized_preceq_justified_stateBefore S rho (j + 1) w)
    have hFP : Block.Preceq st.core.F Pn.erase := Block.preceq_trans hFRoot hRoot
    exact Proofs.Records.mem_filtered_of_mem_V_tree
      (viable_at_event S rho b0 b1 s j Pn hexec hmargin hsleep hentry w hw hheld hFP) hRoot


#print axioms fg_noninterference_at_event

end DecoupledConsensusModel.Proofs.NamedEventNonInterference
