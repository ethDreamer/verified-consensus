module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Duties.Inputs.WindowHistoryFields
public import DecoupledConsensusProofs.Protocol.Grades.JointHistoryGapsIdx
public import DecoupledConsensusProofs.Protocol.Grades.SGVoteHistoryIndices
public import DecoupledConsensusProofs.Execution.HeldJustificationHistoryIdx
public import DecoupledConsensusProofs.Protocol.Duties.Inputs.JustificationHistoryIndices
public import DecoupledConsensusProofs.Execution.ViabilityHistoryIndices
public import DecoupledConsensusProofs.Protocol.Duties.Inputs.LayerAHistoryIndices
public import DecoupledConsensusProofs.Execution.EventIndexBridge
public import DecoupledConsensusProofs.Execution.IdxGaps
public import DecoupledConsensusProofs.Protocol.Handlers.FinalityCarrier

/-!
# Event steps for the renewal history

Delivery and inert-tick steps retain the witness. Honest action fields use
`NamedWindowHistoryFields`; their finality heads are post-tick bodies whose
certificate rows precede the current event. Clause (3) follows from the
finality-emission clause and a retained carrier (PROTOCOL.md `sec:healing-schedule`).
-/
@[expose] public section

namespace DecoupledConsensusModel.Proofs.NamedOutageHistory.IdxDriverSteps
open Execution Internal.NamedOutageEntry Protocol
open Internal.NamedOutageEntry.History
open DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol
open JointHistoryProducersTime
variable {V : Type} [DecidableEq V] [Fintype V]

private theorem witnessProvenanceIdx_mono (S : Setup V) (rho : NamedRun V)
    {n m : Nat} {C : NamedBlock V} (h : WitnessProvenanceIdx S rho n C)
    (hle : n ≤ m) : WitnessProvenanceIdx S rho m C := by
  rcases h with rfl | ⟨i, v, r, hin, hv, he, hbody, hroot⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨i, v, r, hin.trans hle, hv, he, hbody, hroot⟩

/-! ## Clause (1) on its own -/

open NamedWindowHistoryFields

/-! ## Witness monotonicity -/

theorem historyIdx_mono (S : Setup V) (rho : NamedRun V) (m : Nat) (C C' : NamedBlock V)
    (h : LayerAHistoryIdx S rho m C) (hCC' : NamedBlock.Preceq C C')
    (hC'run : NamedRun.blockInRun S rho C') : LayerAHistoryIdx S rho m C' := by
  obtain ⟨-, h1, h2, h3⟩ := h
  refine ⟨hC'run, ?_, ?_, ?_⟩
  · intro i v ta a hv hi hem hlt fp hfp
    obtain ⟨H, K, hHscope, hHheld, hHhead, hKscope, hKheld, hKJ,
      hval, htime, hcreate, hheight, htarget, hhj, hJ, hhF, hroot, hKC⟩ :=
      h1 i v ta a hv hi hem hlt fp hfp
    exact ⟨H, K, hHscope, hHheld, hHhead, hKscope, hKheld, hKJ,
      hval, htime, hcreate, hheight, htarget, hhj, hJ, hhF, hroot,
      named_preceq_trans hKC hCC'⟩
  · intro i v ta a hv hi hem hlt h T timeout hp
    obtain ⟨source, entry, hsourceScope, hsourceHeld, hentryScope, hentryHeld,
      hval, htime, hcreate, hselector, hfields, hheight, htarget, herase,
      hancestor, hsameHeight, hroot, hentryC⟩ := h2 i v ta a hv hi hem hlt h T timeout hp
    exact ⟨source, entry, hsourceScope, hsourceHeld, hentryScope, hentryHeld,
      hval, htime, hcreate, hselector, hfields, hheight, htarget, herase,
      hancestor, hsameHeight, hroot, named_preceq_trans hentryC hCC'⟩
  · intro i v hv hi
    obtain ⟨F, hFscope, hFmem, hFe, hFC⟩ := h3 i v hv hi
    exact ⟨F, hFscope, hFmem, hFe, named_preceq_trans hFC hCC'⟩

theorem jointHistoryIdx_mono (S : Setup V) (rho : NamedRun V) (m : Nat) (C C' : NamedBlock V)
    (h : LayerAJointHistoryIdx S rho m C) (hCC' : NamedBlock.Preceq C C')
    (hC'run : NamedRun.blockInRun S rho C')
    (hprov : WitnessProvenanceIdx S rho m C') :
    LayerAJointHistoryIdx S rho m C' := by
  refine ⟨historyIdx_mono S rho m C C' h.1 hCC' hC'run, ?_, ?_, hprov⟩
  · intro i v ta a hv hi hem hlt key hkey
    obtain ⟨K, hKrun, hKmem, hKroot, hKC⟩ := h.2.1 i v ta a hv hi hem hlt key hkey
    exact ⟨K, hKrun, hKmem, hKroot, named_preceq_trans hKC hCC'⟩
  · intro i v r hv hi hlt
    obtain ⟨L, hLrun, hLmem, hLe, hLC⟩ := h.2.2.1 i v r hv hi hlt
    exact ⟨L, hLrun, hLmem, hLe, named_preceq_trans hLC hCC'⟩

/-! ## Clause (1) alone carries clause (3) -/

/-- `ViabilityHistory.held_finalized_on_history`, with the packaged
history hypothesis replaced by the two projections its proof actually reads. -/
theorem held_finalized_c1
    (S : Setup V) (rho : NamedRun V) (core : NamedAdmissibleCore S rho)
    (m : Nat) (C : NamedBlock V) (hCrun : NamedRun.blockInRun S rho C)
    (hc1 : Clause1Idx S rho m C)
    (i : Nat) (v : V) (hv : v ∈ rho.honest) (hi : i ≤ m)
    (hbad : S.E.electorate.weightOf (Finset.univ \ rho.honest) < S.E.q)
    (D : NamedBlock V) (hD : D ∈ (NamedRun.stateBefore S rho i v).st.bodies) :
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
    obtain ⟨j, hj, received, hacc, hsend, hem⟩ :=
      NamedOutageProvenance.honest_held_ancestor_row_emission S rho
        core.toNamedUnforgeable i v hD hcarrier hrow ha
    obtain ⟨k, hk, hemit⟩ := hem
    have hjn : j < m := lt_of_lt_of_le hj hi
    have hkj : k ≤ j :=
      ViabilityHistory.row_emission_index_le_block_acceptance S rho core v carrier j
        received hacc a hrow ha k hk hemit hsend
    have hkn : k < m := lt_of_le_of_lt hkj hjn
    obtain ⟨H, K, hHscope, hHheld, hHhead, hKscope, hKheld, hKJ,
      hval, htime, hcreate, hheight, htarget, hhj, hJ, hhF, hroot, hKC⟩ :=
      hc1 k a.val_index ((S.node a.val_index).act a.round) a ha hk hemit hkn
        ⟨(derive_named S.E S.cfg D).h_F, F.root⟩ hp
    have hKF : K.root = F.root := hroot.symm
    have heq : K = F := core.root_injective C D hCrun hDscope
      K F (Or.inl hKC) (Or.inr hFD) hKF
    subst K
    exact ⟨F, hFD, hFE, hKC⟩

/-- Clause (3) of `LayerAHistoryIdx` at `m`, from clause (1) at `m`. -/
theorem clause3_of_clause1
    (S : Setup V) (rho : NamedRun V) (core : NamedAdmissibleCore S rho)
    (m : Nat) (C : NamedBlock V) (hCrun : NamedRun.blockInRun S rho C)
    (hc1 : Clause1Idx S rho m C)
    (hbad : S.E.electorate.weightOf (Finset.univ \ rho.honest) < S.E.q) :
    ∀ (i : Nat) (v : V), v ∈ rho.honest → i ≤ m →
      ∃ F : NamedBlock V,
        NamedRun.blockInRun S rho F ∧
        F ∈ (NamedRun.stateBefore S rho i v).st.bodies ∧
        F.erase = (NamedRun.stateBefore S rho i v).st.core.F ∧
        NamedBlock.Preceq F C := by
  intro i v hv hi
  obtain ⟨D, hD, hDF⟩ := FinalityCarrier.finality_carrier_stateBefore S rho i v
  obtain ⟨F, hFD, hFE, hFC⟩ := held_finalized_c1 S rho core m C hCrun hc1 i v hv hi hbad D hD
  have hpc := (Proofs.NamedRuntime.stateBefore_invariants S rho i v).1.1.1.2.2.1
  have hFbody := ViabilityHistoryTime.ancestor_body_mem hpc hD hFD
  exact ⟨F, Proofs.NamedRuntime.blockInRun_of_direct S rho
      (Proofs.NamedRuntime.directBlock_of_prefix S rho hv i hFbody),
    hFbody, hFE.trans hDF, hFC⟩

/-! ## The delivery step -/

set_option linter.unusedVariables false in
/-- Advancing the index-bounded joint history across a delivery. The witness
never has to grow: no honest emission clause gains an instance (event `n` is
not a tick), and clause (3)'s new prefix index `n + 1` is carried by
`clause3_of_clause1` from the clause-(1) bound the step already owns. -/
theorem jointHistoryIdx_step_deliver
    (S : Setup V) (rho : NamedRun V) (cap : Time)
    (core : NamedAdmissibleCore S rho)
    (healthy : NamedHealthyPrefixDelivery S rho cap)
    (committees : HonestCommittees S rho.honest) (hR : 3 ≤ S.hc.R)
    (hcap : cap ≤ rho.horizon)
    (windows : ∀ k, 0 < k → domain S.E S.hc k .g2 ≤ cap →
      AwakeWindowMajority S.E (fun v => (S.node v).awake) rho.honest S.hc.η_SG k)
    (hbad : S.E.electorate.weightOf (Finset.univ \ rho.honest) < S.E.q)
    (n : Nat) (C : NamedBlock V) (hhist : LayerAJointHistoryIdx S rho n C)
    (hcapn : ∀ i, i < n → ∀ e : NamedEvent V, rho.events[i]? = some e → e.time ≤ cap)
    (v : V) (o : NamedObject V) (t : Time)
    (hn : rho.events[n]? = some (.deliver v o t)) :
    LayerAJointHistoryIdx S rho (n + 1) C := by
  obtain ⟨⟨hCrun, h1, h2, h3⟩, h0, h4, hprov⟩ := hhist
  have hc1 : Clause1Idx S rho (n + 1) C := by
    intro i u ta a hu hi hem hlt fp hfp
    rcases (by omega : i < n ∨ i = n) with hlt' | rfl
    · exact h1 i u ta a hu hi hem hlt' fp hfp
    · exact absurd (hn.symm.trans hi) (by simp)
  refine ⟨⟨hCrun, hc1, ?_, clause3_of_clause1 S rho core (n + 1) C hCrun hc1 hbad⟩,
    ?_, ?_, witnessProvenanceIdx_mono S rho hprov (Nat.le_succ _)⟩
  · intro i u ta a hu hi hem hlt h T timeout hp
    rcases (by omega : i < n ∨ i = n) with hlt' | rfl
    · exact h2 i u ta a hu hi hem hlt' h T timeout hp
    · exact absurd (hn.symm.trans hi) (by simp)
  · intro i u ta a hu hi hem hlt key hkey
    rcases (by omega : i < n ∨ i = n) with hlt' | rfl
    · exact h0 i u ta a hu hi hem hlt' key hkey
    · exact absurd (hn.symm.trans hi) (by simp)
  · intro i u r hu hi hlt
    rcases (by omega : i < n ∨ i = n) with hlt' | rfl
    · exact h4 i u r hu hi hlt'
    · exact absurd (hn.symm.trans hi) (by simp)

/-! ## Producers for the acting tick -/

omit [DecidableEq V] [Fintype V] in
private theorem index_of_eq {α : Type} (l : List α) (hnd : l.Nodup) {i j : Nat} {e : α}
    (hi : l[i]? = some e) (hj : l[j]? = some e) : i = j :=
  (List.Nodup.getElem?_inj (List.getElem?_eq_some_iff.mp hi).1 hnd).mp (hi.trans hj.symm)

omit [DecidableEq V] [Fintype V] in
private theorem tick_eq {rho : NamedRun V} {i : Nat} {u v : V} {t t' : Time}
    (h1 : rho.events[i]? = some (.tick v t)) (h2 : rho.events[i]? = some (.tick u t')) :
    u = v ∧ t' = t := by
  have he := h1.symm.trans h2
  simp only [Option.some.injEq, NamedEvent.tick.injEq] at he
  exact ⟨he.1.symm, he.2.symm⟩

/-! ## A tick that is not an honest action -/

/-- A tick of a faulty node, or an honest tick at a non-action time, adds no
emission instance at all: every clause-(0)/(1)/(2) instance at the tick's own
index forces its row's emission time to be its actual action time, and clause (4)'s
forces the tick time to be the actual action time. -/
theorem jointHistoryIdx_step_tick_inert
    (S : Setup V) (rho : NamedRun V) (core : NamedAdmissibleCore S rho)
    (hbad : S.E.electorate.weightOf (Finset.univ \ rho.honest) < S.E.q)
    (n : Nat) (C : NamedBlock V) (hhist : LayerAJointHistoryIdx S rho n C)
    (v : V) (ta : Time) (hn : rho.events[n]? = some (.tick v ta))
    (hno : ∀ r : Round, ta = (S.node v).act r → v ∉ rho.honest) :
    LayerAJointHistoryIdx S rho (n + 1) C := by
  obtain ⟨⟨hCrun, h1, h2, h0'⟩, h0, h4, hprov⟩ := hhist
  have hrow : ∀ (u : V) (ta' : Time) (a : NamedAttestation V), u ∈ rho.honest →
      rho.events[n]? = some (.tick u ta') →
      NamedObject.attest a ∈ NamedRun.emittedAt S rho n u ta' → False := by
    intro u ta' a hu hi hem
    obtain ⟨rfl, rfl⟩ := tick_eq hn hi
    obtain ⟨-, ht, -, -⟩ := emitted_row_at_index S rho core n u ta' a hi hem
    exact hno a.round ht hu
  have hc1 : Clause1Idx S rho (n + 1) C := by
    intro i u ta' a hu hi hem hlt fp hfp
    rcases (by omega : i < n ∨ i = n) with hlt' | rfl
    · exact h1 i u ta' a hu hi hem hlt' fp hfp
    · exact absurd (hrow u ta' a hu hi hem) not_false
  refine ⟨⟨hCrun, hc1, ?_, clause3_of_clause1 S rho core (n + 1) C hCrun hc1 hbad⟩,
    ?_, ?_, witnessProvenanceIdx_mono S rho hprov (Nat.le_succ _)⟩
  · intro i u ta' a hu hi hem hlt h T timeout hp
    rcases (by omega : i < n ∨ i = n) with hlt' | rfl
    · exact h2 i u ta' a hu hi hem hlt' h T timeout hp
    · exact absurd (hrow u ta' a hu hi hem) not_false
  · intro i u ta' a hu hi hem hlt key hkey
    rcases (by omega : i < n ∨ i = n) with hlt' | rfl
    · exact h0 i u ta' a hu hi hem hlt' key hkey
    · exact absurd (hrow u ta' a hu hi hem) not_false
  · intro i u r hu hi hlt
    rcases (by omega : i < n ∨ i = n) with hlt' | rfl
    · exact h4 i u r hu hi hlt'
    · obtain ⟨rfl, hta⟩ := tick_eq hn hi
      exact absurd hu (hno r hta.symm)

/-! ## Clause (2) at the acting tick -/

theorem clause2_at_action_tick
    (S : Setup V) (rho : NamedRun V) (core : NamedAdmissibleCore S rho)
    (n : Nat) (C : NamedBlock V)
    (hgraded : JointHistoryGaps.GradedRootOnHistoryIdx S rho n C)
    (hconf4 : JointHistoryGaps.ConfirmationAtTick S rho n C)
    (v : V) (hv : v ∈ rho.honest) (ta : Time)
    (hn : rho.events[n]? = some (.tick v ta))
    (a : NamedAttestation V)
    (hem : NamedObject.attest a ∈ NamedRun.emittedAt S rho n v ta)
    (h : Height) (T : BlockId) (timeout : Bool)
    (hp : a.height_pair = .vote h T timeout) :
    let m := NamedActionReads.windowActionReadFrom S v (NamedRun.stateBefore S rho n v) a.round
    let gc := NamedProfile.gradeContract m.cache
    let input := Protocol.NamedActions.creatorInput
      (Protocol.attestation_input_with gc S.E S.hc (S.node v) m.st.core.toHealing)
    ∃ source entry : NamedBlock V,
      NamedRun.blockInRun S rho source ∧ source ∈ m.st.bodies ∧
      NamedRun.blockInRun S rho entry ∧ entry ∈ m.st.bodies ∧
      a.val_index = v ∧ ta = (S.node v).act a.round ∧
      a = (Protocol.NamedRecord.create m.record input).2 ∧
      Protocol.fg_source_with gc S.E S.hc m.st.core.toHealing a.round
        (Protocol.grade2_block_with gc S.E S.hc m.st.core.toHealing a.round) =
          some source.erase ∧
      input.fields = some ((m.st.core.σ source.erase).h,
        (m.st.core.σ source.erase).T_h.root, (m.st.core.σ source.erase).nj) ∧
      h = (m.st.core.σ source.erase).h ∧
      T = (m.st.core.σ source.erase).T_h.root ∧
      entry.erase = (m.st.core.σ source.erase).T_h ∧
      NamedBlock.Preceq entry source ∧
      (Protocol.derive_named S.E S.cfg entry).h =
        (Protocol.derive_named S.E S.cfg source).h ∧
      entry.root = T ∧ NamedBlock.Preceq entry C := by
  obtain ⟨hval, ht, hr, hcreate⟩ := emitted_row_at_index S rho core n v ta a hn hem
  subst hval
  subst ht
  intro m gc input
  have hemits : NamedRun.emits S rho a.val_index (.attest a) ((S.node a.val_index).act a.round) := ⟨n, hn, hem⟩
  obtain ⟨i', source, entry, hs, hheight, hrootT⟩ :=
    Proofs.NamedWindowIntrinsicEntry.emitted_height_signed_source S rho hemits hp
  have hi' : i' = n := index_of_eq rho.events core.nodup hs.1 hn
  have hs' : Internal.NamedJointOutage.WindowSignedSourceAt S rho n a source entry := hi' ▸ hs
  have hsourceC : NamedBlock.Preceq source C :=
    JointHistoryGaps.fg_source_on_history_of S rho core n C n hconf4 (le_refl n)
      hgraded a source entry hv hs'
  have hpost := (NamedWindowIntrinsicEntry.signed_source_post_projection S rho hs').1
  obtain ⟨hstick, hsem, hsrow, hsbody, hssel, hsanc, hserase, hsheight, timeout', hsp⟩ := hs'
  have hsbody' : source ∈ (NamedRun.stateBefore S rho (n + 1) a.val_index).st.bodies := by
    rw [hpost]; exact hsbody
  have hsourceRun := Proofs.NamedRuntime.blockInRun_of_direct S rho
    (Proofs.NamedRuntime.directBlock_of_prefix S rho hv (n + 1) hsbody')
  have hentryRun := Proofs.NamedRuntime.blockInRun_of_ancestor S rho hsourceRun hsanc
  have hinv := WindowAction.windowRead_invariant S a.val_index
    (NamedRun.stateBefore S rho n a.val_index) ((S.node a.val_index).act a.round)
    (Proofs.NamedRuntime.stateBefore_invariants S rho n a.val_index).1
  have hpc := hinv.1.1.2.2.1
  have hentryBody : entry ∈ m.st.bodies :=
    ViabilityHistoryTime.ancestor_body_mem hpc hsbody hsanc
  have hco := hinv.1.1
  have hsigma : m.st.core.σ source.erase = Protocol.derive_named S.E S.cfg source :=
    hco.2.2.2.2 source hsbody
  have hfields : input.fields =
      (Protocol.fg_source_with gc S.E S.hc m.st.core.toHealing a.round
        (Protocol.grade2_block_with gc S.E S.hc m.st.core.toHealing a.round)).map
        (fun q => ((m.st.core.σ q).h, (m.st.core.σ q).T_h.root, (m.st.core.σ q).nj)) := by
    rw [hr]; rfl
  have hfields2 : input.fields = some ((m.st.core.σ source.erase).h,
      (m.st.core.σ source.erase).T_h.root, (m.st.core.σ source.erase).nj) := by
    rw [hfields, hssel]; rfl
  refine ⟨source, entry, hsourceRun, hsbody, hentryRun, hentryBody, rfl, rfl, hcreate,
    hssel, hfields2, ?_, ?_, ?_, hsanc, hsheight, hrootT,
    named_preceq_trans hsanc hsourceC⟩
  · rw [hsigma]; exact hheight.symm
  · rw [hsigma, ← hserase, Proofs.NamedWire.erase_root]; exact hrootT.symm
  · rw [hsigma]; exact hserase

/-- The clause-(0) instance of the acting tick: the row's own `confirmed`
key is the SG selector's key at the same action read, so
`sg_vote_on_history`'s block `K0` names it. -/
theorem clause0_at_action_tick
    (S : Setup V) (rho : NamedRun V) (core : NamedAdmissibleCore S rho)
    (n : Nat) (C' : NamedBlock V)
    (v : V) (r : Round) (hn : rho.events[n]? = some (.tick v ((S.node v).act r)))
    (K0 : NamedBlock V) (hK0run : NamedRun.blockInRun S rho K0)
    (hK0body : K0 ∈ (NamedActionReads.windowActionReadFrom S v (NamedRun.stateBefore S rho n v) r).st.bodies)
    (hK0e : K0.erase = Protocol.get_sg_vote_with
      (NamedProfile.gradeContract (NamedActionReads.windowActionReadFrom S v (NamedRun.stateBefore S rho n v) r).cache)
      S.E S.hc (NamedActionReads.windowActionReadFrom S v (NamedRun.stateBefore S rho n v) r).st.core.toHealing r
      (Protocol.grade2_block_with
        (NamedProfile.gradeContract (NamedActionReads.windowActionReadFrom S v (NamedRun.stateBefore S rho n v) r).cache)
        S.E S.hc (NamedActionReads.windowActionReadFrom S v (NamedRun.stateBefore S rho n v) r).st.core.toHealing r))
    (hK0C : NamedBlock.Preceq K0 C')
    (a : NamedAttestation V)
    (hem : NamedObject.attest a ∈ NamedRun.emittedAt S rho n v ((S.node v).act r))
    (key : BlockId) (hkey : a.confirmed = some key) :
    let m := NamedActionReads.windowActionReadFrom S v (NamedRun.stateBefore S rho n v) a.round
    ∃ K : NamedBlock V, NamedRun.blockInRun S rho K ∧ K ∈ m.st.bodies ∧
      K.root = key ∧ NamedBlock.Preceq K C' := by
  intro m
  obtain ⟨hval, ht, hrr, hcreate⟩ := emitted_row_at_index S rho core n v ((S.node v).act r) a hn hem
  have hround : r = a.round := by
    have ha := S.act_round v a.round
    rw [← ht] at ha
    exact (S.act_round v r).symm.trans ha
  rw [hround] at hK0body hK0e
  have hkeyeq := confirmed_key_at_action_tick S rho core n v ((S.node v).act r) hn a hem key hkey
  exact ⟨K0, hK0run, hK0body, by rw [hkeyeq, ← hK0e, Proofs.NamedWire.erase_root], hK0C⟩

/-! ## The tick step -/


#print axioms emitted_row_at_index
#print axioms action_head_body
#print axioms clause0_at_action_tick
#print axioms confirmed_key_at_action_tick
#print axioms clause2_at_action_tick
#print axioms clause1_at_action_tick
#print axioms jointHistoryIdx_step_tick_inert
#print axioms held_finalized_c1
#print axioms clause3_of_clause1
#print axioms jointHistoryIdx_step_deliver
end DecoupledConsensusModel.Proofs.NamedOutageHistory.IdxDriverSteps

end
