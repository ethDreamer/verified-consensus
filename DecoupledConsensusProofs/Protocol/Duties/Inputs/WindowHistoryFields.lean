module
public import DecoupledConsensusProofs.Execution.HeldJustificationHistoryIdx
public import DecoupledConsensusProofs.Protocol.Duties.Inputs.WindowIntrinsicEntry
public import DecoupledConsensusProofs.Protocol.Grades.JointHistoryProducers

/-!
# Actual emission fields for the event history

The finality head is held after the emission tick. Its justification uses
strictly earlier certificate rows, including when a proposal shares that tick.
These fields feed the event-indexed renewal (PROTOCOL.md `sec:healing-schedule`).
-/
@[expose] public section
namespace DecoupledConsensusModel.Proofs.NamedWindowHistoryFields
open Execution Internal.NamedOutageEntry Protocol
open Internal.NamedOutageEntry.History Proofs.NamedOutageHistory
variable {V : Type} [DecidableEq V] [Fintype V]

/-- Clause (1) of `LayerAHistoryIdx`, verbatim. Definitionally the second
component of `LayerAHistoryIdx S rho m C`. -/
def Clause1Idx (S : Setup V) (rho : NamedRun V) (m : Nat) (C : NamedBlock V) : Prop :=
  ∀ (i : Nat) (v : V) (ta : Time) (a : NamedAttestation V),
    v ∈ rho.honest → rho.events[i]? = some (.tick v ta) →
    NamedObject.attest a ∈ NamedRun.emittedAt S rho i v ta → i < m →
    ∀ fp : FinalityPair, a.finality_pair = some fp →
      let n := NamedActionReads.windowActionReadFrom S v (NamedRun.stateBefore S rho i v) a.round
      let gc := NamedProfile.gradeContract n.cache
      let input := Protocol.NamedActions.creatorInput
        (Protocol.attestation_input_with gc S.E S.hc (S.node v) n.st.core.toHealing)
      let st := n.st.core.toHealing
      let head := Protocol.get_head_with gc S.E S.hc st (st.pool st.s)
        ((st.pool st.s).filter (fun u => Protocol.resolved st.T u = true)) st.s
      ∃ H K : NamedBlock V,
        NamedRun.blockInRun S rho H ∧ H ∈ n.st.bodies ∧ H.erase = head ∧
        NamedRun.blockInRun S rho K ∧ K ∈ n.st.bodies ∧
        K.erase = (n.st.core.σ H.erase).J ∧
        a.val_index = v ∧ ta = (S.node v).act a.round ∧
        a = (Protocol.NamedRecord.create n.record input).2 ∧
        fp.height = input.h_j ∧ fp.target = input.J ∧
        input.h_j = (n.st.core.σ H.erase).h_j ∧
        input.J = (n.st.core.σ H.erase).J.root ∧
        input.h_F = (n.st.core.σ H.erase).h_F ∧
        fp.target = K.root ∧ NamedBlock.Preceq K C


omit [DecidableEq V] [Fintype V] in
private theorem index_of_eq {α : Type} (l : List α) (hnd : l.Nodup) {i j : Nat} {e : α}
    (hi : l[i]? = some e) (hj : l[j]? = some e) : i = j :=
  (List.Nodup.getElem?_inj (List.getElem?_eq_some_iff.mp hi).1 hnd).mp (hi.trans hj.symm)

omit [DecidableEq V] [Fintype V] in
private theorem finality_pair_fields (L : Protocol.Record) (h_j : Height) (J : BlockId)
    (h_F : Height) {fp : FinalityPair}
    (h : Protocol.finality_pair L h_j J h_F = some fp) :
    fp.height = h_j ∧ fp.target = J := by
  unfold Protocol.finality_pair at h
  split_ifs at h
  · have he : (⟨h_j, J⟩ : FinalityPair) = fp := Option.some.inj h
    exact ⟨by rw [← he], by rw [← he]⟩

/-- The emitted row at the tick's OWN event index: its author, its action
time, its round, and its exact `NamedRecord.create` shape. The emission-stage theorem returns a tick index; the
run's `Nodup` pins it to `i`. -/
theorem emitted_row_at_index (S : Setup V) (rho : NamedRun V)
    (core : NamedAdmissibleCore S rho) (i : Nat) (v : V) (ta : Time)
    (a : NamedAttestation V)
    (hi : rho.events[i]? = some (.tick v ta))
    (hem : NamedObject.attest a ∈ NamedRun.emittedAt S rho i v ta) :
    let n := NamedActionReads.windowActionReadFrom S v (NamedRun.stateBefore S rho i v) a.round
    let gc := NamedProfile.gradeContract n.cache
    let input := Protocol.NamedActions.creatorInput
      (Protocol.attestation_input_with gc S.E S.hc (S.node v) n.st.core.toHealing)
    a.val_index = v ∧ ta = (S.node v).act a.round ∧
      a.round = S.hc.round_of n.st.core.s ∧
      a = (Protocol.NamedRecord.create n.record input).2 := by
  have hemits : NamedRun.emits S rho v (.attest a) ta := ⟨i, hi, hem⟩
  obtain ⟨j, hj, ho, hrow, hval, hr, ht, hawake⟩ :=
    Proofs.NamedOutageInputs.emitted_attestation_stages S rho hemits
  have hji : j = i := index_of_eq rho.events core.nodup hj hi
  subst hji
  exact ⟨hval, ht, hr, hrow.symm⟩

/-- The Goldfish head the action read's attestation input reads is a retained
named body. -/
theorem action_head_body (S : Setup V) (rho : NamedRun V) (i : Nat) (v : V) (r : Round) :
    let n := NamedActionReads.windowActionReadFrom S v (NamedRun.stateBefore S rho i v) r
    let gc := NamedProfile.gradeContract n.cache
    let st := n.st.core.toHealing
    ∃ H : NamedBlock V, H ∈ n.st.bodies ∧
      H.erase = Protocol.get_head_with gc S.E S.hc st (st.pool st.s)
        ((st.pool st.s).filter (fun u => Protocol.resolved st.T u = true)) st.s := by
  intro n gc st
  have hinv := WindowAction.windowRead_invariant S v
    (NamedRun.stateBefore S rho i v) ((S.node v).act r)
    (Proofs.NamedRuntime.stateBefore_invariants S rho i v).1
  have hroot := Proofs.NamedStoreRoots.fg_root_mem n.st hinv.1.2
  have hanchor := Proofs.NamedConfirmationMembership.runtime_anchor_mem n.cache S.E S.hc
    st (S.hc.round_of st.s) hroot
  have hmem : Protocol.get_head_with gc S.E S.hc st (st.pool st.s)
      ((st.pool st.s).filter (fun u => Protocol.resolved st.T u = true)) st.s ∈ st.T :=
    NamedProposalParent.get_head_with_mem gc S.E S.hc st _ _ st.s hanchor
  have htree : n.st.core.T = n.st.bodies.image NamedBlock.erase := hinv.1.1.1
  have hmem' : Protocol.get_head_with gc S.E S.hc st (st.pool st.s)
      ((st.pool st.s).filter (fun u => Protocol.resolved st.T u = true)) st.s ∈
      n.st.bodies.image NamedBlock.erase := by rw [← htree]; exact hmem
  obtain ⟨H, hH, he⟩ := Finset.mem_image.mp hmem'
  exact ⟨H, hH, he⟩

/-- The clause-(1) instance of the tick that is itself event `n`. The head
`H` is the action read's own Goldfish head, and its justification checkpoint
`K` is placed on the history chain by `causal_justification_checkpoint_on_history` at the emission index.
The post-tick head uses certificate rows strictly before that index; no
current-emission history is consumed (PROTOCOL.md `sec:healing-schedule`). -/
theorem clause1_at_action_tick
    (S : Setup V) (rho : NamedRun V) (core : NamedAdmissibleCore S rho)
    (hbad : S.E.electorate.weightOf (Finset.univ \ rho.honest) < S.E.q)
    (n : Nat) (C : NamedBlock V) (hhist : LayerAHistoryIdx S rho n C)
    (v : V) (hv : v ∈ rho.honest) (ta : Time)
    (hn : rho.events[n]? = some (.tick v ta))
    (a : NamedAttestation V)
    (hem : NamedObject.attest a ∈ NamedRun.emittedAt S rho n v ta)
    (fp : FinalityPair) (hfp : a.finality_pair = some fp) :
    let m := NamedActionReads.windowActionReadFrom S v (NamedRun.stateBefore S rho n v) a.round
    let gc := NamedProfile.gradeContract m.cache
    let input := Protocol.NamedActions.creatorInput
      (Protocol.attestation_input_with gc S.E S.hc (S.node v) m.st.core.toHealing)
    let st := m.st.core.toHealing
    let head := Protocol.get_head_with gc S.E S.hc st (st.pool st.s)
      ((st.pool st.s).filter (fun u => Protocol.resolved st.T u = true)) st.s
    ∃ H K : NamedBlock V,
      NamedRun.blockInRun S rho H ∧ H ∈ m.st.bodies ∧ H.erase = head ∧
      NamedRun.blockInRun S rho K ∧ K ∈ m.st.bodies ∧
      K.erase = (m.st.core.σ H.erase).J ∧
      a.val_index = v ∧ ta = (S.node v).act a.round ∧
      a = (Protocol.NamedRecord.create m.record input).2 ∧
      fp.height = input.h_j ∧ fp.target = input.J ∧
      input.h_j = (m.st.core.σ H.erase).h_j ∧
      input.J = (m.st.core.σ H.erase).J.root ∧
      input.h_F = (m.st.core.σ H.erase).h_F ∧
      fp.target = K.root ∧ NamedBlock.Preceq K C := by
  intro m gc input st head
  obtain ⟨hval, ht, hr, hcreate⟩ := emitted_row_at_index S rho core n v ta a hn hem
  obtain ⟨H, hHbody, hHhead⟩ := action_head_body S rho n v a.round
  have hfields := WindowAction.run_emission_fields S ⟨n, hn, hem⟩
  have hpost : (NamedRun.stateBefore S rho (n + 1) v).st.bodies = m.st.bodies := by
    have hv' := hfields.2.2
    subst v
    have ht' := hfields.1
    subst ta
    exact (NamedWindowIntrinsicEntry.emission_post_projection S rho hn hem).1
  have hHbody' : H ∈ (NamedRun.stateBefore S rho (n + 1) v).st.bodies := by
    rw [hpost]
    exact hHbody
  have hHrun := Proofs.NamedRuntime.blockInRun_of_direct S rho
    (Proofs.NamedRuntime.directBlock_of_prefix S rho hv (n + 1) hHbody')
  have hcausal := NamedCausalCarrierHistory.held_carrier_rows_before S rho core n v hHbody'
  obtain ⟨K, hKrun, hKpost, hKH, hKE, hKC, -, -⟩ :=
    GuardProofs.causal_justification_checkpoint_on_history S rho core n C hhist
      (n + 1) v hv hbad H hHbody' hcausal
  have hKbody : K ∈ m.st.bodies := by rw [← hpost]; exact hKpost
  have hco := (WindowAction.windowRead_invariant S v (NamedRun.stateBefore S rho n v)
    ((S.node v).act a.round) (Proofs.NamedRuntime.stateBefore_invariants S rho n v).1).1.1
  have hsigma : m.st.core.σ H.erase = derive_named S.E S.cfg H := hco.2.2.2.2 H hHbody
  have hfppair : Protocol.finality_pair m.record.legacy input.h_j input.J input.h_F
      = some fp := by rw [hcreate] at hfp; exact hfp
  obtain ⟨hfph, hfpt⟩ := finality_pair_fields _ _ _ _ hfppair
  have hKEsigma : K.erase = (m.st.core.σ H.erase).J := by rw [hsigma]; exact hKE
  have hhj : input.h_j = (m.st.core.σ H.erase).h_j := by rw [hHhead]; rfl
  have hJ : input.J = (m.st.core.σ H.erase).J.root := by rw [hHhead]; rfl
  have hhF : input.h_F = (m.st.core.σ H.erase).h_F := by rw [hHhead]; rfl
  have hKroot : fp.target = K.root := by
    rw [hfpt, hJ, ← hKEsigma, Proofs.NamedWire.erase_root]
  exact ⟨H, K, hHrun, hHbody, hHhead, hKrun, hKbody, hKEsigma, hval, ht, hcreate,
    hfph, hfpt, hhj, hJ, hhF, hKroot, hKC⟩

/-! ## Clause (0) at the acting tick: the row's SG key IS the selector's key -/

theorem confirmed_key_at_action_tick
    (S : Setup V) (rho : NamedRun V) (core : NamedAdmissibleCore S rho)
    (n : Nat) (v : V) (ta : Time) (hn : rho.events[n]? = some (.tick v ta))
    (a : NamedAttestation V)
    (hem : NamedObject.attest a ∈ NamedRun.emittedAt S rho n v ta)
    (key : BlockId) (hkey : a.confirmed = some key) :
    let m := NamedActionReads.windowActionReadFrom S v (NamedRun.stateBefore S rho n v) a.round
    let gc := NamedProfile.gradeContract m.cache
    key = (Protocol.get_sg_vote_with gc S.E S.hc m.st.core.toHealing a.round
      (Protocol.grade2_block_with gc S.E S.hc m.st.core.toHealing a.round)).root := by
  intro m gc
  obtain ⟨hval, ht, hr, hcreate⟩ := emitted_row_at_index S rho core n v ta a hn hem
  have hconf : a.confirmed = some (Protocol.get_sg_vote_with gc S.E S.hc m.st.core.toHealing
      (S.hc.round_of m.st.core.s)
      (Protocol.grade2_block_with gc S.E S.hc m.st.core.toHealing
        (S.hc.round_of m.st.core.s))).root := by rw [hcreate]; rfl
  rw [hkey, ← hr] at hconf
  exact Option.some.inj hconf


/-- At the point schedule, the finality emission fields recover the original
input observer and time equation (PROTOCOL.md `sec:healing-schedule`). -/
theorem clause1_at_action_tick_point
    (S : Setup V) (rho : NamedRun V) (core : NamedAdmissibleCore S rho)
    (hpoint : ∀ v r, (S.node v).act r = S.a r)
    (hbad : S.E.electorate.weightOf (Finset.univ \ rho.honest) < S.E.q)
    (n : Nat) (C : NamedBlock V) (hhist : LayerAHistoryIdx S rho n C)
    (v : V) (hv : v ∈ rho.honest) (ta : Time)
    (hn : rho.events[n]? = some (.tick v ta))
    (a : NamedAttestation V)
    (hem : NamedObject.attest a ∈ NamedRun.emittedAt S rho n v ta)
    (fp : FinalityPair) (hfp : a.finality_pair = some fp) :
    let m := actionReadFrom S (NamedRun.stateBefore S rho n v) a.round
    let gc := NamedProfile.gradeContract m.cache
    let input := Protocol.NamedActions.creatorInput
      (Protocol.attestation_input_with gc S.E S.hc (S.node v) m.st.core.toHealing)
    let st := m.st.core.toHealing
    let head := Protocol.get_head_with gc S.E S.hc st (st.pool st.s)
      ((st.pool st.s).filter (fun u => Protocol.resolved st.T u = true)) st.s
    ∃ H K : NamedBlock V,
      NamedRun.blockInRun S rho H ∧ H ∈ m.st.bodies ∧ H.erase = head ∧
      NamedRun.blockInRun S rho K ∧ K ∈ m.st.bodies ∧
      K.erase = (m.st.core.σ H.erase).J ∧
      a.val_index = v ∧ ta = S.a a.round ∧
      a = (Protocol.NamedRecord.create m.record input).2 ∧
      fp.height = input.h_j ∧ fp.target = input.J ∧
      input.h_j = (m.st.core.σ H.erase).h_j ∧
      input.J = (m.st.core.σ H.erase).J.root ∧
      input.h_F = (m.st.core.σ H.erase).h_F ∧
      fp.target = K.root ∧ NamedBlock.Preceq K C := by
  have h := clause1_at_action_tick S rho core hbad n C hhist v hv ta hn a hem fp hfp
  simpa only [NamedActionReads.windowActionReadFrom, hpoint,
    WindowAction.windowReadFrom_point, actionReadFrom] using! h

#print axioms clause1_at_action_tick_point
#print axioms emitted_row_at_index
#print axioms action_head_body
#print axioms clause1_at_action_tick
#print axioms confirmed_key_at_action_tick
end DecoupledConsensusModel.Proofs.NamedWindowHistoryFields
