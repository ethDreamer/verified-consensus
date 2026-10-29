module
public import DecoupledConsensusProofs.Protocol.Duties.Inputs.WindowIntrinsicEntry
public import DecoupledConsensusProofs.Protocol.ValidatorClient.RecordClean

/-!
# Finality fields at actual attestation inputs

The finality pair reads the Goldfish head after preceding same-tick duties.
Its named witness is retained in the post-event inventory, including when
that head is a newly proposed body (PROTOCOL.md `sec:public-handlers`).
-/
@[expose] public section
namespace DecoupledConsensusModel.Proofs.NamedWindowFinalitySources
open Execution Protocol NamedActionReads
variable {V : Type} [DecidableEq V] [Fintype V]

/-- A nonempty finality pair names the justification fields of a retained
body in the supplied attestation input (PROTOCOL.md `sec:public-handlers`). -/
theorem finality_body_at_input (S : Setup V) (v : V) (n : NamedNodeState V)
    (hinv : NamedConfirmationMembership.Invariant S.E S.cfg n.st)
    {H : Height} {T : BlockId}
    (hpair : (NamedDuties.attest_with (NamedProfile.gradeContract n.cache)
      S.E S.hc (S.node v) n.st n.record).2.2.finality_pair = some ⟨H, T⟩) :
    ∃ D : NamedBlock V, D ∈ n.st.bodies ∧
      (derive_named S.E S.cfg D).h_j = H ∧ (derive_named S.E S.cfg D).J.root = T := by
  obtain ⟨head, hhead, heq⟩ := round_action_finality_pair
    (NamedProfile.gradeContract n.cache) S.E S.hc (S.node v) n.st.core.toHealing n.record
  simp only [Store.toHealing] at heq
  have hp : finality_pair n.record.legacy (n.st.core.σ head).h_j
      (n.st.core.σ head).J.root (n.st.core.σ head).h_F = some ⟨H, T⟩ := by
    rw [← heq]
    exact hpair
  have hh : (n.st.core.σ head).h_j = H := finality_pair_height hp
  have ht : (n.st.core.σ head).J.root = T := by
    unfold finality_pair at hp
    split_ifs at hp
    exact congrArg FinalityPair.target (Option.some.inj hp)
  have hmem : head ∈ n.st.core.T := by
    rw [hhead]
    apply NamedProposalParent.runtime_get_head_mem n.cache S.E S.hc n.st.core.toHealing
    exact NamedStoreRoots.fg_root_mem n.st hinv.1.2
  rw [hinv.1.1.1] at hmem
  obtain ⟨D, hD, he⟩ := Finset.mem_image.mp hmem
  have hsigma : n.st.core.σ head = derive_named S.E S.cfg D := by
    rw [← he]
    exact hinv.1.1.2.2.2.2 D hD
  exact ⟨D, hD, by simpa only [hsigma] using hh, by simpa only [hsigma] using ht⟩

/-- A finality field emitted at event `i` has its body in the post-tick store.
No paper-time identification is needed (PROTOCOL.md `sec:public-handlers`). -/
theorem emitted_finality_body (S : Setup V) (rho : NamedRun V)
    {i : Nat} {v : V} {t : Time} {a : NamedAttestation V} {H : Height} {T : BlockId}
    (hi : rho.events[i]? = some (.tick v t))
    (hem : NamedObject.attest a ∈ NamedRun.emittedAt S rho i v t)
    (hp : a.finality_pair = some ⟨H, T⟩) :
    ∃ D : NamedBlock V, D ∈ (NamedRun.stateBefore S rho (i + 1) v).st.bodies ∧
      (derive_named S.E S.cfg D).h_j = H ∧ (derive_named S.E S.cfg D).J.root = T := by
  obtain ⟨ht, hawake, hval⟩ := WindowAction.run_emission_fields S
    (show NamedRun.emits S rho v (.attest a) t from ⟨i, hi, hem⟩)
  subst t
  have hrow := ((WindowAction.attestation_mem_at_action S v
    (NamedRun.stateBefore S rho i v) a.round a).mp hem).2
  let n := windowActionReadFrom S v (NamedRun.stateBefore S rho i v) a.round
  have hinv := WindowAction.windowRead_invariant S v (NamedRun.stateBefore S rho i v)
    ((S.node v).act a.round) (NamedRuntime.stateBefore_invariants S rho i v).1
  have hp' : (NamedDuties.attest_with (NamedProfile.gradeContract n.cache)
      S.E S.hc (S.node v) n.st n.record).2.2.finality_pair = some ⟨H, T⟩ := by
    rw [hrow] at hp
    exact hp
  obtain ⟨D, hD, hh, ht⟩ := finality_body_at_input S v n hinv hp'
  refine ⟨D, ?_, hh, ht⟩
  rw [NamedRuntime.stateBefore_tick S rho hi,
    WindowAction.tick_store_at_action S v _ a.round hawake]
  simpa only [NamedDuties.attest_with, NamedAdmission.admit_row_bodies] using hD

#print axioms finality_body_at_input
#print axioms emitted_finality_body
end DecoupledConsensusModel.Proofs.NamedWindowFinalitySources
