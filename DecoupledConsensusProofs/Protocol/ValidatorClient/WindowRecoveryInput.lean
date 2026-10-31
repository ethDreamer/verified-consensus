module
public import DecoupledConsensusProofs.Protocol.ValidatorClient.RecoveryBoundary
public import DecoupledConsensusProofs.Execution.FGSelectorWitness
public import DecoupledConsensusProofs.Protocol.Duties.Inputs.WindowFinalitySources

/-!
# Recovery fields at actual action inputs

An honest-store cap through an action event bounds every body in its input,
including a proposal processed earlier in that tick. The input's source and
finality head then obey the recovery-height NJ universe. These facts supply
the record induction without a paper-time identification
(PROTOCOL.md `sec:public-handlers`).
-/
@[expose] public section
namespace DecoupledConsensusModel.Proofs.WindowRecoveryInput
open Protocol Execution Internal HealingSurface NamedActionReads
variable {V : Type} [DecidableEq V] [Fintype V]

/-- The cap at a later prefix includes the input of every earlier action
event, by post-event body retention (PROTOCOL.md `sec:public-handlers`). -/
theorem input_universe (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {stop i : Nat} {hF0 blocked : Height}
    (hcap : HonestPrefixFinalityCap S rho stop hF0)
    (hrec : NjGap.RecoveryHeight S.cfg hF0 blocked) (hiStop : i < stop)
    {v : V} (hv : v ∈ rho.honest) {r : Round}
    (hi : rho.events[i]? = some (.tick v ((S.node v).act r))) :
    ∀ D ∈ (windowActionReadAt S rho v r).st.bodies,
      ((derive_named S.E S.cfg D).h = blocked →
        (derive_named S.E S.cfg D).nj = true) ∧
      (derive_named S.E S.cfg D).h_j ≠ blocked := by
  have hcapPost := honestPrefixFinalityCap_of_le S
    adm.toNamedScheduleWellFormed (Nat.succ_le_of_lt hiStop) hcap
  have hu := honestPrefixNJUniverse_of_finalityCap S
    adm.toNamedDeliveryWellFormed hcapPost hrec
  have hpre := NamedRuntime.tick_prefix_eq_strict S rho
    adm.toNamedScheduleWellFormed.sorted adm.toNamedScheduleWellFormed.nodup hi
  intro D hD
  apply hu v hv D
  change D ∈ (NamedRun.stateBefore S rho (i + 1) v).st.bodies
  rw [NamedRuntime.stateBefore_tick S rho hi,
    (WindowAction.tick_input_projection S v _ r).1, hpre]
  exact hD

/-- A finality row emitted inside the capped prefix cannot name the
recovery height (PROTOCOL.md `sec:public-handlers`). -/
theorem finality_height_ne (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {stop i : Nat} {hF0 blocked : Height}
    (hcap : HonestPrefixFinalityCap S rho stop hF0)
    (hrec : NjGap.RecoveryHeight S.cfg hF0 blocked) (hiStop : i < stop)
    {v : V} (hv : v ∈ rho.honest) {t : Time} {a : NamedAttestation V}
    (hi : rho.events[i]? = some (.tick v t))
    (ho : NamedObject.attest a ∈ NamedRun.emittedAt S rho i v t)
    {T : BlockId} (hp : a.finality_pair = some ⟨blocked, T⟩) : False := by
  obtain ⟨D, hD, hh, _⟩ :=
    NamedWindowFinalitySources.emitted_finality_body S rho hi ho hp
  have hcapPost := honestPrefixFinalityCap_of_le S
    adm.toNamedScheduleWellFormed (Nat.succ_le_of_lt hiStop) hcap
  exact (honestPrefixNJUniverse_of_finalityCap S
    adm.toNamedDeliveryWellFormed hcapPost hrec v hv D hD).2 hh

/-- Recovery-height inputs with a fresh record choose a timeout. The source
and the Goldfish head may differ (PROTOCOL.md `sec:public-handlers`). -/
theorem timeout_of_fresh_input (S : Setup V) (v : V) (n : NamedNodeState V)
    (hinv : NamedConfirmationMembership.Invariant S.E S.cfg n.st) {blocked : Height}
    (hu : ∀ D ∈ n.st.bodies,
      ((derive_named S.E S.cfg D).h = blocked →
        (derive_named S.E S.cfg D).nj = true) ∧
      (derive_named S.E S.cfg D).h_j ≠ blocked)
    {D : NamedBlock V} (hD : D ∈ n.st.bodies)
    (hsource : actionFGSource S n = some D.erase)
    (hh : (n.st.core.σ D.erase).h = blocked)
    (hfresh : RecordFreshAt n.record.legacy blocked) :
    (NamedActions.round_action_with (NamedProfile.gradeContract n.cache)
      S.E S.hc (S.node v) n.st.core.toHealing n.record).2.height_pair =
      NamedHeightPair.vote blocked (n.st.core.σ D.erase).T_h.root true := by
  have hd : n.st.core.σ D.erase = derive_named S.E S.cfg D :=
    hinv.1.1.2.2.2.2 D hD
  have hnj : (n.st.core.σ D.erase).nj = true := by
    rw [hd]
    exact (hu D hD).1 (hd ▸ hh)
  have hhead : actionHeadWith (NamedProfile.gradeContract n.cache)
      S.E S.hc n.st.core.toHealing ∈ n.st.core.T := by
    apply NamedProposalParent.runtime_get_head_mem n.cache S.E S.hc n.st.core.toHealing
    exact NamedStoreRoots.fg_root_mem n.st hinv.1.2
  rw [hinv.1.1.1] at hhead
  obtain ⟨H, hH, he⟩ := Finset.mem_image.mp hhead
  have hheadj : (n.st.core.σ (actionHeadWith (NamedProfile.gradeContract n.cache)
      S.E S.hc n.st.core.toHealing)).h_j ≠ blocked := by
    rw [← he, hinv.1.1.2.2.2.2 H hH]
    exact (hu H hH).2
  exact round_action_height_pair_timeout_of_fresh_source
    (NamedProfile.gradeContract n.cache) S.E S.hc (S.node v)
    n.st.core.toHealing n.record hsource hh hnj hfresh hheadj

/-- A fresh target cannot be introduced by an action inside the capped
prefix; an existing timeout instead repeats (PROTOCOL.md `sec:public-handlers`). -/
theorem target_impossible (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {stop i : Nat} {hF0 blocked : Height}
    (hcap : HonestPrefixFinalityCap S rho stop hF0)
    (hrec : NjGap.RecoveryHeight S.cfg hF0 blocked) (hiStop : i < stop)
    {v : V} (hv : v ∈ rho.honest) {t : Time} {a : NamedAttestation V}
    (hi : rho.events[i]? = some (.tick v t))
    (ho : NamedObject.attest a ∈ NamedRun.emittedAt S rho i v t)
    (htarget : (rho.stateBefore S i v).record.legacy.target blocked = none)
    (hlock : (rho.stateBefore S i v).record.legacy.lock blocked = none)
    {T : BlockId} (hp : a.height_pair.erase = HeightPair.target blocked T) : False := by
  have hem : NamedRun.emits S rho v (.attest a) t := ⟨i, hi, ho⟩
  obtain ⟨ht, _, hval⟩ := WindowAction.run_emission_fields S hem
  subst v
  subst t
  obtain ⟨D, J, _, ha, hs, hD, hh, _⟩ :=
    honestEmittedHeightRow_exactFGSelectorWitness S adm hv hem
      (show a.height_pair.erase.height? = some blocked from hp ▸ rfl)
  let n := windowActionReadAt S rho a.val_index a.round
  have hinv : NamedConfirmationMembership.Invariant S.E S.cfg n.st :=
    WindowAction.windowRead_invariant S a.val_index _ _
      (NamedRuntime.stateBeforeTime_invariants S rho _ a.val_index).1
  have hu := input_universe S adm hcap hrec hiStop hv hi
  have hpre := NamedRuntime.tick_prefix_eq_strict S rho
    adm.toNamedScheduleWellFormed.sorted adm.toNamedScheduleWellFormed.nodup hi
  have hrecord : n.record = (rho.stateBefore S i a.val_index).record := by
    change n.record = (NamedRun.stateBefore S rho i a.val_index).record
    rw [hpre]
    rfl
  have htimeout : (windowActionAttestationAt S rho a.val_index a.round).height_pair =
      NamedHeightPair.vote blocked (n.st.core.σ D.erase).T_h.root true := by
    cases ht : n.record.legacy.timeout blocked with
    | false =>
        exact timeout_of_fresh_input S a.val_index n hinv hu hD hs hh
          ⟨by rw [hrecord]; exact htarget, ht, by rw [hrecord]; exact hlock⟩
    | true =>
        exact round_action_height_pair_timeout_of_recorded_source
          (NamedProfile.gradeContract n.cache) S.E S.hc (S.node a.val_index)
          n.st.core.toHealing n.record hs hh ht
  have he := congrArg NamedHeightPair.erase htimeout
  rw [← ha, hp] at he
  cases he

#print axioms input_universe
#print axioms finality_height_ne
#print axioms timeout_of_fresh_input
#print axioms target_impossible
end DecoupledConsensusModel.Proofs.WindowRecoveryInput
