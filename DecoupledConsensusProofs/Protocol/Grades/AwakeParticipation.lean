module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.OutageInputs
public import DecoupledConsensusProofs.Protocol.Schedule.Action
public import DecoupledConsensusProofs.Execution.HealthyLocalFacts
public import DecoupledConsensusProofs.Protocol.Grades.FrameForward
public import DecoupledConsensusProofs.Protocol.Store.BoundaryRows

@[expose] public section

/-!
# Awake participation closes the named outage inputs

The public outage premise is stated on the environment's awake profile. This
file derives the historical emission predicates used by the existing outage
proof from that premise and the named action schedule.
-/
namespace DecoupledConsensusModel.Proofs.NamedOutageClosure

open Internal Execution Internal.NamedOutageEntry
open DecoupledConsensusModel.Protocol
open Proofs.HealingSurface

variable {V : Type} [DecidableEq V] [Fintype V]

/-- At an action time inside the run, an honest validator emits exactly when it
is awake for that round. -/
theorem honestRoundVoters_eq_awake
    (S : Setup V) (rho : NamedRun V)
    (sch : NamedScheduleWellFormed S rho) (k : Round)
    (hk : ∀ v ∈ rho.honest, (S.node v).act k ≤ rho.horizon) :
    honestRoundVoters S rho k = honestAwakeAt S rho k := by
  ext v
  constructor
  · intro hv
    obtain ⟨hvHon, ha⟩ :=
      (Proofs.NamedOutageInputs.honestRoundVoters_iff S rho v k).mp hv
    obtain ⟨a, _, hround, hem⟩ := ha
    have hawake := (WindowAction.run_emission_fields S hem).2.1
    rw [hround] at hawake
    exact Finset.mem_filter.mpr ⟨hvHon, hawake⟩
  · intro hv
    obtain ⟨hvHon, hawake⟩ := Finset.mem_filter.mp hv
    have hem := WindowAction.honest_emits_action S sch hvHon k hawake (hk v hvHon)
    apply (Proofs.NamedOutageInputs.honestRoundVoters_iff S rho v k).mpr
    refine ⟨hvHon, NamedActionReads.windowActionAttestationAt S rho v k, ?_, ?_, hem⟩
    · exact S.node_val_index v
    · exact WindowAction.actionRead_round S v _ k

/-- At the point schedule the original paper-time horizon hypothesis suffices
(PROTOCOL.md `sec:healing-schedule`). -/
theorem honestRoundVoters_eq_awake_point
    (S : Setup V) (rho : NamedRun V) (sch : NamedScheduleWellFormed S rho) (k : Round)
    (hpoint : ∀ v q, (S.node v).act q = S.a q) (hk : S.a k ≤ rho.horizon) :
    honestRoundVoters S rho k = honestAwakeAt S rho k :=
  honestRoundVoters_eq_awake S rho sch k (by intro v _; simpa only [hpoint] using hk)

/-- P2 puts every older action before every grade-domain cutoff of this round
(PROTOCOL.md `sec:healing-schedule`). -/
private theorem prior_action_le_domain
    (S : Setup V) (v : V) {k r : Round} (hkr : k < r) (p : Phase) :
    (S.node v).act k ≤ domain S.E S.hc r p := by
  have hp := S.act_deadline_le_early v hkr
  have hd := S.E.Δ_pos
  simp only [early, Phase.earlyOffset] at hp
  cases p <;> simp only [domain, Phase.domainOffset] <;> linarith

private theorem honestAwakeAt_subset_window
    (S : Setup V) (rho : NamedRun V) {r : Round} (hr : 0 < r) :
    honestAwakeAt S rho (r - 1) ⊆
      honestAwakeWindow (fun v => (S.node v).awake)
        rho.honest S.hc.η_SG r := by
  intro v hv
  obtain ⟨hvHon, hawake⟩ := Finset.mem_filter.mp hv
  apply Finset.mem_filter.mpr
  refine ⟨hvHon, ?_⟩
  apply List.any_eq_true.mpr
  exact ⟨r - 1,
    Protocol.pred_mem_latest_window S.hc.η_SG r S.hc.η_SG_ge_one hr,
    hawake⟩

/-- The awake grade premise implies the older sleepy-window premise. -/
theorem outageSleepyThroughout_of_awake
    (S : Setup V) (rho : NamedRun V) :
    AwakeGradeMajorityThroughout S rho → OutageSleepyThroughout S rho := by
  intro hawake r hr hcovered
  have hgrade := hawake r hr hcovered
  unfold AwakeGradeMajority at hgrade
  have hfaulty : Finset.univ \ rho.honest ⊆
      (Finset.univ \ rho.honest) ∪ staleAwake S rho r :=
    Finset.subset_union_left
  have hleft := S.E.electorate.weightOf_mono hfaulty
  have hright := S.E.electorate.weightOf_mono
    (honestAwakeAt_subset_window S rho hr)
  exact lt_of_le_of_lt hleft (lt_of_lt_of_le hgrade hright)

/-- A covered round puts its preceding action, and therefore all older eligible
actions, inside the run horizon. This is the schedule fact needed to replace
historical emissions by the awake profile. -/
private theorem prior_action_in_horizon
    (S : Setup V) (rho : NamedRun V) {k r : Round} (hkr : k < r)
    (hcovered : RoundCovered S rho r) (v : V) :
    (S.node v).act k ≤ rho.horizon := by
  rcases hcovered with haction | ⟨p, _, hdomain⟩
  · exact (prior_action_le_domain S v hkr .g2).trans
      ((FrameForward.domain_le_a S r .g2).trans haction.2)
  · exact (prior_action_le_domain S v hkr p).trans hdomain

private theorem previous_action_in_horizon
    (S : Setup V) (rho : NamedRun V) {r : Round} (hr : 0 < r)
    (hcovered : RoundCovered S rho r) :
    ∀ v ∈ rho.honest, (S.node v).act (r - 1) ≤ rho.horizon :=
  fun v _ => prior_action_in_horizon S rho (Nat.sub_lt hr (by decide)) hcovered v

/-- The awake and emitted versions of the stale historical voter set coincide
at every covered positive round. -/
private theorem staleHistoricalVoters_eq_awake
    (S : Setup V) (rho : NamedRun V)
    (sch : NamedScheduleWellFormed S rho) {r : Round} (hr : 0 < r)
    (hcovered : RoundCovered S rho r) :
    staleHistoricalVoters S rho r = staleAwake S rho r := by
  have hprev : ∀ v ∈ rho.honest, (S.node v).act (r - 1) ≤ rho.horizon :=
    previous_action_in_horizon S rho hr hcovered
  have hround : ∀ k : Round,
      k ∈ (Finset.range r).filter
        (fun k => r - S.hc.η_SG ≤ k ∧ k + 1 < r) →
      ∀ v ∈ rho.honest, (S.node v).act k ≤ rho.horizon := by
    intro k hk
    obtain ⟨_, ⟨_, hklt⟩⟩ := Finset.mem_filter.mp hk
    exact fun v _ => prior_action_in_horizon S rho (Nat.lt_of_succ_lt hklt) hcovered v
  have hprevVoters : honestRoundVoters S rho (r - 1) =
      honestAwakeAt S rho (r - 1) :=
    honestRoundVoters_eq_awake S rho sch (r - 1) hprev
  have hhistorical : historicalHonestVoters S rho r =
      ((Finset.range r).filter
        (fun k => r - S.hc.η_SG ≤ k ∧ k + 1 < r)).biUnion
        (fun k => honestAwakeAt S rho k) := by
    unfold historicalHonestVoters
    ext v
    constructor
    · intro hv
      obtain ⟨k, hk, hvk⟩ := Finset.mem_biUnion.mp hv
      have heq := honestRoundVoters_eq_awake S rho sch k (hround k hk)
      rw [heq] at hvk
      exact Finset.mem_biUnion.mpr ⟨k, hk,
        hvk⟩
    · intro hv
      obtain ⟨k, hk, hvk⟩ := Finset.mem_biUnion.mp hv
      have heq := honestRoundVoters_eq_awake S rho sch k (hround k hk)
      rw [← heq] at hvk
      exact Finset.mem_biUnion.mpr ⟨k, hk,
        hvk⟩
  unfold staleHistoricalVoters staleAwake
  rw [hhistorical, hprevVoters]

/-- The awake grade premise implies the historical grade-forming premise. -/
theorem gradeFormingThroughout_of_awake
    (S : Setup V) (rho : NamedRun V)
    (sch : NamedScheduleWellFormed S rho) :
    AwakeGradeMajorityThroughout S rho → GradeFormingThroughout S rho := by
  intro hawake r hr hcovered
  have hstale := staleHistoricalVoters_eq_awake S rho sch hr hcovered
  have hprev : honestRoundVoters S rho (r - 1) =
      honestAwakeAt S rho (r - 1) :=
    honestRoundVoters_eq_awake S rho sch (r - 1)
      (previous_action_in_horizon S rho hr hcovered)
  have hgrade := hawake r hr hcovered
  unfold GradeFormingMajority
  rw [hstale, hprev]
  exact hgrade

/-- Convert an awake grade majority at one covered round to the emitted-voter
form. -/
theorem gradeFormingMajority_of_awakeAt
    (S : Setup V) (rho : NamedRun V)
    (sch : NamedScheduleWellFormed S rho) {r : Round}
    (hr : 0 < r) (hcovered : RoundCovered S rho r)
    (hawake : AwakeGradeMajority S rho r) :
    GradeFormingMajority S rho r := by
  have hstale := staleHistoricalVoters_eq_awake S rho sch hr hcovered
  have hprev : honestRoundVoters S rho (r - 1) =
      honestAwakeAt S rho (r - 1) :=
    honestRoundVoters_eq_awake S rho sch (r - 1)
      (previous_action_in_horizon S rho hr hcovered)
  unfold GradeFormingMajority
  rw [hstale, hprev]
  exact hawake

#print axioms honestRoundVoters_eq_awake_point
#print axioms honestRoundVoters_eq_awake
#print axioms outageSleepyThroughout_of_awake
#print axioms gradeFormingThroughout_of_awake

end DecoupledConsensusModel.Proofs.NamedOutageClosure

end
