import DecoupledConsensusProofs.Execution.OutageInputs

/-!
Late actions invalidate a vacuous base case with only a paper-time boundary.
A complete public tick schedule emits a round-zero row at the boundary 7,
although the previous paper action is at 6. The candidate prefix P is arbitrary,
as allowed by that lemma; this is not a counterexample to an outage regime.
The diagnostic does not import RoundBase and uses only kernel-checked proofs.
-/

open DecoupledConsensusModel Protocol Execution
namespace VoteWindowLateBoundary

def E : Env (Fin 1) where
  Δ := 1
  Δ_pos := by norm_num
  t_GST := 0
  t_GST_nonneg := le_rfl
  proposer := fun _ => 0
  committees := ⟨fun _ => Finset.univ⟩
  electorate := { weight := fun _ => 1, weight_pos := by intro v; decide }
def hc : HealConfig := ⟨4, by decide, 2, by decide⟩
def cfg : HeightConfig where
  K := 4
  D := 2
  timeoutDelay := 8
  K_ge_four := by decide
  D_ge_two := by decide
def node (v : Fin 1) : Node (Fin 1) where
  val_index := v
  new_root := fun s => ⟨s + 1⟩
  awake := fun _ => true
  act := fun r => slotStart E.Δ (hc.opening_slot r) + 7

def S : Setup (Fin 1) where
  E := E
  hc := hc
  cfg := cfg
  node := node
  node_val_index := by intro v; rfl
  act_post_completion := by
    intro v r
    simp [node, domain, Phase.domainOffset, opening, proposal_time, Env.t, E]
  act_before_round_end := by
    intro v r
    simp [node, opening, proposal_time, Env.t, E, hc, HealConfig.opening_slot, slotStart]
    nlinarith
  act_pre_cutoff := by
    intro v r
    simp [node, early, Phase.earlyOffset, opening, proposal_time, Env.t, E,
      hc, HealConfig.opening_slot, slotStart]
    nlinarith
  act_public := by
    intro v r
    refine ⟨16 * r + 7, ?_⟩
    simp [node, E, hc, HealConfig.opening_slot, slotStart]
    ring
  timeout_rounds := by decide
  committee_nonempty := by intro s; exact ⟨0, Finset.mem_univ _⟩
  outage_window := by decide

def rho : NamedRun (Fin 1) where
  honest := Finset.univ
  horizon := 7
  events := [.tick 0 0, .tick 0 1, .tick 0 2, .tick 0 3, .tick 0 4,
    .tick 0 5, .tick 0 6, .tick 0 7]

def row : NamedAttestation (Fin 1) :=
  NamedActionReads.windowActionAttestationAt S rho 0 0

def K : NamedBlock (Fin 1) := .node .genesis 1 ⟨2⟩ [] [] [] 0

def P : NamedBlock (Fin 1) := .node .genesis 1 ⟨99⟩ [] [] [] 0

set_option maxRecDepth 10000 in
theorem emission : NamedRun.emits S rho row.val_index (.attest row) 7 := by
  refine ⟨7, rfl, ?_⟩
  decide +kernel

set_option maxRecDepth 10000 in
theorem carrier_scoped : NamedRun.blockInRun S rho K := by
  apply Proofs.NamedRuntime.blockInRun_of_direct S rho
  apply Proofs.NamedRuntime.directBlock_of_prefix S rho (Finset.mem_univ (0 : Fin 1)) 7
  decide +kernel

theorem in_horizon : ∀ e ∈ rho.events, 0 ≤ e.time ∧ e.time ≤ rho.horizon := by
  intro e he
  change e ∈ [.tick 0 0, .tick 0 1, .tick 0 2, .tick 0 3, .tick 0 4,
    .tick 0 5, .tick 0 6, .tick 0 7] at he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem schedule : NamedScheduleWellFormed S rho where
  horizon_nonneg := by decide
  sorted := by decide
  nodup := by decide
  in_horizon := in_horizon
  honest_only := by intro e he; exact Finset.mem_univ _
  tick_public := by
    intro v t ht
    have hlo : 0 ≤ t := (in_horizon _ ht).1
    refine ⟨t.toNat, ?_⟩
    change t = (t.toNat : Int) * 1
    rw [mul_one, Int.toNat_of_nonneg hlo]
  tick_total := by
    intro v hv t ht hlo hhi
    change t ≤ 7 at hhi
    interval_cases t <;> fin_cases v <;> decide

set_option maxRecDepth 10000 in
theorem body_set :
    (NamedActionReads.windowActionReadFrom S 0
      (NamedRun.stateBefore S rho 7 0) 0).st.bodies = {NamedBlock.genesis, K} := by
  decide +kernel

set_option maxRecDepth 10000 in
theorem base_hpost_fails :
    ¬ (∀ (a : NamedAttestation (Fin 1)) (t : Time), a.val_index ∈ rho.honest →
      NamedRun.emits S rho a.val_index (.attest a) t → 7 ≤ t → a.round < 1 →
      ∀ key, a.confirmed = some key →
        ∀ B : NamedBlock (Fin 1), NamedRun.blockInRun S rho B → B.root = key →
          Block.Preceq P.erase B.erase) := by
  intro h
  obtain ⟨i, hi, _, H, hH, hroot⟩ :=
    Proofs.NamedOutageInputs.emitted_attestation_head S rho emission
  have hiLt : i < 8 := by
    simpa [rho] using (List.getElem?_eq_some_iff.mp hi).1
  have hiEq : i = 7 := by
    interval_cases i <;> first | rfl | cases hi
  subst i
  change H ∈ (NamedActionReads.windowActionReadFrom S 0
    (NamedRun.stateBefore S rho 7 0) 0).st.bodies at hH
  rw [body_set] at hH
  simp only [Finset.mem_insert, Finset.mem_singleton] at hH
  have hscoped : NamedRun.blockInRun S rho H := by
    apply Proofs.NamedRuntime.blockInRun_of_direct S rho
    apply Proofs.NamedRuntime.directBlock_of_prefix S rho (Finset.mem_univ (0 : Fin 1)) 7
    rcases hH with rfl | rfl <;> decide +kernel
  have hc := h row 7 (Finset.mem_univ _) emission le_rfl (by decide)
    H.root hroot H hscoped rfl
  have hn : ¬ Block.Preceq P.erase H.erase := by
    rcases hH with rfl | rfl <;> decide
  exact hn hc

theorem first_boundary : S.a (1 - 1) < 7 := by decide

-- The first-included-round arithmetic used by StableCoverageConsumer also
-- permits a boundary below the next early cutoff, even with formation and
-- retention margins. This checks timing premises, not a full outage regime.
def boundaryRun : NamedRun (Fin 1) where
  honest := Finset.univ
  horizon := 40
  events := (List.range 41).map (fun n => .tick 0 (n : Time))

theorem first_included_round :
    ∀ q : Round, 0 < q → 23 ≤ S.a q → 2 ≤ q := by
  intro q _ hq
  by_contra hnot
  have hqLt : q < 2 := Nat.lt_of_not_ge hnot
  interval_cases q <;>
    norm_num [Setup.a, HealConfig.a, HealConfig.opening_slot, slotStart, S, E, hc] at hq

theorem base_consumer_timing_below_cutoff :
    ((0 : Time) ≤ 23 ∧ (23 : Time) ≤ 32 ∧ 32 ≤ boundaryRun.horizon) ∧
    S.E.t_GST ≤ 32 ∧ (∃ k : Nat, (23 : Time) = (k : Time) * S.E.Δ) ∧
    Internal.NamedStableChainOutage.FormationMargin S 0 23 ∧
    Internal.NamedJointOutage.DomainIncluded S boundaryRun 23 2 ∧
    domain S.E S.hc 2 .g2 ≤ 32 + S.E.Δ ∧
    Internal.NamedStableChainOutage.RetentionDuration S boundaryRun 0 32 ∧
    S.a (2 - 1) < 23 ∧
    (∀ q : Round, 0 < q → 23 ≤ S.a q → 2 ≤ q) ∧
    23 < early S.E S.hc 2 .g2 ∧
    ¬ (∀ v, (S.node v).act (2 - 1) < 23) := by
  refine ⟨by decide, by decide, ⟨23, rfl⟩,
    by unfold Internal.NamedStableChainOutage.FormationMargin; decide,
    by unfold Internal.NamedJointOutage.DomainIncluded; decide,
    by decide,
    by unfold Internal.NamedStableChainOutage.RetentionDuration; decide, by decide,
    first_included_round, by decide, ?_⟩
  intro h
  have hbad := h 0
  norm_num [S, node, hc, E, HealConfig.opening_slot, slotStart] at hbad

#print axioms base_consumer_timing_below_cutoff
#print axioms base_hpost_fails
#print axioms schedule
end VoteWindowLateBoundary
