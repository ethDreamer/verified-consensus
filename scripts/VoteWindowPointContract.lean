import DecoupledConsensusProofs.Protocol.Schedule.WindowAction

open DecoupledConsensusModel Protocol Execution
namespace VoteWindowPointContract

def E : Env (Fin 1) where
  Δ := 1
  Δ_pos := by norm_num
  t_GST := 0
  t_GST_nonneg := le_rfl
  proposer := fun _ => 0
  committees := ⟨fun _ => Finset.univ⟩
  electorate := { weight := fun _ => 1, weight_pos := by intro v; decide }
def hc : HealConfig := ⟨3, by decide, 2, by decide⟩
def cfg : HeightConfig where
  K := 4
  D := 2
  timeoutDelay := 6
  K_ge_four := by decide
  D_ge_two := by decide
def node (v : Fin 1) : Node (Fin 1) where
  val_index := v
  new_root := fun s => ⟨s + 1⟩
  awake := fun _ => true
  act := fun r => slotStart E.Δ (hc.opening_slot r) + 5

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
    refine ⟨12 * r + 5, ?_⟩
    simp [node, E, hc, HealConfig.opening_slot, slotStart]
    ring
  timeout_rounds := by decide
  committee_nonempty := by intro s; exact ⟨0, Finset.mem_univ _⟩
  outage_window := by decide

-- This Setup satisfies P1/P2/P3, but its action is at 5 rather than a_0 = 6.
theorem no_emissions_at_point :
    (NamedNode.tick S 0 NamedNode.initial (S.a 0)).2 = [] := by
  rfl

-- At the actual action, a Goldfish vote shares the tick with the attestation.
theorem two_emissions_at_action :
    (NamedNode.tick S 0 NamedNode.initial ((S.node 0).act 0)).2.length = 2 := by
  rfl

#print axioms no_emissions_at_point
#print axioms two_emissions_at_action
#print axioms Proofs.WindowAction.attestation_mem_at_action
#print axioms Proofs.WindowAction.emitted_at_action_time
#print axioms Proofs.WindowAction.run_emission_iff
#print axioms Proofs.WindowAction.honest_emits_action

end VoteWindowPointContract
