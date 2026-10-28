import DecoupledConsensusModel.Protocol.Tick
import Mathlib.Tactic

open DecoupledConsensusModel Protocol Execution

namespace VoteWindowPublicTimeGap

-- A candidate schedule for the P1/P2 relaxation; it does not satisfy Setup.act_eq.
def hc : HealConfig := ⟨3, by decide, 2, by decide⟩
def E : Env (Fin 1) where
  Δ := 2
  Δ_pos := by norm_num
  t_GST := 0
  t_GST_nonneg := le_rfl
  proposer := fun _ => 0
  committees := ⟨fun _ => Finset.univ⟩
  electorate := { weight := fun _ => 1, weight_pos := by intro v; omega }

def act (r : Round) : Time := slotStart E.Δ (hc.opening_slot r) + 3

theorem act_eq (r : Round) : act r = 24 * (r : Int) + 3 := by
  simp [act, E, hc, HealConfig.opening_slot, slotStart]
  ring

-- P1: grade 0 has completed and the scheduler reads the intended round.
theorem post_completion (r : Round) : domain E hc r .g0 ≤ act r := by
  simp [domain, opening, proposal_time, Env.t, Phase.domainOffset, act, E]

theorem within_round (r : Round) : hc.round_of (E.slotOf (act r)) = r := by
  rw [act_eq]
  simp only [HealConfig.round_of, hc, Env.slotOf, slotOfTime, E]
  rw [Int.fdiv_eq_ediv_of_nonneg _ (by norm_num)]
  change ((24 * (r : Int) + 3) / 8).toNat / 3 = r
  omega

-- P2: delivery within Delta precedes the next round's earliest grade cutoff.
theorem pre_cutoff (r : Round) : act r + E.Δ ≤ early E hc (r + 1) .g2 := by
  simp [act, early, opening, proposal_time, Env.t, Phase.earlyOffset,
    E, hc, HealConfig.opening_slot, slotStart]
  nlinarith

-- PublicTime requires exactly this multiple-of-Delta equation.
theorem not_public (r : Round) : ¬ ∃ k : Nat, act r = (k : Time) * E.Δ := by
  rw [act_eq]
  rintro ⟨k, h⟩
  change 24 * (r : Int) + 3 = (k : Int) * 2 at h
  omega

-- Even an always-awake node never takes its attestation branch on public ticks.
theorem no_attestation_at_public_tick
    (gc : GradeContract (Fin 1)) (cfg : HeightConfig) (nd : Node (Fin 1))
    (hact : nd.act = act) (st : NamedStore (Fin 1)) (record : NamedRecord)
    (k : Nat) (a : NamedAttestation (Fin 1)) :
    NamedObject.attest a ∉
      (NamedTick.tick gc E hc cfg nd st record ((k : Time) * E.Δ)).2.2 := by
  have hne : ∀ r, (k : Time) * E.Δ ≠ nd.act r := by
    intro r h
    exact not_public r ⟨k, (h.trans (congrFun hact r)).symm⟩
  simp only [NamedTick.tick, TickScheduler.runWith, NamedTick.namedOps, hne,
    false_and, ite_false, List.mem_append, not_or]
  constructor
  · split
    · split <;> simp only [List.mem_nil_iff, List.mem_singleton, reduceCtorEq, not_false_eq_true]
    · simp only [List.mem_nil_iff, not_false_eq_true]
  · split
    · simp only [List.mem_map, reduceCtorEq, and_false, exists_false, not_false_eq_true]
    · simp only [List.mem_nil_iff, not_false_eq_true]

end VoteWindowPublicTimeGap

#print axioms VoteWindowPublicTimeGap.post_completion
#print axioms VoteWindowPublicTimeGap.within_round
#print axioms VoteWindowPublicTimeGap.pre_cutoff
#print axioms VoteWindowPublicTimeGap.not_public
#print axioms VoteWindowPublicTimeGap.no_attestation_at_public_tick
