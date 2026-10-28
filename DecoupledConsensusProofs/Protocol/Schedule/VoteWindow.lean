module
public import DecoupledConsensusModel.Execution.Setup
public import Mathlib.Tactic

/-!
# Vote-window arithmetic

Relates the action window to grade completion and strict delivery cutoffs
(PROTOCOL.md `sec:healing-schedule`, `sec:grades`). Read the execution setup
before this file and the scheduled-action proofs after it.
-/
@[expose] public section

namespace DecoupledConsensusModel.Protocol.HealConfig

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The paper action reads completed grade 0. -/
theorem a_post_completion (hc : HealConfig) (E : Env V) (r : Round) :
    domain E hc r .g0 ≤ hc.a E.Δ r := by
  have hd := E.Δ_pos
  simp only [domain, opening, proposal_time, Env.t, Phase.domainOffset, a]
  linarith

/-- The paper action remains in its round using only the configured round bound. -/
theorem a_before_round_end (hc : HealConfig) (E : Env V) (r : Round) :
    hc.a E.Δ r < opening E hc (r + 1) := by
  have hR : (3 : Int) ≤ hc.R := by exact_mod_cast hc.R_ge_three
  have hd := E.Δ_pos
  simp only [a, opening, proposal_time, Env.t, opening_slot, slotStart,
    Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  nlinarith

/-- The paper action's strict delivery precedes the next G2 early cutoff. -/
theorem a_pre_cutoff (hc : HealConfig) (E : Env V) (r : Round) :
    hc.a E.Δ r + E.Δ ≤ early E hc (r + 1) .g2 := by
  have hR : (3 : Int) ≤ hc.R := by exact_mod_cast hc.R_ge_three
  have hd := E.Δ_pos
  simp only [a, early, opening, proposal_time, Env.t, Phase.earlyOffset,
    opening_slot, slotStart, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  nlinarith

/-- The paper action lies on the public tick grid. -/
theorem a_public (hc : HealConfig) (E : Env V) (r : Round) :
    ∃ k : Nat, hc.a E.Δ r = (k : Time) * E.Δ := by
  refine ⟨4 * (r * hc.R) + 6, ?_⟩
  simp only [a, opening_slot, slotStart, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  ring

end DecoupledConsensusModel.Protocol.HealConfig

namespace DecoupledConsensusModel.Execution.Setup

variable {V : Type} [DecidableEq V] [Fintype V]

/-- An action occurs after the beginning of its round. -/
theorem opening_le_act (S : Setup V) (v : V) (r : Round) :
    Protocol.opening S.E S.hc r ≤ (S.node v).act r := by
  have h := S.act_post_completion v r
  simp only [Protocol.domain, Protocol.Phase.domainOffset] at h
  have hd := S.E.Δ_pos
  linarith

/-- Window actions occur at nonnegative times. -/
theorem act_nonneg (S : Setup V) (v : V) (r : Round) :
    0 ≤ (S.node v).act r := by
  have h := S.opening_le_act v r
  have ho : 0 ≤ Protocol.opening S.E S.hc r := by
    unfold Protocol.opening Protocol.proposal_time Env.t slotStart
    have hd : (0 : Int) ≤ S.E.Δ := le_of_lt S.E.Δ_pos
    positivity
  exact le_trans ho h

/-- The scheduler's slot-to-round test recognizes a window action. -/
theorem act_round (S : Setup V) (v : V) (r : Round) :
    S.hc.round_of (S.E.slotOf ((S.node v).act r)) = r := by
  have hd : (0 : Int) < 4 * S.E.Δ := by have h : (0 : Int) < S.E.Δ := S.E.Δ_pos; linarith
  have hl := S.opening_le_act v r
  have hu := S.act_before_round_end v r
  simp only [Protocol.opening, Protocol.proposal_time, Env.t, slotStart] at hl hu
  have hlo : (S.hc.opening_slot r : Int) ≤ (S.node v).act r / (4 * S.E.Δ) := by
    apply (Int.le_ediv_iff_mul_le hd).mpr
    nlinarith
  have hhi : (S.node v).act r / (4 * S.E.Δ) < (S.hc.opening_slot (r + 1) : Int) := by
    apply (Int.ediv_lt_iff_lt_mul hd).mpr
    nlinarith
  have hn : 0 ≤ (S.node v).act r / (4 * S.E.Δ) :=
    le_trans (Int.natCast_nonneg _) hlo
  have hs : S.E.slotOf ((S.node v).act r) =
      ((S.node v).act r / (4 * S.E.Δ)).toNat := by
    simp only [Env.slotOf, slotOfTime, Int.fdiv_eq_ediv_of_nonneg _ (le_of_lt hd)]
  have hslotlo : r * S.hc.R ≤ S.E.slotOf ((S.node v).act r) := by
    rw [hs]
    exact (Int.le_toNat hn).mpr hlo
  have hslothi : S.E.slotOf ((S.node v).act r) < (r + 1) * S.hc.R := by
    rw [hs]
    exact (Int.toNat_lt hn).mpr hhi
  have hR : 0 < S.hc.R := by have := S.hc.R_ge_three; omega
  unfold Protocol.HealConfig.round_of
  have hlo' := (Nat.le_div_iff_mul_le hR).mpr hslotlo
  have hhi' := (Nat.div_lt_iff_lt_mul hR).mpr hslothi
  exact Nat.le_antisymm (Nat.lt_succ_iff.mp hhi') hlo'

/-- Every grade has completed by the validator's action. -/
theorem domain_le_act (S : Setup V) (v : V) (r : Round) (p : Protocol.Phase) :
    Protocol.domain S.E S.hc r p ≤ (S.node v).act r := by
  have h := S.act_post_completion v r
  have hd : (0 : Int) < S.E.Δ := S.E.Δ_pos
  cases p <;> simp only [Protocol.domain, Protocol.Phase.domainOffset] at h ⊢ <;> linarith

/-- Even different validators' actions respect the order between successive rounds. -/
theorem act_lt_next (S : Setup V) (u v : V) (r : Round) :
    (S.node u).act r < (S.node v).act (r + 1) :=
  lt_of_lt_of_le (S.act_before_round_end u r) (S.opening_le_act v (r + 1))

/-- Strict delivery of a window vote precedes each next-round early cutoff. -/
theorem delivery_before_next_early (S : Setup V) (v : V) (r : Round)
    (p : Protocol.Phase) {received : Time}
    (hdelivery : received < (S.node v).act r + S.E.Δ) :
    received < Protocol.early S.E S.hc (r + 1) p := by
  have h := lt_of_lt_of_le hdelivery (S.act_pre_cutoff v r)
  have hd : (0 : Int) < S.E.Δ := S.E.Δ_pos
  cases p <;> simp only [Protocol.early, Protocol.Phase.earlyOffset] at h ⊢ <;> linarith

end DecoupledConsensusModel.Execution.Setup
