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

/-- Grade completion respects round order (PROTOCOL.md `sec:grades`). -/
theorem domain_mono (hc : HealConfig) (E : Env V) (p : Phase)
    {q r : Round} (hqr : q ≤ r) : domain E hc q p ≤ domain E hc r p := by
  have hd : 0 ≤ E.Δ := le_of_lt E.Δ_pos
  simp only [domain, opening, proposal_time, Env.t, opening_slot, slotStart]
  gcongr

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

/-- An action strictly before G0 completion belongs to an earlier round
(PROTOCOL.md `sec:healing-schedule`). -/
theorem round_lt_of_act_lt_domain (S : Setup V) (v : V) {q r : Round}
    (h : (S.node v).act q < Protocol.domain S.E S.hc r .g0) : q < r := by
  by_contra hnot
  exact (not_lt_of_ge (le_trans (S.hc.domain_mono S.E .g0 (Nat.le_of_not_gt hnot))
    (S.act_post_completion v q))) h

/-- The paper instant may see this round's actions, but no later round
(PROTOCOL.md `sec:healing-schedule`). -/
theorem round_le_of_act_lt_a (S : Setup V) (v : V) {q r : Round}
    (h : (S.node v).act q < S.a r) : q ≤ r := by
  have hnext : S.a r < Protocol.domain S.E S.hc (r + 1) .g0 := by
    have hend := S.hc.a_before_round_end S.E r
    have hd := S.E.Δ_pos
    change S.hc.a S.E.Δ r < _
    simp only [Protocol.domain, Protocol.Phase.domainOffset]
    linarith
  exact Nat.lt_succ_iff.mp (S.round_lt_of_act_lt_domain v (lt_trans h hnext))

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

/-- Every time inside the round has that round's scheduler index
(PROTOCOL.md `sec:healing-schedule`). -/
theorem round_of_between_openings (S : Setup V) (r : Round) (t : Time)
    (hl : Protocol.opening S.E S.hc r ≤ t)
    (hu : t < Protocol.opening S.E S.hc (r + 1)) :
    S.hc.round_of (S.E.slotOf t) = r := by
  have hd : (0 : Int) < 4 * S.E.Δ := by have h : (0 : Int) < S.E.Δ := S.E.Δ_pos; linarith
  simp only [Protocol.opening, Protocol.proposal_time, Env.t, slotStart] at hl hu
  have hlo : (S.hc.opening_slot r : Int) ≤ t / (4 * S.E.Δ) := by
    apply (Int.le_ediv_iff_mul_le hd).mpr
    nlinarith
  have hhi : t / (4 * S.E.Δ) < (S.hc.opening_slot (r + 1) : Int) := by
    apply (Int.ediv_lt_iff_lt_mul hd).mpr
    nlinarith
  have hn : 0 ≤ t / (4 * S.E.Δ) :=
    le_trans (Int.natCast_nonneg _) hlo
  have hs : S.E.slotOf (t) =
      (t / (4 * S.E.Δ)).toNat := by
    simp only [Env.slotOf, slotOfTime, Int.fdiv_eq_ediv_of_nonneg _ (le_of_lt hd)]
  have hslotlo : r * S.hc.R ≤ S.E.slotOf (t) := by
    rw [hs]
    exact (Int.le_toNat hn).mpr hlo
  have hslothi : S.E.slotOf (t) < (r + 1) * S.hc.R := by
    rw [hs]
    exact (Int.toNat_lt hn).mpr hhi
  have hR : 0 < S.hc.R := by have := S.hc.R_ge_three; omega
  unfold Protocol.HealConfig.round_of
  have hlo' := (Nat.le_div_iff_mul_le hR).mpr hslotlo
  have hhi' := (Nat.div_lt_iff_lt_mul hR).mpr hslothi
  exact Nat.le_antisymm (Nat.lt_succ_iff.mp hhi') hlo'

/-- The scheduler's slot-to-round test recognizes a window action. -/
theorem act_round (S : Setup V) (v : V) (r : Round) :
    S.hc.round_of (S.E.slotOf ((S.node v).act r)) = r :=
  S.round_of_between_openings r _ (S.opening_le_act v r) (S.act_before_round_end v r)

/-- The whole strict delivery interval of an actual action stays in its round.
P2 leaves the next opening beyond the delivery deadline (PROTOCOL.md `sec:grades`). -/
theorem round_of_between_act (S : Setup V) (v : V) (r : Round) {t : Time}
    (hlo : (S.node v).act r ≤ t) (hhi : t < (S.node v).act r + S.E.Δ) :
    S.hc.round_of (S.E.slotOf t) = r := by
  apply S.round_of_between_openings r t ((S.opening_le_act v r).trans hlo)
  have h := hhi.trans_le (S.act_pre_cutoff v r)
  have hd := S.E.Δ_pos
  simp only [Protocol.early, Protocol.Phase.earlyOffset] at h
  linarith

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

/-- The latest permitted action deadline precedes the next paper instant
(PROTOCOL.md `sec:healing-schedule`). -/
theorem act_deadline_lt_next_a (S : Setup V) (v : V) (r : Round) :
    (S.node v).act r + S.E.Δ < S.a (r + 1) := by
  apply lt_of_le_of_lt (S.act_pre_cutoff v r)
  have hd := S.E.Δ_pos
  simp only [Protocol.early, Protocol.opening, Protocol.proposal_time, Env.t,
    Protocol.Phase.earlyOffset, Setup.a, Protocol.HealConfig.a]
  linarith

/-- P2 bounds a prior round's action deadline by every later G2 cutoff
(PROTOCOL.md `sec:grades`). -/
theorem act_deadline_le_early (S : Setup V) (v : V) {q r : Round} (hqr : q < r) :
    (S.node v).act q + S.E.Δ ≤ Protocol.early S.E S.hc r .g2 := by
  apply (S.act_pre_cutoff v q).trans
  have h := S.hc.domain_mono S.E .g0 hqr
  simp only [Protocol.domain, Protocol.early, Protocol.Phase.domainOffset,
    Protocol.Phase.earlyOffset] at h ⊢
  linarith

/-- The inclusive opening read fits inside the strict G0 completion cut.
Time is integral and the configured delay is positive (PROTOCOL.md `sec:grades`). -/
theorem opening_read_le_completion (S : Setup V) (r : Round) :
    Protocol.domain S.E S.hc r .g1 + 1 ≤ Protocol.domain S.E S.hc r .g0 := by
  have hd := S.E.Δ_pos
  simp only [Protocol.domain, Protocol.Phase.domainOffset]
  have hd1 : (1 : Int) ≤ S.E.Δ := Int.add_one_le_iff.mpr hd
  linarith

/-- Strict delivery of a window vote precedes each next-round early cutoff. -/
theorem delivery_before_next_early (S : Setup V) (v : V) (r : Round)
    (p : Protocol.Phase) {received : Time}
    (hdelivery : received < (S.node v).act r + S.E.Δ) :
    received < Protocol.early S.E S.hc (r + 1) p := by
  have h := lt_of_lt_of_le hdelivery (S.act_pre_cutoff v r)
  have hd : (0 : Int) < S.E.Δ := S.E.Δ_pos
  cases p <;> simp only [Protocol.early, Protocol.Phase.earlyOffset] at h ⊢ <;> linarith

end DecoupledConsensusModel.Execution.Setup
