module
public import DecoupledConsensusProofs.Protocol.Schedule.VoteWindow

/-!
# First proposal time after the vote-window deadline

The first public proposal time after next-round early G2 is the last slot
of the current round. This is a schedule fact; honesty of its proposer is
separate (PROTOCOL.md `sec:healing-schedule`, `proposal_attestations`).
-/
@[expose] public section
namespace DecoupledConsensusModel.Execution.Setup
open Protocol
variable {V : Type} [DecidableEq V] [Fintype V]

/-- The first public proposal slot at or after P2's deadline
(PROTOCOL.md `sec:healing-schedule`). -/
def deadlineProposalSlot (S : Setup V) (q : Round) : Slot :=
  S.hc.opening_slot (q + 1) - 1

/-- The deadline proposal immediately precedes the next opening slot
(PROTOCOL.md `sec:healing-schedule`). -/
theorem deadlineProposalSlot_add_one (S : Setup V) (q : Round) :
    S.deadlineProposalSlot q + 1 = S.hc.opening_slot (q + 1) := by
  apply Nat.sub_add_cancel
  have hR := S.hc.R_ge_three
  simp only [HealConfig.opening_slot, Nat.add_mul, Nat.one_mul]
  omega

/-- P2's cutoff is before this proposal time by one network-delay unit
(PROTOCOL.md `sec:grades`). -/
theorem deadlineProposal_time (S : Setup V) (q : Round) :
    proposal_time S.E (S.deadlineProposalSlot q) =
      early S.E S.hc (q + 1) .g2 + S.E.Δ := by
  have hk : (S.deadlineProposalSlot q : Int) + 1 =
      (S.hc.opening_slot (q + 1) : Int) := by
    exact_mod_cast S.deadlineProposalSlot_add_one q
  simp only [proposal_time, Env.t, slotStart, early, opening, Phase.earlyOffset]
  rw [← hk]
  ring

/-- No earlier public proposal meets the P2 cutoff
(PROTOCOL.md `sec:healing-schedule`). -/
theorem deadlineProposalSlot_le_iff (S : Setup V) (q : Round) (s : Slot) :
    S.deadlineProposalSlot q ≤ s ↔
      early S.E S.hc (q + 1) .g2 ≤ proposal_time S.E s := by
  have hk := S.deadlineProposal_time q
  have hd := S.E.Δ_pos
  have htime : ∀ k : Slot, proposal_time S.E k = 4 * S.E.Δ * (k : Int) :=
    fun _ => rfl
  constructor
  · intro h
    have hh : (S.deadlineProposalSlot q : Int) ≤ (s : Int) := by exact_mod_cast h
    rw [htime] at hk ⊢
    nlinarith
  · intro h
    by_contra hn
    have hh : (s : Int) + 1 ≤ (S.deadlineProposalSlot q : Int) := by
      exact_mod_cast Nat.lt_of_not_ge hn
    rw [htime] at hk h
    nlinarith

/-- The first deadline proposal is still in the row's own round
(PROTOCOL.md `proposal_attestations`). -/
theorem deadlineProposal_round (S : Setup V) (q : Round) :
    S.hc.round_of (S.deadlineProposalSlot q) = q := by
  have hk := S.deadlineProposalSlot_add_one q
  have hR := S.hc.R_ge_three
  simp only [HealConfig.opening_slot, Nat.add_mul, Nat.one_mul] at hk
  have hp : 0 < S.hc.R := by omega
  change S.deadlineProposalSlot q / S.hc.R = q
  apply Nat.le_antisymm
  · exact Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul hp).mpr (by
      rw [Nat.succ_mul]
      rw [← hk]
      exact Nat.lt_succ_self _))
  · apply (Nat.le_div_iff_mul_le hp).mpr
    have hh : q * S.hc.R + 1 ≤ q * S.hc.R + S.hc.R :=
      Nat.add_le_add_left hp _
    rw [← hk] at hh
    exact Nat.le_of_add_le_add_right hh

/-- With three slots per round the honest carrier's `+2` slot is exactly
the first deadline proposal (PROTOCOL.md `sec:healing-schedule`). -/
theorem deadlineProposalSlot_eq_plusTwo_of_R_eq_three (S : Setup V)
    (hR : S.hc.R = 3) (q : Round) :
    S.deadlineProposalSlot q = S.hc.opening_slot q + 2 := by
  have hk := S.deadlineProposalSlot_add_one q
  simp only [HealConfig.opening_slot, Nat.add_mul, Nat.one_mul, hR] at hk ⊢
  exact Nat.add_right_cancel hk

/-- With at least four slots, the old carrier triple ends strictly before
the availability cutoff (PROTOCOL.md `sec:healing-schedule`). -/
theorem plusTwo_lt_deadline_of_four_le_R (S : Setup V)
    (hR : 4 ≤ S.hc.R) (q : Round) :
    proposal_time S.E (S.hc.opening_slot q + 2) <
      early S.E S.hc (q + 1) .g2 := by
  apply lt_of_not_ge
  rw [← S.deadlineProposalSlot_le_iff]
  have hk := S.deadlineProposalSlot_add_one q
  simp only [HealConfig.opening_slot, Nat.add_mul, Nat.one_mul] at hk ⊢
  intro hle
  have hh := Nat.add_le_add_right hle 1
  rw [hk] at hh
  exact (Nat.not_le_of_gt hR) (Nat.le_of_add_le_add_left
    (by simpa only [Nat.add_assoc] using hh))

#print axioms deadlineProposalSlot_eq_plusTwo_of_R_eq_three
#print axioms plusTwo_lt_deadline_of_four_le_R
#print axioms deadlineProposal_time
#print axioms deadlineProposalSlot_le_iff
#print axioms deadlineProposal_round
end DecoupledConsensusModel.Execution.Setup
