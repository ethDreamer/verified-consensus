module
public import DecoupledConsensusProofs.Protocol.ChainState.OpeningAlignedCarrierCoverage
public import DecoupledConsensusProofs.Execution.CarrierCoverage

/-!
# Point recovery of opening-aligned carriage

The canonical round's paper source identification and the honest triple
supply the aligned interface at the point schedule. No source or accumulator
condition is added to the setup (PROTOCOL.md `sec:healing-schedule`).
-/
@[expose] public section

namespace DecoupledConsensusModel.Proofs.HealingSurface
open Execution Internal Statements.Instantiation

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The point schedule transports the canonical round's original source
identification and exact height pair to the actual action reader. -/
theorem openingAlignedCarrierCoverage_point
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {q : Round} (hpoint : ∀ v, (S.node v).act q = S.a q)
    (hcar : ProposerCarrierAt S rho q)
    (hpost : S.E.t_GST ≤ S.a q)
    (hhor : Protocol.proposal_time S.E (S.hc.opening_slot q + 2) ≤ rho.horizon)
    (hsource : ∀ v ∈ rho.honest, ∀ P : NamedBlock V,
      proposedBlockAt S rho (S.hc.opening_slot q) = some P →
      actionFGSource S (actionReadAt S rho v q) = some P.erase) :
    OpeningAlignedCarrierCoverage S rho q := by
  refine ⟨carrierCoverage_of_carrier_bound S adm hcar hpost hhor ?_, ?_, ?_⟩
  · intro v
    rw [hpoint v]
    exact action_add_delta_le_plusTwo_proposal_time S q
  · intro v hv P hP
    rw [WindowAction.windowActionReadAt_point S rho v q (hpoint v)]
    exact hsource v hv P hP
  · intro v hv
    rw [WindowAction.windowActionAttestationAt_point S rho v q (hpoint v)]

#print axioms openingAlignedCarrierCoverage_point

/-- With three slots per round, P2 and the opening-confirmation lower bound
force the original paper action time (PROTOCOL.md `sec:healing-schedule`). -/
theorem fg_window_point_of_R_eq_three
    (S : Setup V) (hR : S.hc.R = 3) (v : V) (q : Round)
    (hlower : S.a q ≤ (S.node v).act q) :
    (S.node v).act q = S.a q := by
  have hu := S.act_pre_cutoff v q
  simp only [Protocol.early, Protocol.opening, Protocol.Phase.earlyOffset,
    Protocol.proposal_time, Env.t, slotStart,
    Protocol.HealConfig.opening_slot, hR, Nat.cast_mul, Nat.cast_add,
    Nat.cast_one, Nat.cast_ofNat] at hu
  have ha : S.a q = 4 * S.E.Δ * (q * 3 : Nat) + 6 * S.E.Δ := by
    simp only [Setup.a, Protocol.HealConfig.a, slotStart,
      Protocol.HealConfig.opening_slot, hR]
  simp only [Nat.cast_mul, Nat.cast_ofNat] at ha
  nlinarith

/-- At R=3 the aligned FG window has the point instance, rather than the
whole SG window (PROTOCOL.md `sec:healing-schedule`). -/
theorem openingAlignedCarrierCoverage_of_R_eq_three
    (S : Setup V) {rho : Run V} (adm : Admissible S rho) (hR : S.hc.R = 3)
    {q : Round} (hlower : ∀ v, S.a q ≤ (S.node v).act q)
    (hcar : ProposerCarrierAt S rho q)
    (hpost : S.E.t_GST ≤ S.a q)
    (hhor : Protocol.proposal_time S.E (S.hc.opening_slot q + 2) ≤ rho.horizon)
    (hsource : ∀ v ∈ rho.honest, ∀ P : NamedBlock V,
      proposedBlockAt S rho (S.hc.opening_slot q) = some P →
      actionFGSource S (actionReadAt S rho v q) = some P.erase) :
    OpeningAlignedCarrierCoverage S rho q :=
  openingAlignedCarrierCoverage_point S adm
    (fun v => fg_window_point_of_R_eq_three S hR v q (hlower v))
    hcar hpost hhor hsource

#print axioms fg_window_point_of_R_eq_three
#print axioms openingAlignedCarrierCoverage_of_R_eq_three

/-- The FG timing interval contains exactly the paper tick and the next
public tick; P3 excludes intervening action times
(PROTOCOL.md `sec:healing-schedule`, `sec:public-handlers`). -/
theorem fg_window_two_ticks
    (S : Setup V) (v : V) (q : Round)
    (hlower : S.a q ≤ (S.node v).act q)
    (hupper : (S.node v).act q + S.E.Δ ≤
      Protocol.proposal_time S.E (S.hc.opening_slot q + 2)) :
    (S.node v).act q = S.a q ∨ (S.node v).act q = S.a q + S.E.Δ := by
  let m : Nat := 4 * (q * S.hc.R) + 6
  have ha : S.a q = (m : Time) * S.E.Δ := by
    simp only [m, Setup.a, Protocol.HealConfig.a, slotStart,
      Protocol.HealConfig.opening_slot, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    ring
  have hp : Protocol.proposal_time S.E (S.hc.opening_slot q + 2) =
      S.a q + 2 * S.E.Δ := by
    simp only [Setup.a, Protocol.HealConfig.a, Protocol.proposal_time, Env.t,
      slotStart, Nat.cast_add, Nat.cast_ofNat]
    ring
  obtain ⟨k, hk⟩ := S.act_public v q
  rw [hp] at hupper
  rw [hk, ha] at hlower hupper
  have hbounds : (m : Int) ≤ k ∧ (k : Int) ≤ m + 1 := by
    constructor <;> nlinarith [S.E.Δ_pos]
  have hcases : k = m ∨ k = m + 1 := by omega
  rcases hcases with rfl | rfl
  · exact Or.inl (hk.trans ha.symm)
  · right
    rw [hk, ha, Nat.cast_add, Nat.cast_one]
    ring

#print axioms fg_window_two_ticks

end DecoupledConsensusModel.Proofs.HealingSurface

end
