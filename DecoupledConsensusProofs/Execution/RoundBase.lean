module
public import DecoupledConsensusProofs.Protocol.Schedule.WindowAction

/-!
# Post-boundary emissions from earlier rounds

The vacuous base case uses each validator's actual action boundary.
P2 supplies that boundary after the next early G2 cutoff; the point schedule
recovers the paper-time premise (PROTOCOL.md `sec:healing-schedule`).
-/
@[expose] public section
namespace DecoupledConsensusModel.Proofs.NamedOutageClosure
open Execution Protocol
variable {V : Type} [DecidableEq V] [Fintype V]

/-- After the early G2 cutoff, every preceding-round action is strictly past.
The strict inequality uses positive delay and P2 (PROTOCOL.md `sec:grades`). -/
theorem base_actions_before_of_early (S : Setup V) (b0 : Time) (r : Round)
    (hr : 0 < r) (hcut : early S.E S.hc r .g2 ≤ b0) :
    ∀ v, (S.node v).act (r - 1) < b0 := by
  intro v
  have h := S.act_pre_cutoff v (r - 1)
  rw [Nat.sub_add_cancel (Nat.succ_le_iff.mpr hr)] at h
  have hd := S.E.Δ_pos
  exact lt_of_lt_of_le (by linarith) hcut

/-- A paper instant before the boundary also puts the earlier G2 cutoff
before it (PROTOCOL.md `sec:healing-schedule`). -/
theorem base_actions_before_of_paper_lt (S : Setup V) (b0 : Time) (r : Round)
    (hr : 0 < r) (hpaper : S.a r < b0) :
    ∀ v, (S.node v).act (r - 1) < b0 := by
  apply base_actions_before_of_early S b0 r hr
  have hcut : early S.E S.hc r .g2 ≤ S.a r := by
    have hd := S.E.Δ_pos
    simp only [early, opening, proposal_time, Env.t, Phase.earlyOffset, Setup.a,
      HealConfig.a]
    linarith
  exact hcut.trans hpaper.le

/-- If every validator's preceding-round action is before b0, earlier-round
emissions after b0 are impossible (PROTOCOL.md `sec:healing-schedule`). -/
theorem base_hpost (S : Setup V) (rho : NamedRun V) (b0 : Time) (r : Round)
    (Pn : NamedBlock V) (hfirst : ∀ v, (S.node v).act (r - 1) < b0) :
    ∀ (a : NamedAttestation V) (t : Time), a.val_index ∈ rho.honest →
      NamedRun.emits S rho a.val_index (.attest a) t → b0 ≤ t → a.round < r →
      ∀ key, a.confirmed = some key →
        ∀ K : NamedBlock V, NamedRun.blockInRun S rho K → K.root = key →
          Block.Preceq Pn.erase K.erase := by
  intro a t _ha hem hb0t hlt key _hkey K _hKrun _hKroot
  have ht := (WindowAction.run_emission_fields S hem).1
  have hmono : Monotone (S.node a.val_index).act :=
    (strictMono_nat_of_lt_succ (fun q => S.act_lt_next a.val_index a.val_index q)).monotone
  have hprior : a.round ≤ r - 1 := Nat.le_sub_one_of_lt hlt
  have hbefore : t < b0 := ht ▸ (lt_of_le_of_lt (hmono hprior) (hfirst a.val_index))
  exact False.elim ((not_lt_of_ge hb0t) hbefore)

/-- The paper schedule recovers the original premise and the identical
confirmation conclusion (PROTOCOL.md `sec:healing-schedule`). -/
theorem base_hpost_point (S : Setup V) (rho : NamedRun V) (b0 : Time) (r : Round)
    (Pn : NamedBlock V) (hfirst : S.a (r - 1) < b0)
    (hpoint : ∀ v q, (S.node v).act q = S.a q) :
    ∀ (a : NamedAttestation V) (t : Time), a.val_index ∈ rho.honest →
      NamedRun.emits S rho a.val_index (.attest a) t → b0 ≤ t → a.round < r →
      ∀ key, a.confirmed = some key →
        ∀ K : NamedBlock V, NamedRun.blockInRun S rho K → K.root = key →
          Block.Preceq Pn.erase K.erase := by
  apply base_hpost S rho b0 r Pn
  intro v
  rw [hpoint]
  exact hfirst

#print axioms base_actions_before_of_early
#print axioms base_actions_before_of_paper_lt
#print axioms base_hpost
#print axioms base_hpost_point
end DecoupledConsensusModel.Proofs.NamedOutageClosure
