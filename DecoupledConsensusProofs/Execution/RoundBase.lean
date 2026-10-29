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

/-- Minimality of the first included paper round places every older action's
whole delay before the boundary (PROTOCOL.md `sec:healing-schedule`). -/
theorem first_round_older_deadline_before (S : Setup V) (b0 : Time) (r : Round)
    (hmin : ∀ q : Round, 0 < q → b0 ≤ S.a q → r ≤ q)
    (v : V) (q : Round) (hq : q + 1 < r) :
    (S.node v).act q + S.E.Δ < b0 := by
  have hpaper : S.a (q + 1) < b0 := by
    apply lt_of_not_ge
    intro hb
    exact (not_le_of_gt hq) (hmin (q + 1) (Nat.zero_lt_succ q) hb)
  exact lt_trans (S.act_deadline_lt_next_a v q) hpaper

/-- A prior-round emission at or after the first boundary can only belong
to the immediately preceding round; its P2 deadline is no later than the
first G2 read cutoff (PROTOCOL.md `sec:grades`). -/
theorem first_round_straggler_fields (S : Setup V) (rho : NamedRun V)
    (b0 : Time) (r : Round)
    (hmin : ∀ q : Round, 0 < q → b0 ≤ S.a q → r ≤ q)
    {v : V} {a : NamedAttestation V} {t : Time}
    (hem : NamedRun.emits S rho v (.attest a) t)
    (hb : b0 ≤ t) (har : a.round < r) :
    a.round + 1 = r ∧ t + S.E.Δ ≤ early S.E S.hc r .g2 := by
  have ht := (WindowAction.run_emission_fields S hem).1
  have hr : a.round + 1 = r := by
    by_contra hne
    have hlt : a.round + 1 < r := Nat.lt_of_le_of_ne (Nat.succ_le_of_lt har) hne
    have hbefore := first_round_older_deadline_before S b0 r hmin v a.round hlt
    rw [← ht] at hbefore
    have hd := S.E.Δ_pos
    linarith
  refine ⟨hr, ?_⟩
  rw [ht]
  simpa only [hr] using S.act_pre_cutoff v a.round

/-- Any receipt satisfying the strict network delay reaches the next early
G2 cutoff in time, including a boundary-straddling send
(PROTOCOL.md `sec:grades`). -/
theorem first_round_straggler_receipt_before (S : Setup V) (rho : NamedRun V)
    (b0 : Time) (r : Round)
    (hmin : ∀ q : Round, 0 < q → b0 ≤ S.a q → r ≤ q)
    {v : V} {a : NamedAttestation V} {t received : Time}
    (hem : NamedRun.emits S rho v (.attest a) t)
    (hb : b0 ≤ t) (har : a.round < r) (hdelay : received < t + S.E.Δ) :
    received < early S.E S.hc r .g2 :=
  lt_of_lt_of_le hdelay (first_round_straggler_fields S rho b0 r hmin hem hb har).2

/-- After GST, broadcast synchrony supplies an actual straggler receipt
before the cutoff when the deadline is covered and the object is not excluded
(PROTOCOL.md `sec:public-handlers`). -/
theorem first_round_straggler_handles_after_gst (S : Setup V) (rho : NamedRun V)
    (syn : NamedSynchrony S rho) (b0 : Time) (r : Round)
    (hmin : ∀ q : Round, 0 < q → b0 ≤ S.a q → r ≤ q)
    {v w : V} {a : NamedAttestation V} {t : Time}
    (hv : v ∈ rho.honest) (hw : w ∈ rho.honest)
    (hem : NamedRun.emits S rho v (.attest a) t)
    (hb : b0 ≤ t) (har : a.round < r) (hgst : S.E.t_GST ≤ t)
    (hhor : t + S.E.Δ ≤ rho.horizon)
    (hexcl : NamedReceipt.excludes
      (NamedRun.stateBeforeTime S rho (t + S.E.Δ) w).st (.attest a) = false) :
    ∃ received : Time, t ≤ received ∧ received < early S.E S.hc r .g2 ∧
      ∃ j : Nat, NamedRun.actualHandlesAt S rho j w (.attest a) received := by
  have hmax : max t S.E.t_GST = t := max_eq_left hgst
  obtain ⟨received, hlo, hhi, j, hcall⟩ := syn.broadcast v hv (.attest a) t hem w hw
    (by simpa only [hmax] using hhor) (by simpa only [hmax] using hexcl)
  rw [hmax] at hhi
  exact ⟨received, hlo,
    first_round_straggler_receipt_before S rho b0 r hmin hem hb har hhi, j, hcall⟩

/-- With the paper schedule there are no first-round stragglers, so the
second case of the classification is empty (PROTOCOL.md `sec:healing-schedule`). -/
theorem first_round_no_stragglers_point (S : Setup V) (rho : NamedRun V)
    (b0 : Time) (r : Round)
    (hmin : ∀ q : Round, 0 < q → b0 ≤ S.a q → r ≤ q)
    (hpoint : ∀ v q, (S.node v).act q = S.a q)
    (hfirst : S.a (r - 1) < b0)
    {v : V} {a : NamedAttestation V} {t : Time}
    (hem : NamedRun.emits S rho v (.attest a) t)
    (hb : b0 ≤ t) (har : a.round < r) : False := by
  have hr := (first_round_straggler_fields S rho b0 r hmin hem hb har).1
  have ht := (WindowAction.run_emission_fields S hem).1
  rw [ht, hpoint] at hb
  rw [← hr, Nat.add_sub_cancel] at hfirst
  exact (not_lt_of_ge hb) hfirst

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
#print axioms first_round_older_deadline_before
#print axioms first_round_straggler_fields
#print axioms first_round_straggler_receipt_before
#print axioms first_round_straggler_handles_after_gst
#print axioms first_round_no_stragglers_point
end DecoupledConsensusModel.Proofs.NamedOutageClosure
