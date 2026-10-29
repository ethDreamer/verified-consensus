module
public import DecoupledConsensusProofs.Execution.RoundBase
public import DecoupledConsensusProofs.Execution.ExcludesRefute
public import DecoupledConsensusProofs.Protocol.Grades.FrameForward

/-!
# The frozen frame of a first-round straggler

The first included round's predecessor already has its pre-boundary G2
certificate. That certificate persists along the emitter's own timeline to
its actual action, up to finality clipping (PROTOCOL.md `sec:grades`).
Turning this raw certificate into a voting floor additionally uses the
consuming store's FG viability and finality compatibility.
-/

@[expose] public section
namespace DecoupledConsensusModel.Proofs.NamedOutageClosure
open Execution Protocol Internal.NamedStableChainOutage

variable {V : Type} [DecidableEq V] [Fintype V]

/-- A straggler is in the range of the existing pre-boundary frame clause:
its paper instant is before the boundary, and its round follows the stable
round (PROTOCOL.md `sec:healing-schedule`). -/
theorem straggler_preBoundary_round (S : Setup V) (rho : NamedRun V)
    (b0 : Time) (s r : Round)
    (hmargin : FormationMargin S s b0)
    (hmin : ∀ q : Round, 0 < q → b0 ≤ S.a q → r ≤ q)
    (hfirst : S.a (r - 1) < b0)
    {v : V} {a : NamedAttestation V} {t : Time}
    (hem : NamedRun.emits S rho v (.attest a) t)
    (hb : b0 ≤ t) (har : a.round < r) :
    s + 1 ≤ a.round ∧ S.a a.round < b0 := by
  have hpred := (first_round_straggler_fields S rho b0 r hmin hem hb har).1
  have hpaper : S.a a.round < b0 := by
    simpa only [← hpred, Nat.add_sub_cancel] using hfirst
  refine ⟨?_, hpaper⟩
  by_contra hn
  have hle : a.round + 1 ≤ s + 1 :=
    Nat.succ_le_succ (Nat.lt_succ_iff.mp (Nat.lt_of_not_ge hn))
  have ht := (WindowAction.run_emission_fields S hem).1
  have hdeadline := S.act_deadline_lt_next_a v a.round
  have hmono := Assembly.a_mono S hle
  change S.a (s + 1) + S.E.Δ ≤ b0 at hmargin
  rw [← ht] at hdeadline
  have hd := S.E.Δ_pos
  linarith

/-- The pre-boundary frame hypothesis supplies the straggler's own opening
certificate, without an included-round invariant (PROTOCOL.md `sec:grades`). -/
theorem straggler_opening_frame (S : Setup V) (rho : NamedRun V)
    (b0 : Time) (s r : Round) (P : NamedBlock V)
    (hmargin : FormationMargin S s b0)
    (hmin : ∀ q : Round, 0 < q → b0 ≤ S.a q → r ≤ q)
    (hfirst : S.a (r - 1) < b0)
    (hframes : PreBoundaryFrames S rho b0 s P.erase)
    {v : V} {a : NamedAttestation V} {t : Time} (hv : v ∈ rho.honest)
    (hem : NamedRun.emits S rho v (.attest a) t)
    (hb : b0 ≤ t) (har : a.round < r) :
    let n := NamedRun.readAt S rho (domain S.E S.hc a.round .g1) v
    Block.Preceq P.erase n.st.core.F ∨
      ∃ raw : Block V, (readFrame n.cache n.st.core.toHealing a.round).g2 =
        some (some raw) ∧ Block.Preceq P.erase raw := by
  obtain ⟨hlo, hpaper⟩ := straggler_preBoundary_round S rho b0 s r
    hmargin hmin hfirst hem hb har
  exact hframes v hv a.round hlo hpaper

private theorem readAt_eq_succ (S : Setup V) (rho : NamedRun V) (t : Time) :
    NamedRun.readAt S rho t = NamedRun.stateBeforeTime S rho (t + 1) := by
  have hpred : (fun e : NamedEvent V => decide (e.time ≤ t)) =
      fun e => decide (e.time < t + 1) := by
    funext e
    exact decide_eq_decide.mpr Int.lt_add_one_iff.symm
  unfold NamedRun.readAt NamedRun.stateBeforeTime
  rw [hpred]

/-- Finality and the raw G2 certificate carry to the actual action boundary.
The certificate is clipped at the new finality; its active FG projection is
not asserted here (PROTOCOL.md `sec:grades`). -/
theorem straggler_frame_at_action (S : Setup V) (rho : NamedRun V)
    (core : NamedAdmissibleCore S rho) (b0 : Time) (s r : Round) (P : NamedBlock V)
    (hmargin : FormationMargin S s b0)
    (hmin : ∀ q : Round, 0 < q → b0 ≤ S.a q → r ≤ q)
    (hfirst : S.a (r - 1) < b0)
    (hframes : PreBoundaryFrames S rho b0 s P.erase)
    {v : V} {a : NamedAttestation V} {t : Time} (hv : v ∈ rho.honest)
    (hem : NamedRun.emits S rho v (.attest a) t)
    (hb : b0 ≤ t) (har : a.round < r) :
    let n := NamedRun.stateBeforeTime S rho ((S.node v).act a.round) v
    Block.Preceq P.erase n.st.core.F ∨
      ∃ raw : Block V, Block.Preceq P.erase raw ∧
        (readFrame n.cache n.st.core.toHealing a.round).g2 =
          some (some (clipGrade raw n.st.core.F)) := by
  have hlo : domain S.E S.hc a.round .g1 + 1 ≤ (S.node v).act a.round := by
    have hpost := S.act_post_completion v a.round
    have hd : (1 : Time) ≤ S.E.Δ := Int.add_one_le_iff.mpr S.E.Δ_pos
    simp only [domain, Phase.domainOffset] at hpost ⊢
    linarith
  have hframe := straggler_opening_frame S rho b0 s r P hmargin hmin hfirst
    hframes hv hem hb har
  dsimp only at hframe ⊢
  rw [readAt_eq_succ] at hframe
  rcases hframe with hF | ⟨raw, hraw, hP⟩
  · exact Or.inl (Block.preceq_trans hF
      (stateBeforeTime_F_mono_of_le S rho core.sorted hlo))
  · refine Or.inr ⟨raw, hP, ?_⟩
    exact FrameForward.frame_phase_persists_in_round S rho core v a.round .g2
      (domain S.E S.hc a.round .g1 + 1) ((S.node v).act a.round) hlo
      (S.act_before_round_end v a.round).le (some raw) hraw

#print axioms straggler_preBoundary_round
#print axioms straggler_opening_frame
#print axioms straggler_frame_at_action
end DecoupledConsensusModel.Proofs.NamedOutageClosure
end
