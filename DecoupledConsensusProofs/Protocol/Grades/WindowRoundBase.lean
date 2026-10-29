module
public import DecoupledConsensusProofs.Protocol.Grades.WindowSGFloor

/-!
# Casewise post-boundary head coverage

The first included round uses older-round vacuity and the derived straggler
floor. Later rounds split off those same stragglers before using their
included-round induction hypothesis. Reads and delivery deadlines stay fixed
(PROTOCOL.md `sec:healing-schedule`).
-/
@[expose] public section
namespace DecoupledConsensusModel.Proofs.NamedOutageClosure
open Execution Protocol Internal.NamedJointOutage Internal.NamedStableChainOutage
open Internal.NamedOutageEntry
variable {V : Type} [DecidableEq V] [Fintype V]

/-- The first-round post-boundary clause is vacuous through `r - 2`;
its remaining case uses the causal straggler floor, with no receipt bound
(PROTOCOL.md `sec:grades`). -/
theorem first_round_hpost
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time) (s r : Round) (P : NamedBlock V)
    (hexec : OutageExecution S rho b0 b1) (hmargin : FormationMargin S s b0)
    (hsleep : OutageSleepyThroughout S rho) (hP : NamedRun.blockInRun S rho P)
    (hno : NoHonestConflictAbove S rho b0 P.erase)
    (hmin : ∀ q : Round, 0 < q → b0 ≤ S.a q → r ≤ q)
    (hfirst : S.a (r - 1) < b0) (hframes : PreBoundaryFrames S rho b0 s P.erase)
    (hheld0 : ∀ v ∈ rho.honest, P ∈ (NamedRun.stateBeforeTime S rho b0 v).st.bodies) :
    ∀ (a : NamedAttestation V) (t : Time), a.val_index ∈ rho.honest →
      NamedRun.emits S rho a.val_index (.attest a) t → b0 ≤ t → a.round < r →
      ∀ key, a.confirmed = some key →
        ∀ K : NamedBlock V, NamedRun.blockInRun S rho K → K.root = key →
          Block.Preceq P.erase K.erase := by
  intro a t ha hem hb har key hkey K hK hroot
  by_cases hold : a.round + 1 < r
  · have hd := first_round_older_deadline_before S b0 r hmin a.val_index a.round hold
    have ht := (WindowAction.run_emission_fields S hem).1
    rw [← ht] at hd
    have hdelay := S.E.Δ_pos
    exfalso
    linarith
  · have hstraggler : a.round + 1 = r :=
      Nat.le_antisymm (Nat.succ_le_of_lt har) (Nat.le_of_not_gt hold)
    exact NamedWindowSGFloor.straggler_confirmed_head_floor S rho b0 b1 s r P
      hexec hmargin hsleep hP hno hmin hfirst hframes hheld0 ha hem hb
      (Nat.lt_of_lt_of_eq (Nat.lt_succ_self _) hstraggler) key hkey K hK hroot

/-- With `act = S.a`, both receipt arms are vacuous and the original base
hypothesis gives the unchanged head-coverage conclusion
(PROTOCOL.md `sec:healing-schedule`). -/
theorem first_round_hpost_point
    (S : Setup V) (rho : NamedRun V) (b0 : Time) (r : Round) (P : NamedBlock V)
    (hmin : ∀ q : Round, 0 < q → b0 ≤ S.a q → r ≤ q)
    (hfirst : S.a (r - 1) < b0) (hpoint : ∀ v q, (S.node v).act q = S.a q) :
    ∀ (a : NamedAttestation V) (t : Time), a.val_index ∈ rho.honest →
      NamedRun.emits S rho a.val_index (.attest a) t → b0 ≤ t → a.round < r →
      ∀ key, a.confirmed = some key →
        ∀ K : NamedBlock V, NamedRun.blockInRun S rho K → K.root = key →
          Block.Preceq P.erase K.erase := by
  intro a t _ha hem hb har
  exact (first_round_no_stragglers_point S rho b0 r hmin hpoint hfirst hem hb har).elim

/-- A post-boundary emission either belongs to the first-round straggler
case or to an included round. Actual ticks supply the opening horizon bound;
they need not put that round's paper checkpoint inside the horizon
(PROTOCOL.md `sec:healing-schedule`). -/
theorem hpost_of_first_round_and_included
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time) (s r0 r : Round) (P : NamedBlock V)
    (hexec : OutageExecution S rho b0 b1) (hmargin : FormationMargin S s b0)
    (hsleep : OutageSleepyThroughout S rho) (hP : NamedRun.blockInRun S rho P)
    (hno : NoHonestConflictAbove S rho b0 P.erase)
    (hr0 : DomainIncluded S rho b0 r0)
    (hmin : ∀ q : Round, 0 < q → b0 ≤ S.a q → r0 ≤ q)
    (hfirst : S.a (r0 - 1) < b0) (hframes : PreBoundaryFrames S rho b0 s P.erase)
    (hheld0 : ∀ v ∈ rho.honest, P ∈ (NamedRun.stateBeforeTime S rho b0 v).st.bodies)
    (hincluded : ∀ (a : NamedAttestation V) (t : Time),
      DomainIncluded S rho b0 a.round → a.round < r → a.val_index ∈ rho.honest →
      NamedRun.emits S rho a.val_index (.attest a) t → b0 ≤ t →
      ∀ key, a.confirmed = some key →
        ∀ K : NamedBlock V, NamedRun.blockInRun S rho K → K.root = key →
          Block.Preceq P.erase K.erase) :
    ∀ (a : NamedAttestation V) (t : Time), a.val_index ∈ rho.honest →
      NamedRun.emits S rho a.val_index (.attest a) t → b0 ≤ t → a.round < r →
      ∀ key, a.confirmed = some key →
        ∀ K : NamedBlock V, NamedRun.blockInRun S rho K → K.root = key →
          Block.Preceq P.erase K.erase := by
  intro a t ha hem hb har
  by_cases hprior : a.round < r0
  · exact first_round_hpost S rho b0 b1 s r0 P hexec hmargin hsleep hP hno
      hmin hfirst hframes hheld0 a t ha hem hb hprior
  · have hge := Nat.le_of_not_gt hprior
    have ht := (WindowAction.run_emission_fields S hem).1
    obtain ⟨i, hi, hmem⟩ := hem
    have hhor : t ≤ rho.horizon :=
      (hexec.core.in_horizon _ (List.mem_iff_getElem?.mpr ⟨i, hi⟩)).2
    have hopen : domain S.E S.hc a.round .g1 ≤ (S.node a.val_index).act a.round := by
      have hpost := S.act_post_completion a.val_index a.round
      have hd := S.E.Δ_pos
      simp only [domain, Phase.domainOffset] at hpost ⊢
      linarith
    have hinc : DomainIncluded S rho b0 a.round :=
      ⟨lt_of_lt_of_le hr0.1 hge, hr0.2.1.trans (Assembly.a_mono S hge),
        hopen.trans (ht ▸ hhor)⟩
    exact hincluded a t hinc har ha ⟨i, hi, hmem⟩ hb

#print axioms first_round_hpost
#print axioms first_round_hpost_point
#print axioms hpost_of_first_round_and_included
end DecoupledConsensusModel.Proofs.NamedOutageClosure
