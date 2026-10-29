module
public import DecoupledConsensusProofs.Protocol.Grades.Inclusions
public import DecoupledConsensusProofs.Protocol.Grades.WindowRoundBase

/-!
# Straggler arrivals in an actual ready view

Resolve new ready tokens at the reader's own store, trace their honest
emissions, and apply the derived straggler floor. Neither the strict-delay
arm nor the outage-delay arm needs an extra receipt deadline
(PROTOCOL.md `sec:grades`).
-/
@[expose] public section
namespace DecoupledConsensusModel.Proofs.NamedOutageClosure
open Execution Protocol Internal.NamedJointOutage Internal.NamedStableChainOutage
open Internal.NamedOutageEntry
variable {V : Type} [DecidableEq V] [Fintype V]

/-- Ready straggler additions preserve support and introduce no opposition.
The difference between the old and new views supplies only their straggler
classification; provenance, head resolution and non-equivocation are derived
from the actual reader and sender (PROTOCOL.md `sec:grades`). -/
theorem straggler_ready_arrival_preserves
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time) (s r0 : Round) (P : NamedBlock V)
    (hexec : OutageExecution S rho b0 b1) (hmargin : FormationMargin S s b0)
    (hsleep : OutageSleepyThroughout S rho) (hP : NamedRun.blockInRun S rho P)
    (hno : NoHonestConflictAbove S rho b0 P.erase)
    (hmin : ∀ q : Round, 0 < q → b0 ≤ S.a q → r0 ≤ q)
    (hfirst : S.a (r0 - 1) < b0) (hframes : PreBoundaryFrames S rho b0 s P.erase)
    (hheld0 : ∀ v ∈ rho.honest, P ∈ (NamedRun.stateBeforeTime S rho b0 v).st.bodies)
    (cut ec lc : Time) (r : Round) (reader u : V)
    (hreader : reader ∈ rho.honest) (hu : u ∈ rho.honest)
    (oldEarly oldLate oldRaw : Finset (Token (Option BlockId)))
    (he : oldEarly ⊆ readyView
      (NamedRun.stateBeforeTime S rho cut reader).st.core.toHealing.gradeView
      (NamedRun.stateBeforeTime S rho cut reader).st.core.F S.hc.η_SG r ec u)
    (hel : readyView (NamedRun.stateBeforeTime S rho cut reader).st.core.toHealing.gradeView
      (NamedRun.stateBeforeTime S rho cut reader).st.core.F S.hc.η_SG r ec u ⊆
      readyView (NamedRun.stateBeforeTime S rho cut reader).st.core.toHealing.gradeView
        (NamedRun.stateBeforeTime S rho cut reader).st.core.F S.hc.η_SG r lc u)
    (her : readyView (NamedRun.stateBeforeTime S rho cut reader).st.core.toHealing.gradeView
      (NamedRun.stateBeforeTime S rho cut reader).st.core.F S.hc.η_SG r ec u ⊆
      rawView (NamedRun.stateBeforeTime S rho cut reader).st.core.toHealing.gradeView
        S.hc.η_SG r lc u)
    (hnew : ∀ z ∈ interpretedInputs
      (NamedRun.stateBeforeTime S rho cut reader).st.core.toHealing.gradeView
      (NamedRun.stateBeforeTime S rho cut reader).st.core.F S.hc.η_SG r lc u,
      token z ∉ oldLate → b0 ≤ (S.node u).act z.round ∧ z.round < r0) :
    let gv := (NamedRun.stateBeforeTime S rho cut reader).st.core.toHealing.gradeView
    let F := (NamedRun.stateBeforeTime S rho cut reader).st.core.F
    (Supports (fun k B => localCovers gv k B = true) oldEarly oldLate oldRaw P.erase →
      Supports (fun k B => localCovers gv k B = true)
        (readyView gv F S.hc.η_SG r ec u) (readyView gv F S.hc.η_SG r lc u)
        (rawView gv S.hc.η_SG r lc u) P.erase) ∧
    (Opposes (fun k B => localCovers gv k B = true)
        (readyView gv F S.hc.η_SG r ec u) (readyView gv F S.hc.η_SG r lc u)
        (rawView gv S.hc.η_SG r lc u) P.erase →
      Opposes (fun k B => localCovers gv k B = true) oldEarly oldLate oldRaw P.erase) := by
  let sch := hexec.core.toNamedScheduleWellFormed
  let auth := hexec.core.toNamedUnforgeable
  apply NamedWindowSGFloor.straggler_arrival_preserves S rho b0 b1 s r0 P
    hexec hmargin hsleep hP hno hmin hfirst hframes hheld0 _ he hel her
  · intro x hx hn
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨a, hav, har, hap, _, _, hem⟩ :=
      rawInputs_trace S rho sch auth cut lc reader S.hc.η_SG r u hu
        (Finset.mem_filter.mp hz).1
    obtain ⟨hb, hround⟩ := hnew z hz hn
    obtain ⟨_, _, _, H, _, hkey⟩ := NamedOutageInputs.emitted_attestation_head S rho hem
    have hzconf : z.confirmed = some H.root := by
      rw [← hap, sgVote_confirmed, hkey]
    have hready := (Finset.mem_filter.mp hz).2
    obtain ⟨B, hfind⟩ : ∃ B, Block.find?
        (NamedRun.stateBeforeTime S rho cut reader).st.core.T H.root = some B := by
      cases hf : Block.find? (NamedRun.stateBeforeTime S rho cut reader).st.core.T H.root with
      | some B => exact ⟨B, rfl⟩
      | none =>
        simp only [bodyReady, hzconf, HealingStore.gradeView, Store.toHealing, hf] at hready
        cases hready
    have hm := HealingLemmas.find?_mem hfind
    have hcoh := (NamedRuntime.stateBeforeTime_invariants S rho cut reader).1.1.1
    rw [hcoh.1] at hm
    obtain ⟨K, hK, hKe⟩ := Finset.mem_image.mp hm
    have hKrun := held_blockInRun S rho sch reader hreader cut hK
    have hKr : K.root = H.root := by
      rw [← NamedWire.erase_root K, hKe]
      exact HealingLemmas.find?_root hfind
    refine ⟨a, (S.node a.val_index).act a.round, H.root, K, hav ▸ hu, ?_, ?_, ?_,
      hkey, hzconf, hKrun, hKr, ?_⟩
    · simpa only [hav] using hem
    · simpa only [hav, har] using hb
    · simpa only [har] using hround
    · simpa only [HealingStore.gradeView, Store.toHealing, hKe] using hfind
  · intro x hx y hy _ hround
    simp only [rawView, Finset.mem_image] at hx hy
    obtain ⟨zx, hx, rfl⟩ := hx
    obtain ⟨zy, hy, rfl⟩ := hy
    obtain ⟨a, _, har, hap, _, _, ha⟩ := rawInputs_trace S rho sch auth cut lc
      reader S.hc.η_SG r u hu hx
    obtain ⟨b, _, hbr, hbp, _, _, hb⟩ := rawInputs_trace S rho sch auth cut lc
      reader S.hc.η_SG r u hu hy
    have hab := NamedOutageProvenance.emitted_same_round_unique S rho sch ha hb
      (by rw [har, hbr]; exact hround)
    change zx.confirmed = zy.confirmed
    rw [← hap, ← hbp, hab]

#print axioms straggler_ready_arrival_preserves
end DecoupledConsensusModel.Proofs.NamedOutageClosure
