module
public import DecoupledConsensusProofs.Protocol.Duties.Inputs.WindowIntrinsicEntry
public import DecoupledConsensusProofs.Protocol.Grades.JointHistoryProducers
public import DecoupledConsensusProofs.Execution.BodyRetention

/-!
# Strict pre-tick inventory of height sources

The proposal duty can insert a body before attestation. A height source still
comes from the earlier G2 capture or the live confirmation, which the proposal
duty preserves (PROTOCOL.md `sec:public-handlers`).
-/
@[expose] public section
namespace DecoupledConsensusModel.Proofs.NamedWindowHeightSources
open Execution Protocol Internal.NamedJointOutage NamedActionReads
variable {V : Type} [DecidableEq V] [Fintype V]

private theorem bodies_or_live (S : Setup V) (v : V) (before : NamedNodeState V)
    (t : Time) :
    (windowReadFrom S v before t).st.bodies = before.st.bodies ∨
      (windowReadFrom S v before t).st.core.live_confirmed = before.st.core.live_confirmed := by
  by_cases hp : 0 < S.E.slotOf t ∧ t = proposal_time S.E (S.E.slotOf t) ∧
      S.E.proposer (S.E.slotOf t) = (S.node v).val_index
  · right
    have hn : ¬ (0 < S.E.slotOf t ∧ t = support_cutoff S.E (S.E.slotOf t)) := by
      intro hc
      have hd := S.E.Δ_pos
      have he := hp.2.1.symm.trans hc.2
      simp only [proposal_time, support_cutoff] at he
      linarith
    unfold windowReadFrom
    dsimp only
    rw [ite_eq_left hp, ite_eq_right hn]
    split_ifs <;> simp only [Optimistic.goldfish_vote_with_live_confirmed,
      Optimistic.propose_block_with_live_confirmed, NamedStore.setClock]
  · left
    unfold windowReadFrom
    dsimp only
    rw [ite_eq_right hp]
    split_ifs <;> rfl

/-- The actual Q2 is an ancestor of a body already held before the action. -/
theorem q2_mem_before (S : Setup V) (rho : NamedRun V) (i : Nat) (v : V) (r : Round)
    {q : Block V}
    (hQ : grade2_block_with
      (NamedProfile.gradeContract (windowActionReadFrom S v
        (NamedRun.stateBefore S rho i v) r).cache) S.E S.hc
      (windowActionReadFrom S v (NamedRun.stateBefore S rho i v) r).st.core.toHealing r =
        some q) : q ∈ (NamedRun.stateBefore S rho i v).st.core.T := by
  obtain ⟨j, raw, hj, _, hfreeze, hqraw⟩ :=
    NamedOutageHistory.JointHistoryProducersTime.q2_capture_at_window_read S rho i v r hQ
  have hraw : raw ∈ (NamedRun.stateBefore S rho j v).st.core.T :=
    (Finset.mem_filter.mp (Engine.deepest?_mem
      (by simpa only [freezeRoot, HealingStore.gradeView, Store.toHealing] using hfreeze))).1
  have hjcoh := (NamedRuntime.stateBefore_invariants S rho j v).1.1.1
  rw [hjcoh.1] at hraw
  obtain ⟨B, hB, hBe⟩ := Finset.mem_image.mp hraw
  have hiInv := (NamedRuntime.stateBefore_invariants S rho i v).1
  have hrawi : raw ∈ (NamedRun.stateBefore S rho i v).st.core.T := by
    rw [hiInv.1.1.1, ← hBe]
    exact Finset.mem_image_of_mem _ (NamedBodyRetention.stateBefore_bodies_mono
      S rho v hj.le hB)
  exact NamedStoreRoots.core_ancestor_mem S.E S.cfg _ hiInv.1.1 hrawi hqraw

/-- A signed height source belongs to the strict pre-event inventory, including
when a proposal was processed in the same tick. -/
theorem signed_source_mem_before (S : Setup V) (rho : NamedRun V)
    {i : Nat} {a : NamedAttestation V} {source entry : NamedBlock V}
    (hs : WindowSignedSourceAt S rho i a source entry) :
    source ∈ (NamedRun.stateBefore S rho i a.val_index).st.bodies := by
  let before := NamedRun.stateBefore S rho i a.val_index
  let n := windowActionReadFrom S a.val_index before a.round
  obtain ⟨hi, hem, _, hsource, hsel, _⟩ := hs
  change source ∈ n.st.bodies at hsource
  change fg_source_with (NamedProfile.gradeContract n.cache) S.E S.hc n.st.core.toHealing
    a.round (grade2_block_with (NamedProfile.gradeContract n.cache)
      S.E S.hc n.st.core.toHealing a.round) = some source.erase at hsel
  have hinv := (NamedRuntime.stateBefore_invariants S rho i a.val_index).1
  have hmem : source.erase ∈ before.st.core.T := by
    rcases bodies_or_live S a.val_index before ((S.node a.val_index).act a.round) with hb | hl
    · change n.st.bodies = before.st.bodies at hb
      rw [hinv.1.1.1]
      exact Finset.mem_image_of_mem _ (hb ▸ hsource)
    · change n.st.core.live_confirmed = before.st.core.live_confirmed at hl
      unfold fg_source_with at hsel
      cases hQ : grade2_block_with (NamedProfile.gradeContract n.cache)
          S.E S.hc n.st.core.toHealing a.round with
      | none => simp [hQ] at hsel
      | some q =>
        simp only [hQ] at hsel
        cases hd : deepest_clear (some q) n.st.core.toHealing.live_confirmed
            ((NamedProfile.gradeContract n.cache).read S.E S.hc
              n.st.core.toHealing a.round).clear with
        | none =>
          rw [hd] at hsel
          exact Option.some.inj hsel ▸ q2_mem_before S rho i a.val_index a.round hQ
        | some B =>
          rw [hd] at hsel
          have hpre := Engine.deepest_clear_preceq hd
          change Block.Preceq B n.st.core.live_confirmed at hpre
          rw [Option.some.inj hsel, hl] at hpre
          exact NamedStoreRoots.core_ancestor_mem S.E S.cfg _ hinv.1.1 hinv.2.1 hpre
  rw [hinv.1.1.1] at hmem
  obtain ⟨B, hB, he⟩ := Finset.mem_image.mp hmem
  have hpost := (NamedWindowIntrinsicEntry.emission_post_projection S rho hi hem).1
  have hBpost := NamedBodyRetention.stateBefore_bodies_mono S rho a.val_index
    (Nat.le_succ i) hB
  have hsourcePost : source ∈ (NamedRun.stateBefore S rho (i + 1) a.val_index).st.bodies := by
    rw [hpost]
    exact hsource
  have hcoh := (NamedRuntime.stateBefore_invariants S rho (i + 1) a.val_index).1.1.1
  have hEq : B = source := hcoh.2.1 B hBpost source hsourcePost he
  exact hEq ▸ hB

#print axioms q2_mem_before
#print axioms signed_source_mem_before
end DecoupledConsensusModel.Proofs.NamedWindowHeightSources
