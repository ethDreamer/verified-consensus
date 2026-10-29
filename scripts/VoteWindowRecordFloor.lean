import DecoupledConsensusProofs.Protocol.Grades.StragglerFrame

/-!
Local selector diagnostic, not an outage-run counterexample. The post-state
map below is supplied data; no reachable named store or authenticated carrier
is claimed. The example isolates the viability condition that a causal FG
proof must preserve: retained user records and raw frames alone do not floor
the live confirmation or the attestation head.
-/
open DecoupledConsensusModel Protocol
namespace VoteWindowRecordFloor

def E : Env (Fin 1) where
  Δ := 1
  Δ_pos := by decide
  t_GST := 48
  t_GST_nonneg := by decide
  proposer := fun _ => 0
  committees := ⟨fun _ => Finset.univ⟩
  electorate := { weight := fun _ => 1, weight_pos := by intro v; decide }

def hc : HealConfig := ⟨4, by decide, 2, by decide⟩
def P : Block (Fin 1) := .node .genesis 1 ⟨1⟩ [] [] [] 0
def Q : Block (Fin 1) := .node .genesis 2 ⟨2⟩ [] [] [] 0
def cache : Cache (Fin 1) :=
  ⟨2, ⟨some (some P), some (some P), some (some P)⟩, pendingFrame⟩

def before : Store (Fin 1) :=
  { Store.init with
    t := 38, s := 9, T := {Block.genesis, P}
    timestamp_block := fun _ => some (0 : Time)
    live_confirmed := P, latest_confirmed := P, latest_stable := P }

def raised : Store (Fin 1) :=
  { before with
    t := 42, s := 10, T := {Block.genesis, P, Q}, h_max := 3
    σ := fun B => if B = Q then { ChainState.initial with h := 3 } else before.σ B }

def after : Store (Fin 1) :=
  update_confirmation_with (frameContract cache) E hc raised 9

def vote (st : Store (Fin 1)) : Block (Fin 1) :=
  currentSGVote st.toHealing (frameGradeRead cache E hc st.toHealing 2)

theorem initial_floor :
    P ∈ get_filtered_block_tree before.toHealing.toFG ∧
    vote before = P ∧ before.latest_confirmed = P ∧ before.latest_stable = P := by
  decide +kernel

theorem record_frame_and_finality_retained :
    before.T ⊆ raised.T ∧ before.h_max ≤ raised.h_max ∧
    before.F = raised.F ∧ raised.F = after.F ∧
    after.latest_confirmed = P ∧ after.latest_stable = P ∧
    (readFrame cache after.toHealing 2).g2 = some (some P) ∧
    (readFrame cache after.toHealing 2).g0 = some (some P) ∧
    clear (readFrame cache after.toHealing 2) P = true := by
  decide +kernel

theorem live_floor_lost :
    P ∉ get_filtered_block_tree raised.toHealing.toFG ∧
    after.live_confirmed = Block.genesis ∧ vote after = Block.genesis ∧
    ¬ Block.Preceq P (vote after) := by decide +kernel

theorem same_round_and_support_cutoff :
    hc.round_of before.s = 2 ∧ hc.round_of raised.s = 2 ∧
    raised.t = support_cutoff E raised.s ∧
    (39 : Time) ≤ raised.t ∧
    raised.t + E.Δ ≤ early E hc 3 .g2 := by decide +kernel

#print axioms initial_floor
#print axioms record_frame_and_finality_retained
#print axioms live_floor_lost
#print axioms same_round_and_support_cutoff
end VoteWindowRecordFloor
