import DecoupledConsensusProofs.Protocol.Grades.HonestArrival

/-!
Grade-view diagnostic: non-equivocation and delivery timing alone do not make
an added row harmless. This is not a run satisfying the outage regime, and it
does not assert that its newer confirmed head is an honest duty's output.
The missing execution-level fact is precisely that head's coverage of P.
-/
open DecoupledConsensusModel Protocol
namespace VoteWindowStragglerCoverage

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
def older : SGVote (Fin 1) := ⟨0, 1, some P.root⟩
def straggler : SGVote (Fin 1) := ⟨0, 2, some (Block.genesis (V := Fin 1)).root⟩

def before : GradeView (Fin 1) where
  T := {Block.genesis, P}
  timestamp_block := fun _ => some (0 : Time)
  tree := {Block.genesis, P}
  sg_votes := fun q => if q = 1 then {older} else ∅
  timestamp_sg_vote := fun a => if a = older then some (23 : Time) else none

def after (received : Time) : GradeView (Fin 1) :=
  { before with
    sg_votes := fun q => if q = 2 then {straggler} else before.sg_votes q
    timestamp_sg_vote := fun a =>
      if a = straggler then some received else before.timestamp_sg_vote a }

theorem eligible_and_clean :
    straggler.round + 1 = 3 ∧
    straggler.round ∈ latest_window hc.η_SG 3 ∧
    CleanFrom (rawView (after 39) hc.η_SG 3 (late E hc 3 .g2) 0) 0 ∧
    Block.compatible P (Block.genesis (V := Fin 1)) = true := by
  unfold CleanFrom
  decide +kernel

theorem delivery_arms :
    39 + E.Δ ≤ early E hc 3 .g2 ∧
    (39 : Time) < 39 + E.Δ ∧
    early E hc 3 .g2 ≤ 45 ∧
    (45 : Time) < max 39 E.t_GST + E.Δ ∧
    (45 : Time) < late E hc 3 .g2 := by decide +kernel

theorem supported_before :
    positive before .genesis hc.η_SG 3 (early E hc 3 .g2) (late E hc 3 .g2) 0 P = true ∧
    opposing before .genesis hc.η_SG 3 (early E hc 3 .g2) (late E hc 3 .g2) 0 P = false ∧
    gradeBool E before .genesis hc.η_SG 3 (early E hc 3 .g2) (late E hc 3 .g2) P = true := by
  decide +kernel

theorem timely_arrival_loses_grade :
    positive (after 39) .genesis hc.η_SG 3 (early E hc 3 .g2) (late E hc 3 .g2) 0 P = false ∧
    opposing (after 39) .genesis hc.η_SG 3 (early E hc 3 .g2) (late E hc 3 .g2) 0 P = true ∧
    gradeBool E (after 39) .genesis hc.η_SG 3 (early E hc 3 .g2) (late E hc 3 .g2) P = false := by
  decide +kernel

theorem delayed_arrival_loses_grade :
    positive (after 45) .genesis hc.η_SG 3 (early E hc 3 .g2) (late E hc 3 .g2) 0 P = false ∧
    opposing (after 45) .genesis hc.η_SG 3 (early E hc 3 .g2) (late E hc 3 .g2) 0 P = true ∧
    gradeBool E (after 45) .genesis hc.η_SG 3 (early E hc 3 .g2) (late E hc 3 .g2) P = false := by
  decide +kernel

#print axioms eligible_and_clean
#print axioms delivery_arms
#print axioms supported_before
#print axioms timely_arrival_loses_grade
#print axioms delayed_arrival_loses_grade
end VoteWindowStragglerCoverage
