module
public import DecoupledConsensusProofs.Protocol.Grades.GradeCutoffMono

/-!
# Coverage under additional honest evidence

The grade predicate inspects the newest evidence as well as the early witness.
Growing the views preserves support when new ready tokens cover the protected
block and the sender remains non-equivocating (PROTOCOL.md `sec:grades`).
-/

@[expose] public section
namespace DecoupledConsensusModel.Proofs.HonestArrival
open Protocol

variable {Key Blk : Type*}

/-- Adding covering evidence from a non-equivocating sender preserves support,
whether the evidence enters the early view or only the late view
(PROTOCOL.md `sec:grades`). -/
theorem supports_of_covering_arrivals (covers : Key → Blk → Prop)
    {early late raw early' late' raw' : Finset (Token Key)} {B : Blk}
    (he : early ⊆ early') (hel : early' ⊆ late')
    (her : early' ⊆ raw')
    (hnew : ∀ x ∈ late', x ∉ late → covers x.key B)
    (hclean : CleanFrom raw' 0)
    (hs : Supports covers early late raw B) :
    Supports covers early' late' raw' B := by
  obtain ⟨u, hu, _, hcov, _, hsweep⟩ := hs
  obtain ⟨v, hv, hmax⟩ := Finset.exists_max_image early' (fun x => x.round) ⟨u, he hu⟩
  have huv : u.round ≤ v.round := hmax u (he hu)
  refine ⟨v, hv, hmax, ?_, ?_, ?_⟩
  · by_cases hvl : v ∈ late
    · rcases lt_or_eq_of_le huv with hlt | heq
      · exact hsweep v hvl hlt
      · have hk := hclean u (her (he hu)) v (her hv) (Nat.zero_le _) heq
        exact hk ▸ hcov
    · exact hnew v (hel hv) hvl
  · intro x hx y hy _ hxy
    exact hclean x hx y hy (Nat.zero_le _) hxy
  · intro x hx hvx
    by_cases hxl : x ∈ late
    · exact hsweep x hxl (lt_of_le_of_lt huv hvx)
    · exact hnew x hx hxl

/-- New covering tokens from a non-equivocating sender cannot introduce an
opponent. No bound on their arrival time is needed (PROTOCOL.md `sec:grades`). -/
theorem opposes_before_of_covering_arrivals (covers : Key → Blk → Prop)
    {early late raw early' late' raw' : Finset (Token Key)} {B : Blk}
    (he : early ⊆ early')
    (hnew : ∀ x ∈ late', x ∉ late → covers x.key B)
    (hclean : CleanFrom raw' 0)
    (ho : Opposes covers early' late' raw' B) :
    Opposes covers early late raw B := by
  rcases ho with ⟨x, hx, hmax, hnot⟩ | ⟨x, hx, y, hy, _, hround, hkey⟩
  · have hxl : x ∈ late := by
      by_contra hn
      exact hnot (hnew x hx hn)
    exact Or.inl ⟨x, hxl, fun u hu => hmax u (he hu), hnot⟩
  · exact False.elim (hkey (hclean x hx y hy (Nat.zero_le _) hround))

#print axioms supports_of_covering_arrivals
#print axioms opposes_before_of_covering_arrivals
end DecoupledConsensusModel.Proofs.HonestArrival
end
