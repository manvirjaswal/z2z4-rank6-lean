module

public import Z2Z4Rank6.ECFullSelmerModel
public import Mathlib.Data.Finset.Max

@[expose] public section

/-!
# Local projective normalization for the full two-descent certificates

Every nonzero local solution of the two homogeneous quadrics can be
scaled to integral coordinates with one coordinate 1. Its reduction therefore
passes the finite square-residue test of `ECFullSelmerModel`.
-/

namespace Z2Z4Rank6

section Prime

variable {p : ℕ} [Fact p.Prime]

theorem splitCover_integral_normalization (d : ECFullTriple)
    (h : SplitCoverSoluble (d.1 : ℚ_[p]) (d.2.1 : ℚ_[p]) (d.2.2 : ℚ_[p]) 729 484) :
    ∃ z : Fin 4 → ℤ_[p], (∃ i, z i = 1) ∧
      (d.2.1 : ℤ_[p])*(z 1)^2-(d.1 : ℤ_[p])*(z 0)^2=729*(z 3)^2 ∧
      (d.2.2 : ℤ_[p])*(z 2)^2-(d.1 : ℤ_[p])*(z 0)^2=484*(z 3)^2 := by
  classical
  obtain ⟨w,hnonzero,h1,h2⟩ := h
  obtain ⟨i,_,hi⟩ := Finset.exists_max_image Finset.univ (fun j => ‖w j‖)
    Finset.univ_nonempty
  have hmax : ∀ j, ‖w j‖ ≤ ‖w i‖ := fun j => hi j (Finset.mem_univ _)
  have hwi : w i ≠ 0 := by
    intro hwi
    obtain ⟨j,hj⟩ := hnonzero
    have hz : ‖w j‖ ≤ 0 := by simpa [hwi] using hmax j
    exact hj (norm_eq_zero.mp (le_antisymm hz (norm_nonneg _)))
  let z : Fin 4 → ℤ_[p] := fun j => ⟨w j/w i, by
    rw [norm_div, div_le_one (norm_pos_iff.mpr hwi)]
    exact hmax j⟩
  refine ⟨z,⟨i,Subtype.ext (div_self hwi)⟩,?_,?_⟩
  · apply Subtype.ext
    change (d.2.1 : ℚ_[p])*(w 1/w i)^2-(d.1 : ℚ_[p])*(w 0/w i)^2=
      729*(w 3/w i)^2
    field_simp
    linear_combination h1
  · apply Subtype.ext
    change (d.2.2 : ℚ_[p])*(w 2/w i)^2-(d.1 : ℚ_[p])*(w 0/w i)^2=
      484*(w 3/w i)^2
    field_simp
    linear_combination h2

theorem splitCover_local_implies_residue_test (k : ℕ) (d : ECFullTriple)
    (h : SplitCoverSoluble (d.1 : ℚ_[p]) (d.2.1 : ℚ_[p]) (d.2.2 : ℚ_[p]) 729 484) :
    splitCoverResiduePossible (p^k) d = true := by
  obtain ⟨z,⟨i,hi⟩,h1,h2⟩ := splitCover_integral_normalization d h
  let q : Fin 4 → ZMod (p^k) := fun j => PadicInt.toZModPow k (z j)
  simp only [splitCoverResiduePossible, List.any_eq_true, decide_eq_true_eq]
  refine ⟨(q 0)^2,square_mem_squareResidues _ _,
    (q 1)^2,square_mem_squareResidues _ _,
    (q 2)^2,square_mem_squareResidues _ _,
    (q 3)^2,square_mem_squareResidues _ _,?_,?_,?_⟩
  · have hq : q i = 1 := by simp [q,hi]
    fin_cases i <;> simp_all
  · have hm := congrArg (PadicInt.toZModPow k) h1
    simpa only [map_sub,map_mul,map_pow,map_intCast,map_ofNat] using hm
  · have hm := congrArg (PadicInt.toZModPow k) h2
    simpa only [map_sub,map_mul,map_pow,map_intCast,map_ofNat] using hm

end Prime

end Z2Z4Rank6
