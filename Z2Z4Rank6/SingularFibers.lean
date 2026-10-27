module

public import Z2Z4Rank6.Torsion
public import Z2Z4Rank6.BaseSingular
public import Z2Z4Rank6.Statements
public import Mathlib.Data.Rat.Lemmas
public import Mathlib.Tactic

@[expose] public section

/-!
# Singular fibers and torsion inclusion

The rational singular-parameter calculation in Section 2 and the first clause
of Theorem 1.2(c) of Manvir Jaswal, "Infinitely many elliptic curves with
torsion Z/2Z × Z/4Z and rank at least six",
DOI: 10.5281/zenodo.23437117.
-/

namespace Z2Z4Rank6

theorem E_good_iff (α β : ℚ) :
    GoodCurve (E α β) ↔ α * β * (α ^ 2 - β ^ 2) ≠ 0 := by
  constructor
  · intro hg hz
    apply hg.isUnit.ne_zero
    rw [E_discriminant]
    rcases mul_eq_zero.mp hz with hab | hdiff
    · rcases mul_eq_zero.mp hab with ha | hb
      · rw [ha]
        ring
      · rw [hb]
        ring
    · rw [hdiff]
      ring
  · exact E_good α β

theorem a_sub_b_eq (m : ℚ) :
    a m - b m = 14 * ((m ^ 2 - 1) ^ 2 + 9800) := by simp only [a, b]; ring

theorem a_add_b_eq (m : ℚ) :
    a m + b m = -1400 * m * (m ^ 2 - 99) := by simp only [a, b]; ring

theorem a_sub_b_pos (m : ℚ) : 0 < a m - b m := by rw [a_sub_b_eq]; positivity

theorem parameter_sq_ne_ninetynine (m : ℚ) : m ^ 2 - 99 ≠ 0 := by
  intro hm
  have hs : IsSquare (99 : ℚ) := ⟨m, by nlinarith⟩
  norm_num at hs

theorem a_sq_sub_b_sq_ne_zero_iff (m : ℚ) :
    a m ^ 2 - b m ^ 2 ≠ 0 ↔ m ≠ 0 := by
  rw [show a m ^ 2 - b m ^ 2 = (a m - b m) * (a m + b m) by ring,
    mul_ne_zero_iff, and_iff_right (ne_of_gt (a_sub_b_pos m)), a_add_b_eq]
  constructor
  · intro h
    exact (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp h).1).2
  · intro hm
    exact mul_ne_zero (mul_ne_zero (by norm_num) hm) (parameter_sq_ne_ninetynine m)

private theorem rational_add_ne_zero (x y : ℚ) : x + y ≠ 0 ↔ x ≠ -y := by
  constructor <;> intro h hn <;> apply h <;> linarith

theorem family_discriminant_factor_nonzero_iff (m : ℚ) :
    a m * b m * (a m ^ 2 - b m ^ 2) ≠ 0 ↔ ¬singularParameter m := by
  rw [mul_ne_zero_iff, a_sq_sub_b_sq_ne_zero_iff]
  simp only [a, b, singularParameter, Finset.mem_insert, Finset.mem_singleton,
    not_or, mul_ne_zero_iff, sub_ne_zero, rational_add_ne_zero]
  norm_num
  tauto

/-- Over Q the singular fibers are exactly m=0,±1,±9,±11,±99. -/
theorem X_good_iff_not_singular_parameter (m : ℚ) :
    GoodCurve (X m) ↔ ¬singularParameter m :=
  (E_good_iff (a m) (b m)).trans (family_discriminant_factor_nonzero_iff m)

theorem exceptionalPoints_eq_singularCPoints : exceptionalPoints = (singularCPoints : Set CPoint) := by
  ext c
  exact (mem_singularCPoints_iff c).symm

theorem exceptionalPoints_finite : exceptionalPoints.Finite := by
  rw [exceptionalPoints_eq_singularCPoints]
  exact singularCPoints.finite_toSet

theorem exceptionalPoints_card : exceptionalPoints.ncard = 16 := by
  rw [exceptionalPoints_eq_singularCPoints, Set.ncard_coe_finset, singularCPoints_card]

/-- The sixteen printed points are exactly the singular rational
fibers over C, with all signs independent. -/
theorem X_good_iff_not_exceptional (c : CPoint) :
    GoodCurve (X c.m) ↔ c ∉ exceptionalPoints := by
  rw [X_good_iff_not_singular_parameter, singularParameter_iff_exceptional]
  rfl

/-- The first clause of Theorem 1.2(c), with an injection into the
rational torsion subgroup. -/
theorem theorem12c_first_clause (c : CPoint) (hc : c ∉ exceptionalPoints) :
    GoodCurve (X c.m) ∧ TorsionContains (X c.m) := by
  have hg := (X_good_iff_not_exceptional c).2 hc
  have hfactor := (E_good_iff (a c.m) (b c.m)).1 hg
  exact ⟨hg, E_torsion_two_four_inclusion (a c.m) (b c.m) hfactor⟩

end Z2Z4Rank6
