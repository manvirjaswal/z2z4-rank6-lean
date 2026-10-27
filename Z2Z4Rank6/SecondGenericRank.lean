import Z2Z4Rank6.SecondFunctionFieldSpecialization
import Z2Z4Rank6.SecondTorsionCriterion
import Z2Z4Rank6.SingularFibers
import Mathlib.LinearAlgebra.Dimension.Basic

/-!
# Generic independence and torsion inclusion in the second family

The six specified generic points are independent. Every smooth rational
fiber contains the explicit torsion subgroup. Source: Jaswal, Theorem 8.1(b),(c),
DOI 10.5281/zenodo.23437117.
-/

namespace Z2Z4Rank6
open SecondFamily
noncomputable section
open scoped Classical

/-- Theorem 8.1(b): the six specified generic points are
integer-linearly independent and their group has rank at least six. -/
theorem theorem_8_1_b (hMazur : MazurTorsionTheorem)
    (hReduction : GoodReductionHomomorphisms) (hFormal : FormalGoodReductionHomomorphisms) :
    LinearIndependent ℤ SecondFunctionField.points ∧
      6≤Module.rank ℤ (F SecondFunctionField.W).toAffine.Point := by
  have h := SecondFunctionField.points_independent hMazur hReduction hFormal
  exact ⟨h,by simpa using h.cardinal_le_rank⟩

/-- At every smooth second-family fiber, its rational torsion
subgroup contains Z/2×Z/4. -/
theorem second_torsion_contains_of_good (P : G2Point ℚ) (hP : GoodCurve (F P.W)) :
    TorsionContains (F P.W) := by
  have he := SecondTorsionCofinite.F_split_G2 P
  rw [he] at hP ⊢
  exact E_torsion_two_four_inclusion _ _ ((E_good_iff _ _).mp hP)

end
end Z2Z4Rank6
