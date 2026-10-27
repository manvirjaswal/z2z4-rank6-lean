import Z2Z4Rank6.CParameterCounting
import Z2Z4Rank6.FiniteRemovalCounting
import Z2Z4Rank6.SingularFibers
import Z2Z4Rank6.FiniteImageCounting

/-!
# Counting smooth first-family parameters by parameter height

The finite-removal step of Jaswal Remark 6.3,
DOI 10.5281/zenodo.23437117. The sixteen singular C-points are
removed from the reduced-m-height bounded sets. Their exponent 1/2
is preserved. This is a parameter-height count, with no minimal curve-height
comparison asserted.
-/
namespace Z2Z4Rank6.CParameterGoodCounting
noncomputable section
open scoped Classical

def heightSet (H : ℕ) : Set CPoint := CParameterCounting.heightSet H\exceptionalPoints

def count (H : ℕ) : ℕ := (heightSet H).ncard

theorem heightSet_finite (hN : NeronRigidCountingTheorem.{0})
    (hMW : MordellWeilTheorem) (hDescent : CompleteTwoDescentTheorem)
    (hOdd : OddPrimeTorsionIntegrality) (H : ℕ) : (heightSet H).Finite :=
  (CParameterCounting.heightSet_finite hN hMW hDescent hOdd H).sdiff

theorem heightSet_smooth (H : ℕ) (c : CPoint) (hc : c∈heightSet H) :
    GoodCurve (X c.m) := (X_good_iff_not_exceptional c).mpr hc.2

/-- Each bounded count loses at most the proved sixteen points. -/
theorem count_bounds (hN : NeronRigidCountingTheorem.{0})
    (hMW : MordellWeilTheorem) (hDescent : CompleteTwoDescentTheorem)
    (hOdd : OddPrimeTorsionIntegrality) (H : ℕ) :
    count H≤CParameterCounting.count H ∧ CParameterCounting.count H≤count H+16 := by
  have h := FiniteRemovalCounting.ncard_sdiff_sandwich (CParameterCounting.heightSet H)
    exceptionalPoints (CParameterCounting.heightSet_finite hN hMW hDescent hOdd H)
    exceptionalPoints_finite
  simpa only [count,heightSet,CParameterCounting.count,exceptionalPoints_card] using h

/-- The smooth-fiber parameter count retains exponent 1/2. -/
theorem counting_exponent (hN : NeronRigidCountingTheorem.{0})
    (hMW : MordellWeilTheorem) (hDescent : CompleteTwoDescentTheorem)
    (hOdd : OddPrimeTorsionIntegrality) : HasLogarithmicCountingExponent count (1/2) := by
  exact FiniteRemovalCounting.counting_exponent_sdiff CParameterCounting.heightSet
    (CParameterCounting.heightSet_finite hN hMW hDescent hOdd) exceptionalPoints
    exceptionalPoints_finite (1/2) (CParameterCounting.counting_exponent hN hMW hDescent hOdd)
    (by norm_num)

/-- Distinct j-values of smooth fibers with parameter height at most H. -/
def jImageSet (H : ℕ) : Set ℚ := (fun c : CPoint => jValue (X c.m)) '' heightSet H

def jCount (H : ℕ) : ℕ := (jImageSet H).ncard

theorem jImageSet_finite (hN : NeronRigidCountingTheorem.{0})
    (hMW : MordellWeilTheorem) (hDescent : CompleteTwoDescentTheorem)
    (hOdd : OddPrimeTorsionIntegrality) (H : ℕ) : (jImageSet H).Finite :=
  (heightSet_finite hN hMW hDescent hOdd H).image _

/-- Image counts are squeezed by the proved 192 fiber bound. -/
theorem jCount_bounds (hN : NeronRigidCountingTheorem.{0})
    (hMW : MordellWeilTheorem) (hDescent : CompleteTwoDescentTheorem)
    (hOdd : OddPrimeTorsionIntegrality) (H : ℕ) :
    jCount H≤count H ∧ count H≤192*jCount H := by
  have hfinite := heightSet_finite hN hMW hDescent hOdd H
  exact ⟨FiniteImageCounting.ncard_image_le (heightSet H) hfinite _,
    ncard_CPoint_le_192_mul_jimage (heightSet H) hfinite (heightSet_smooth H)⟩

/-- The distinct-j count, still bounded by parameter height, has
exponent 1/2. -/
theorem j_counting_exponent (hN : NeronRigidCountingTheorem.{0})
    (hMW : MordellWeilTheorem) (hDescent : CompleteTwoDescentTheorem)
    (hOdd : OddPrimeTorsionIntegrality) : HasLogarithmicCountingExponent jCount (1/2) := by
  apply (counting_exponent hN hMW hDescent hOdd).of_eventually_mul_sandwich
    (C:=192) (by norm_num) (by decide)
  exact Filter.Eventually.of_forall (jCount_bounds hN hMW hDescent hOdd)

end
end Z2Z4Rank6.CParameterGoodCounting
