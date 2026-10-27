import Z2Z4Rank6.ProjectiveBaseSchemeRationalPoints
import Z2Z4Rank6.BaseCurve

/-!
# The printed rational point on the projective base

Jaswal, Lemma 4.1(a), DOI 10.5281/zenodo.23437117: the displayed point
(m,u,v)=(1,35,35) defines a morphism Spec Q→Proj C over Spec Q.
Its affine coordinates are recovered through the rational point equivalence.
-/
namespace Z2Z4Rank6.ProjectiveBaseSchemePrintedPoint
noncomputable section
open AlgebraicGeometry CategoryTheory
open ProjectiveBaseScheme ProjectiveBaseSchemeRationalPoints

/-- The scheme rational point represented by (1:35:35:1). -/
def printedPoint : RationalPoint := fromAffine baseOrigin

theorem printedPoint_morphism : printedPoint.val = pointMorphism baseOrigin := rfl

theorem printedPoint_over :
    printedPoint.val ≫ structureMap = 𝟙 (Spec (CommRingCat.of ℚ)) :=
  printedPoint.property

/-- The inverse chart equivalence recovers the printed affine point. -/
theorem printedPoint_affine : rationalPointEquiv.symm printedPoint = baseOrigin :=
  rationalPointEquiv.symm_apply_apply baseOrigin

theorem printedPoint_coordinates :
    (rationalPointEquiv.symm printedPoint).m = 1 ∧
      (rationalPointEquiv.symm printedPoint).u = 35 ∧
      (rationalPointEquiv.symm printedPoint).v = 35 := by
  rw [printedPoint_affine]
  exact ⟨rfl,rfl,rfl⟩

end
end Z2Z4Rank6.ProjectiveBaseSchemePrintedPoint
