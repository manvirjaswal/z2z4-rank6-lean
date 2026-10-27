import Common.Elliptic.WeierstrassScheme
import Common.AlgebraicGeometry.ProjRationalPoint
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-!
# Homogeneous evaluations on the Weierstrass scheme

Infinity is the rational scheme morphism represented by (0:1:0).
An affine solution is the morphism represented by (x:y:1).
These constructions use the full projective cubic and retain their
over-Spec Q equations.
-/

namespace WeierstrassScheme
noncomputable section
open AlgebraicGeometry CategoryTheory
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def infinityEvaluation (W : WeierstrassCurve ℚ) : CoordinateRing W →ₐ[ℚ] ℚ :=
  Ideal.Quotient.liftₐ (definingIdeal W) (MvPolynomial.aeval ![0,1,0]) (by
    have hker : definingIdeal W ≤ RingHom.ker (MvPolynomial.aeval ![(0:ℚ),1,0]).toRingHom := by
      apply Ideal.span_le.mpr
      rintro p (rfl : p = relation W)
      change (MvPolynomial.aeval ![(0:ℚ),1,0]) (relation W) = 0
      simp [relation]
    intro p hp
    exact hker hp)

@[simp] theorem infinityEvaluation_coordinate (W : WeierstrassCurve ℚ) (i : Fin 3) :
    infinityEvaluation W (coordinate W i) = ![(0:ℚ),1,0] i := by
  change (MvPolynomial.aeval ![(0:ℚ),1,0]) (MvPolynomial.X i) = _
  simp

def infinityPoint (W : WeierstrassCurve ℚ) : Spec (CommRingCat.of ℚ) ⟶ scheme W :=
  ProjRationalPoint.point (grading W) (infinityEvaluation W)
    (by decide : 0 < 1) (coordinate W 1) (coordinate_degree W 1) (by simp)

theorem infinityPoint_over (W : WeierstrassCurve ℚ) :
    infinityPoint W ≫ structureMap W = 𝟙 (Spec (CommRingCat.of ℚ)) :=
  ProjRationalPoint.point_over (grading W) (infinityEvaluation W)
    (by decide : 0 < 1) (coordinate W 1) (coordinate_degree W 1) (by simp)

def affineEvaluation (W : WeierstrassCurve ℚ) (x y : ℚ) (h : W.toAffine.Equation x y) :
    CoordinateRing W →ₐ[ℚ] ℚ :=
  Ideal.Quotient.liftₐ (definingIdeal W) (MvPolynomial.aeval ![x,y,1]) (by
    have hker : definingIdeal W ≤ RingHom.ker (MvPolynomial.aeval ![x,y,1]).toRingHom := by
      apply Ideal.span_le.mpr
      rintro p (rfl : p = relation W)
      change (MvPolynomial.aeval ![x,y,1]) (relation W) = 0
      rw [WeierstrassCurve.Affine.equation_iff] at h
      simp [relation]
      linear_combination h
    intro p hp
    exact hker hp)

@[simp] theorem affineEvaluation_coordinate (W : WeierstrassCurve ℚ) (x y : ℚ)
    (h : W.toAffine.Equation x y) (i : Fin 3) :
    affineEvaluation W x y h (coordinate W i) = ![x,y,1] i := by
  change (MvPolynomial.aeval ![x,y,1]) (MvPolynomial.X i) = _
  simp

def affinePoint (W : WeierstrassCurve ℚ) (x y : ℚ) (h : W.toAffine.Equation x y) :
    Spec (CommRingCat.of ℚ) ⟶ scheme W :=
  ProjRationalPoint.point (grading W) (affineEvaluation W x y h)
    (by decide : 0 < 1) (coordinate W 2) (coordinate_degree W 2) (by simp)

theorem affinePoint_over (W : WeierstrassCurve ℚ) (x y : ℚ) (h : W.toAffine.Equation x y) :
    affinePoint W x y h ≫ structureMap W = 𝟙 (Spec (CommRingCat.of ℚ)) :=
  ProjRationalPoint.point_over (grading W) (affineEvaluation W x y h)
    (by decide : 0 < 1) (coordinate W 2) (coordinate_degree W 2) (by simp)

/-- Canonical evaluation of every nonsingular Weierstrass point,
including the identity at infinity, on the projective scheme. -/
def pointMorphism (W : WeierstrassCurve ℚ) :
    W.toAffine.Point → (Spec (CommRingCat.of ℚ) ⟶ scheme W)
  | .zero => infinityPoint W
  | .some x y h => affinePoint W x y h.1

theorem pointMorphism_over (W : WeierstrassCurve ℚ) (P : W.toAffine.Point) :
    pointMorphism W P ≫ structureMap W = 𝟙 (Spec (CommRingCat.of ℚ)) := by
  cases P with
  | zero => exact infinityPoint_over W
  | some x y h => exact affinePoint_over W x y h.1

end
end WeierstrassScheme
