module

public import Common.Elliptic.BinaryQuarticModel
public import Common.AlgebraicGeometry.ProjRationalPoint

@[expose] public section

/-!
# Rational points of a binary quartic model

The homogeneous coordinate evaluation (x,1,y) is used to construct a
Spec Q morphism into the complete weighted Proj. Its rational structure-map
equation is retained.
-/

namespace BinaryQuarticModel
noncomputable section
open AlgebraicGeometry CategoryTheory
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def Equation (f : BinaryQuartic ℚ) (x y : ℚ) : Prop :=
  y^2=f.a*x^4+f.b*x^3+f.c*x^2+f.d*x+f.e

def affineEvaluation (f : BinaryQuartic ℚ) (x y : ℚ) (h : Equation f x y) :
    CoordinateRing f →ₐ[ℚ] ℚ :=
  Ideal.Quotient.liftₐ (definingIdeal f) (MvPolynomial.aeval ![x,1,y]) (by
    have hker : definingIdeal f ≤ RingHom.ker (MvPolynomial.aeval ![x,1,y]).toRingHom := by
      apply Ideal.span_le.mpr
      rintro p (rfl : p = relation f)
      change (MvPolynomial.aeval ![x,1,y]) (relation f) = 0
      simp only [relation,form,map_sub,map_add,map_mul,map_pow,MvPolynomial.aeval_X,
        MvPolynomial.aeval_C,Fin.isValue,Matrix.cons_val_zero,Matrix.cons_val_one,
        one_pow,mul_one,Matrix.cons_val_two]
      exact sub_eq_zero.mpr h
    intro p hp
    exact hker hp)

@[simp] theorem affineEvaluation_coordinate (f : BinaryQuartic ℚ) (x y : ℚ)
    (h : Equation f x y) (i : Fin 3) :
    affineEvaluation f x y h (coordinate f i) = ![x,1,y] i := by
  change (MvPolynomial.aeval ![x,1,y]) (MvPolynomial.X i) = _
  simp

def affinePointMorphism (f : BinaryQuartic ℚ) (x y : ℚ) (h : Equation f x y) :
    Spec (CommRingCat.of ℚ) ⟶ scheme f :=
  ProjRationalPoint.point (grading f) (affineEvaluation f x y h)
    (by decide : 0 < 1) (coordinate f 1) (coordinate_degree f 1)
    (by simp)

theorem affinePointMorphism_over (f : BinaryQuartic ℚ) (x y : ℚ) (h : Equation f x y) :
    affinePointMorphism f x y h ≫ structureMap f = 𝟙 (Spec (CommRingCat.of ℚ)) :=
  ProjRationalPoint.point_over (grading f) (affineEvaluation f x y h)
    (by decide : 0 < 1) (coordinate f 1) (coordinate_degree f 1) (by simp)

end
end BinaryQuarticModel
