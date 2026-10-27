import Z2Z4Rank6.ECProjectiveScheme
import Z2Z4Rank6.BaseCurveArithmetic
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.RingTheory.Extension.Presentation.Submersive

/-! The affine quotient of the printed EC cubic, with coordinates (x,y).
Source: Jaswal, DOI 10.5281/zenodo.23437117, Theorem 1.2(a), Lemma 4.1.
Its equation is proved equivalent to Mathlib's EC affine equation. -/
namespace Z2Z4Rank6.ECProjectiveSchemeAffine
noncomputable section
open scoped Classical
open CategoryTheory AlgebraicGeometry

abbrev PolynomialRing := MvPolynomial (Fin 2) ℚ
def relation (_:Fin 1) : PolynomialRing :=
  MvPolynomial.X 1^2-MvPolynomial.X 0^3-MvPolynomial.X 0^2+
    137620*MvPolynomial.X 0+10504000
def definingIdeal : Ideal PolynomialRing := Ideal.span (Set.range relation)
abbrev CoordinateRing := PolynomialRing⧸definingIdeal
def x : CoordinateRing := Ideal.Quotient.mk definingIdeal (MvPolynomial.X 0)
def y : CoordinateRing := Ideal.Quotient.mk definingIdeal (MvPolynomial.X 1)

def presentation : Algebra.Presentation ℚ CoordinateRing (Fin 2) (Fin 1) :=
  Algebra.Presentation.naive (v:=relation)
instance coordinateRing_finitePresentation : Algebra.FinitePresentation ℚ CoordinateRing :=
  presentation.finitePresentation_of_isFinite

theorem relation_zero : Ideal.Quotient.mk definingIdeal (relation 0)=0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨0,rfl⟩)

theorem equation : y^2=x^3+x^2-137620*x-10504000 := by
  have h := relation_zero
  simp only [relation,map_sub,map_add,map_pow,map_mul,map_ofNat] at h
  change y^2-x^3-x^2+137620*x+10504000=0 at h
  linear_combination h

/-- This explicit quotient is the printed Mathlib Weierstrass equation. -/
theorem equation_iff_mathlib (a b:ℚ) :
    (MvPolynomial.aeval ![a,b]) (relation 0)=0 ↔ EC.toAffine.Equation a b := by
  rw [ec_equation_iff]
  simp only [relation,map_sub,map_add,map_mul,map_pow,map_ofNat,MvPolynomial.aeval_X,
    Matrix.cons_val_zero,Matrix.cons_val_one]
  constructor <;> intro h <;> linear_combination h

def evaluation (a b:ℚ) (h:EC.toAffine.Equation a b) : CoordinateRing→ₐ[ℚ]ℚ :=
  Ideal.Quotient.liftₐ definingIdeal (MvPolynomial.aeval ![a,b]) (by
    have hker : definingIdeal≤RingHom.ker (MvPolynomial.aeval ![a,b]).toRingHom := by
      apply Ideal.span_le.mpr
      rintro p ⟨i,rfl⟩
      have hi : i=0 := Subsingleton.elim _ _
      subst i
      exact (equation_iff_mathlib a b).mpr h
    intro p hp
    exact hker hp)

instance coordinateRing_nontrivial : Nontrivial CoordinateRing :=
  (evaluation 404 0 ((ec_equation_iff _ _).mpr (by norm_num))).toRingHom.domain_nontrivial

def scheme : Scheme := Spec (CommRingCat.of CoordinateRing)
def structureMap : scheme⟶Spec (CommRingCat.of ℚ) :=
  Spec.map (CommRingCat.ofHom (algebraMap ℚ CoordinateRing))

end
end Z2Z4Rank6.ECProjectiveSchemeAffine
