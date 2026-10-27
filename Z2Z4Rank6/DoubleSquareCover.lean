module

public import Z2Z4Rank6.QuadraticRingMaps
public import Mathlib.RingTheory.Extension.Presentation.Basic
public import Mathlib.Tactic

@[expose] public section

/-! Affine two-square covers with one polynomial parameter.
The objects are the three-variable quotient by the two displayed
square relations. This common presentation is used by the torsion-cover
normal forms and the separate smoothness calculation. -/
namespace Z2Z4Rank6.DoubleSquareCover
noncomputable section
open Polynomial
open scoped Classical
abbrev Poly := Polynomial ℚ
abbrev PolynomialRing := MvPolynomial (Fin 3) ℚ

def relation (f : Fin 2→Poly) (i : Fin 2) : PolynomialRing :=
  (MvPolynomial.X i.succ)^2-Polynomial.aeval (MvPolynomial.X (0:Fin 3):PolynomialRing) (f i)
def definingIdeal (f : Fin 2→Poly) : Ideal PolynomialRing := Ideal.span (Set.range (relation f))
abbrev CoordinateRing (f : Fin 2→Poly) := PolynomialRing⧸definingIdeal f
abbrev Ring := CoordinateRing

def coordinate (f : Fin 2→Poly) (i : Fin 3) : CoordinateRing f :=
  Ideal.Quotient.mk (definingIdeal f) (MvPolynomial.X i)
def parameter (f : Fin 2→Poly) : CoordinateRing f := coordinate f 0
def root (f : Fin 2→Poly) (i : Fin 2) : CoordinateRing f := coordinate f i.succ

def presentation (f : Fin 2→Poly) : Algebra.Presentation ℚ (CoordinateRing f) (Fin 3) (Fin 2) :=
  Algebra.Presentation.naive (v:=relation f)

instance coordinateRing_finitePresentation (f : Fin 2→Poly) : Algebra.FinitePresentation ℚ (CoordinateRing f) :=
  (presentation f).finitePresentation_of_isFinite

@[simp] theorem relation_zero (f : Fin 2→Poly) (i : Fin 2) :
    Ideal.Quotient.mk (definingIdeal f) (relation f i)=0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i,rfl⟩)

theorem quotient_aeval (f : Fin 2→Poly) (p : Poly) :
    Ideal.Quotient.mk (definingIdeal f) (Polynomial.aeval (MvPolynomial.X (0:Fin 3):PolynomialRing) p)=
      Polynomial.aeval (parameter f) p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add,hp,hq]
  | monomial n q =>
    simp only [Polynomial.aeval_monomial,map_mul,map_pow]
    rfl

theorem root_sq (f : Fin 2→Poly) (i : Fin 2) :
    (root f i)^2=Polynomial.aeval (parameter f) (f i) := by
  have h := relation_zero f i
  simp only [relation,map_sub,map_pow,quotient_aeval] at h
  exact sub_eq_zero.mp h

/-- The quotient universal property, with prescribed rational
parameter and two roots in an arbitrary rational commutative algebra. -/
def lift {A : Type*} [CommRing A] [Algebra ℚ A] (f : Fin 2→Poly)
    (t : A) (s : Fin 2→A) (hs : ∀i,(s i)^2=Polynomial.aeval t (f i)) : CoordinateRing f→ₐ[ℚ]A :=
  Ideal.Quotient.liftₐ (definingIdeal f)
    (MvPolynomial.aeval (Fin.cases t s)) (by
      have hker : definingIdeal f≤RingHom.ker (MvPolynomial.aeval (Fin.cases t s)).toRingHom := by
        apply Ideal.span_le.mpr
        rintro p ⟨i,rfl⟩
        change (MvPolynomial.aeval (Fin.cases t s)) (relation f i)=0
        simp only [relation,map_sub,map_pow,MvPolynomial.aeval_X,Fin.cases_succ]
        have he : (MvPolynomial.aeval (Fin.cases t s):PolynomialRing→ₐ[ℚ]A)
            (Polynomial.aeval (MvPolynomial.X (0:Fin 3):PolynomialRing) (f i))=Polynomial.aeval t (f i) := by
          induction (f i) using Polynomial.induction_on' with
          | add p q hp hq => simp only [map_add,hp,hq]
          | monomial n q => simp only [Polynomial.aeval_monomial,map_mul,map_pow,AlgHom.commutes,
              MvPolynomial.aeval_X,Fin.cases_zero]
        rw [he,hs i,sub_self]
      intro p hp
      exact hker hp)

@[simp] theorem lift_parameter {A : Type*} [CommRing A] [Algebra ℚ A] (f : Fin 2→Poly)
    (t : A) (s : Fin 2→A) (hs : ∀i,(s i)^2=Polynomial.aeval t (f i)) : lift f t s hs (parameter f)=t := by
  change (MvPolynomial.aeval (Fin.cases t s)) (MvPolynomial.X 0)=t
  simp
@[simp] theorem lift_root {A : Type*} [CommRing A] [Algebra ℚ A] (f : Fin 2→Poly)
    (t : A) (s : Fin 2→A) (hs : ∀i,(s i)^2=Polynomial.aeval t (f i)) (i : Fin 2) :
    lift f t s hs (root f i)=s i := by
  change (MvPolynomial.aeval (Fin.cases t s)) (MvPolynomial.X i.succ)=s i
  simp
end
end Z2Z4Rank6.DoubleSquareCover
