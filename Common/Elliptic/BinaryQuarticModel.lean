module

public import Common.AlgebraicGeometry.HomogeneousQuotient
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import Mathlib.Tactic

@[expose] public section

/-!
# Binary quartics and their weighted projective curves

The model y²=ax⁴+bx³z+cx²z²+dxz³+ez⁴ is the quotient Proj with
weights (x,z,y)=(1,1,2). Its invariants use Cremona–Fisher–Stoll,
Minimisation and reduction of 2-, 3- and 4-coverings of elliptic curves,
Algebra & Number Theory 4 (2010), 763–820, Definition 2.2;
arXiv:0908.1741v1, p. 4. In particular c4=16I, c6=32J, and Δ is sixteen
times the ordinary polynomial discriminant.
-/

namespace BinaryQuarticModel
noncomputable section
open scoped Classical
open MvPolynomial AlgebraicGeometry CategoryTheory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
universe u

structure BinaryQuartic (K : Type u) where
  a : K
  b : K
  c : K
  d : K
  e : K

variable {K : Type u}

def invariantI [CommRing K] (f : BinaryQuartic K) : K := 12*f.a*f.e-3*f.b*f.d+f.c^2
def invariantJ [CommRing K] (f : BinaryQuartic K) : K :=
  72*f.a*f.c*f.e-27*f.a*f.d^2-27*f.b^2*f.e+9*f.b*f.c*f.d-2*f.c^3
def c4 [CommRing K] (f : BinaryQuartic K) : K := 16*invariantI f
def c6 [CommRing K] (f : BinaryQuartic K) : K := 32*invariantJ f
def discriminant [Field K] (f : BinaryQuartic K) : K := (c4 f^3-c6 f^2)/1728

def polynomial [CommRing K] (f : BinaryQuartic K) : Polynomial K :=
  Polynomial.C f.a*Polynomial.X^4+Polynomial.C f.b*Polynomial.X^3+
    Polynomial.C f.c*Polynomial.X^2+Polynomial.C f.d*Polynomial.X+Polynomial.C f.e

variable [Field K]
abbrev PolynomialRing (K : Type u) [Field K] := MvPolynomial (Fin 3) K
def weights : Fin 3 → ℕ := ![1,1,2]
def polynomialGrading : ℕ → Submodule K (PolynomialRing K) :=
  MvPolynomial.weightedHomogeneousSubmodule K weights
instance polynomialGradedAlgebra : GradedAlgebra (polynomialGrading (K := K)) :=
  MvPolynomial.weightedGradedAlgebra K weights

def form (f : BinaryQuartic K) : PolynomialRing K :=
  C f.a*X 0^4+C f.b*(X 0^3*X 1)+C f.c*(X 0^2*X 1^2)+
    C f.d*(X 0*X 1^3)+C f.e*X 1^4
def relation (f : BinaryQuartic K) : PolynomialRing K := X 2^2-form f
def definingIdeal (f : BinaryQuartic K) : Ideal (PolynomialRing K) :=
  Ideal.span {relation f}

theorem form_homogeneous (f : BinaryQuartic K) : (form f).IsWeightedHomogeneous weights 4 := by
  have hx : (X (0 : Fin 3) : PolynomialRing K).IsWeightedHomogeneous weights 1 := by
    simpa [weights] using isWeightedHomogeneous_X K weights (0 : Fin 3)
  have hz : (X (1 : Fin 3) : PolynomialRing K).IsWeightedHomogeneous weights 1 := by
    simpa [weights] using isWeightedHomogeneous_X K weights (1 : Fin 3)
  have h1 := ((hx.pow 4).C_mul f.a).add (((hx.pow 3).mul hz).C_mul f.b)
  have h2 := h1.add (((hx.pow 2).mul (hz.pow 2)).C_mul f.c)
  exact (h2.add ((hx.mul (hz.pow 3)).C_mul f.d)).add ((hz.pow 4).C_mul f.e)

theorem relation_homogeneous (f : BinaryQuartic K) :
    (relation f).IsWeightedHomogeneous weights 4 := by
  have hy : (X (2 : Fin 3) : PolynomialRing K).IsWeightedHomogeneous weights 2 := by
    simpa [weights] using isWeightedHomogeneous_X K weights (2 : Fin 3)
  exact (hy.pow 2).sub (form_homogeneous f)

theorem definingIdeal_homogeneous (f : BinaryQuartic K) :
    (definingIdeal f).IsHomogeneous polynomialGrading :=
  Ideal.homogeneous_span polynomialGrading _ (by
    rintro p (rfl : p = relation f)
    exact ⟨4, relation_homogeneous f⟩)

abbrev CoordinateRing (f : BinaryQuartic K) := PolynomialRing K ⧸ definingIdeal f
def grading (f : BinaryQuartic K) : ℕ → Submodule K (CoordinateRing f) :=
  HomogeneousQuotient.component polynomialGrading (definingIdeal f)
instance coordinateRingGradedAlgebra (f : BinaryQuartic K) : GradedAlgebra (grading f) :=
  HomogeneousQuotient.quotientGradedAlgebra (polynomialGrading (K := K)) (definingIdeal f)
    (definingIdeal_homogeneous f)

def coordinate (f : BinaryQuartic K) (i : Fin 3) : CoordinateRing f :=
  Ideal.Quotient.mk (definingIdeal f) (X i)
theorem coordinate_degree (f : BinaryQuartic K) (i : Fin 3) :
    coordinate f i ∈ grading f (weights i) :=
  ⟨X i, isWeightedHomogeneous_X K weights i, rfl⟩

/-- The complete weighted projective curve, with coordinates (x,z,y). -/
def scheme (f : BinaryQuartic K) : Scheme := Proj (grading f)

/-- This vertex ring evaluation establishes nontriviality; it does not
represent a projective point. -/
def originEvaluation (f : BinaryQuartic K) : CoordinateRing f →ₐ[K] K :=
  Ideal.Quotient.liftₐ (definingIdeal f) (MvPolynomial.aeval (fun _ => 0)) (by
    have hker : definingIdeal f ≤ RingHom.ker
        (MvPolynomial.aeval (fun _ : Fin 3 => (0 : K))).toRingHom := by
      apply Ideal.span_le.mpr
      rintro p (rfl : p = relation f)
      change (MvPolynomial.aeval (fun _ : Fin 3 => (0 : K))) (relation f) = 0
      simp [relation, form]
    intro p hp
    exact hker hp)

instance coordinateRing_nontrivial (f : BinaryQuartic K) : Nontrivial (CoordinateRing f) :=
  (originEvaluation f).toRingHom.domain_nontrivial
instance gradeZero_nontrivial (f : BinaryQuartic K) : Nontrivial (grading f 0) := by
  refine ⟨⟨0, 1, ?_⟩⟩
  intro h
  exact zero_ne_one (congrArg Subtype.val h : (0 : CoordinateRing f) = 1)

theorem weights_ne_zero (i : Fin 3) : weights i ≠ 0 := by fin_cases i <;> decide
theorem degreeZero_eq_coefficient (f : BinaryQuartic K) (r : grading f 0) :
    ∃ q : K, r = algebraMap K (grading f 0) q := by
  obtain ⟨p, hp, he⟩ := r.property
  have hp0 : p.IsWeightedHomogeneous weights 0 := hp
  have hpC : p = C (p.coeff 0) :=
    hp0.weightedHomogeneousComponent_same.symm.trans
      (MvPolynomial.weightedHomogeneousComponent_zero p weights_ne_zero)
  refine ⟨p.coeff 0, Subtype.ext ?_⟩
  change (r : CoordinateRing f) = algebraMap K (CoordinateRing f) (p.coeff 0)
  rw [←he, hpC]
  simp only [MvPolynomial.coeff_C]
  rfl

instance gradeZero_scalarTower (f : BinaryQuartic K) :
    IsScalarTower K (grading f 0) (CoordinateRing f) :=
  IsScalarTower.of_algebraMap_eq' (R := K) (S := grading f 0) (A := CoordinateRing f) rfl

def degreeZeroEquiv (f : BinaryQuartic K) : K ≃+* grading f 0 :=
  RingEquiv.ofBijective (algebraMap K (grading f 0))
    ⟨(algebraMap K (grading f 0)).injective, fun r => by
      obtain ⟨q, hq⟩ := degreeZero_eq_coefficient f r
      exact ⟨q, hq.symm⟩⟩

def structureMap (f : BinaryQuartic K) : scheme f ⟶ Spec (CommRingCat.of K) :=
  Proj.toSpecZero (grading f) ≫ Spec.map (CommRingCat.ofHom (algebraMap K (grading f 0)))
instance coordinateRing_finiteType (f : BinaryQuartic K) :
    Algebra.FiniteType (grading f 0) (CoordinateRing f) := by
  let : Algebra.FiniteType K (CoordinateRing f) := inferInstance
  exact Algebra.FiniteType.of_restrictScalars_finiteType K (grading f 0) (CoordinateRing f)
instance structureMap_proper (f : BinaryQuartic K) : IsProper (structureMap f) := by
  have : IsIso (Spec.map (CommRingCat.ofHom (algebraMap K (grading f 0)))) := by
    change IsIso (Scheme.Spec.mapIso (degreeZeroEquiv f).toCommRingCatIso.op).hom
    infer_instance
  dsimp only [structureMap]
  infer_instance

end
end BinaryQuarticModel
