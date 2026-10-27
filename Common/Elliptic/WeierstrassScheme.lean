import Common.AlgebraicGeometry.HomogeneousQuotient
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic

/-!
# The projective scheme of a Weierstrass equation

This is the homogeneous quotient Proj, including the point at infinity,
of Y²Z+a1 XYZ+a3 YZ²=X³+a2 X²Z+a4 XZ²+a6 Z³. The construction works over
any field. Properness follows from the grading and the proved degree-zero
coefficient-ring isomorphism.

Reference: Silverman, The Arithmetic of Elliptic Curves, second edition,
Chapter III, Section 1, pp. 42–46 (Weierstrass equations and their projective
coordinates). The grading argument generalizes the local EC projective model.
-/

namespace WeierstrassScheme
noncomputable section
open scoped Classical
open MvPolynomial AlgebraicGeometry CategoryTheory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
universe u
variable {K : Type u} [Field K]

abbrev PolynomialRing (K : Type u) [Field K] := MvPolynomial (Fin 3) K
def polynomialGrading : ℕ → Submodule K (PolynomialRing K) :=
  MvPolynomial.homogeneousSubmodule (Fin 3) K
instance polynomialGradedAlgebra : GradedAlgebra (polynomialGrading (K := K)) :=
  MvPolynomial.gradedAlgebra

def relation (W : WeierstrassCurve K) : PolynomialRing K :=
  X 1 ^ 2 * X 2 + C W.a₁ * (X 0 * X 1 * X 2) + C W.a₃ * (X 1 * X 2 ^ 2) -
    X 0 ^ 3 - C W.a₂ * (X 0 ^ 2 * X 2) - C W.a₄ * (X 0 * X 2 ^ 2) - C W.a₆ * X 2 ^ 3

def definingIdeal (W : WeierstrassCurve K) : Ideal (PolynomialRing K) :=
  Ideal.span {relation W}

theorem relation_homogeneous (W : WeierstrassCurve K) : (relation W).IsHomogeneous 3 := by
  have hx := isHomogeneous_X K (0 : Fin 3)
  have hy := isHomogeneous_X K (1 : Fin 3)
  have hz := isHomogeneous_X K (2 : Fin 3)
  have h1 := ((hy.pow 2).mul hz).add (((hx.mul hy).mul hz).C_mul W.a₁)
  have h2 := h1.add ((hy.mul (hz.pow 2)).C_mul W.a₃)
  have h3 := (h2.sub (hx.pow 3)).sub (((hx.pow 2).mul hz).C_mul W.a₂)
  exact (h3.sub ((hx.mul (hz.pow 2)).C_mul W.a₄)).sub ((hz.pow 3).C_mul W.a₆)

theorem definingIdeal_homogeneous (W : WeierstrassCurve K) :
    (definingIdeal W).IsHomogeneous polynomialGrading :=
  Ideal.homogeneous_span polynomialGrading _ (by
    rintro p (rfl : p = relation W)
    exact ⟨3, relation_homogeneous W⟩)

abbrev CoordinateRing (W : WeierstrassCurve K) := PolynomialRing K ⧸ definingIdeal W
def grading (W : WeierstrassCurve K) : ℕ → Submodule K (CoordinateRing W) :=
  HomogeneousQuotient.component polynomialGrading (definingIdeal W)
instance coordinateRingGradedAlgebra (W : WeierstrassCurve K) : GradedAlgebra (grading W) :=
  HomogeneousQuotient.quotientGradedAlgebra (polynomialGrading (K := K)) (definingIdeal W)
    (definingIdeal_homogeneous W)

def coordinate (W : WeierstrassCurve K) (i : Fin 3) : CoordinateRing W :=
  Ideal.Quotient.mk (definingIdeal W) (X i)
theorem coordinate_degree (W : WeierstrassCurve K) (i : Fin 3) :
    coordinate W i ∈ grading W 1 := ⟨X i, isHomogeneous_X K i, rfl⟩

/-- The complete projective cubic, with coordinate order (X,Y,Z). -/
def scheme (W : WeierstrassCurve K) : Scheme := Proj (grading W)

/-- The vertex evaluation proves that the homogeneous quotient is nonzero.
It is a ring map, not a projective point. -/
def originEvaluation (W : WeierstrassCurve K) : CoordinateRing W →ₐ[K] K :=
  Ideal.Quotient.liftₐ (definingIdeal W) (MvPolynomial.aeval (fun _ => 0)) (by
    have hker : definingIdeal W ≤ RingHom.ker
        (MvPolynomial.aeval (fun _ : Fin 3 => (0 : K))).toRingHom := by
      apply Ideal.span_le.mpr
      rintro p (rfl : p = relation W)
      change (MvPolynomial.aeval (fun _ : Fin 3 => (0 : K))) (relation W) = 0
      simp [relation]
    intro p hp
    exact hker hp)

instance coordinateRing_nontrivial (W : WeierstrassCurve K) : Nontrivial (CoordinateRing W) :=
  (originEvaluation W).toRingHom.domain_nontrivial
instance gradeZero_nontrivial (W : WeierstrassCurve K) : Nontrivial (grading W 0) := by
  refine ⟨⟨0, 1, ?_⟩⟩
  intro h
  exact zero_ne_one (congrArg Subtype.val h : (0 : CoordinateRing W) = 1)

theorem degreeZero_eq_coefficient (W : WeierstrassCurve K) (r : grading W 0) :
    ∃ q : K, r = algebraMap K (grading W 0) q := by
  obtain ⟨p, hp, he⟩ := r.property
  have hp0 : p.IsHomogeneous 0 := hp
  have hpC : p = C (p.coeff 0) :=
    hp0.weightedHomogeneousComponent_same.symm.trans
      (MvPolynomial.weightedHomogeneousComponent_zero p (by simp))
  refine ⟨p.coeff 0, Subtype.ext ?_⟩
  change (r : CoordinateRing W) = algebraMap K (CoordinateRing W) (p.coeff 0)
  rw [←he, hpC]
  simp only [MvPolynomial.coeff_C]
  rfl

instance gradeZero_scalarTower (W : WeierstrassCurve K) :
    IsScalarTower K (grading W 0) (CoordinateRing W) :=
  IsScalarTower.of_algebraMap_eq' (R := K) (S := grading W 0) (A := CoordinateRing W) rfl

def degreeZeroEquiv (W : WeierstrassCurve K) : K ≃+* grading W 0 :=
  RingEquiv.ofBijective (algebraMap K (grading W 0))
    ⟨(algebraMap K (grading W 0)).injective, fun r => by
      obtain ⟨q, hq⟩ := degreeZero_eq_coefficient W r
      exact ⟨q, hq.symm⟩⟩

def structureMap (W : WeierstrassCurve K) : scheme W ⟶ Spec (CommRingCat.of K) :=
  Proj.toSpecZero (grading W) ≫ Spec.map (CommRingCat.ofHom (algebraMap K (grading W 0)))

instance coordinateRing_finiteType (W : WeierstrassCurve K) :
    Algebra.FiniteType (grading W 0) (CoordinateRing W) := by
  let : Algebra.FiniteType K (CoordinateRing W) := inferInstance
  exact Algebra.FiniteType.of_restrictScalars_finiteType K (grading W 0) (CoordinateRing W)

instance structureMap_proper (W : WeierstrassCurve K) : IsProper (structureMap W) := by
  have : IsIso (Spec.map (CommRingCat.ofHom (algebraMap K (grading W 0)))) := by
    change IsIso (Scheme.Spec.mapIso (degreeZeroEquiv W).toCommRingCatIso.op).hom
    infer_instance
  dsimp only [structureMap]
  infer_instance

end
end WeierstrassScheme
