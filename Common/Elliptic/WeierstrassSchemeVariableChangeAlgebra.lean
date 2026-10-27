import Common.Elliptic.WeierstrassScheme
import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Maps
import Mathlib.Algebra.MvPolynomial.Funext

/-!
# Admissible coordinate changes on homogeneous cubic rings

The linear homogeneous substitution is Silverman, The Arithmetic of Elliptic
Curves, second edition, III.1, Table 3.1, pp. 45–46. Its effect on the
equation, its inverse and its induced graded quotient maps are proved here.
Mathlib's admissible variable-change coefficients are used without alteration.
-/

namespace WeierstrassScheme.VariableChange
noncomputable section
open scoped Classical
open MvPolynomial
universe u
variable {K : Type u} [Field K]
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

/-- Homogeneous coordinates of the admissible linear transformation. -/
def linear (c : WeierstrassCurve.VariableChange K) : Fin 3 → PolynomialRing K :=
  ![C ((c.u : K)^2)*X 0+C c.r*X 2,
    C ((c.u : K)^3)*X 1+C ((c.u : K)^2*c.s)*X 0+C c.t*X 2,
    X 2]

def substitution (c : WeierstrassCurve.VariableChange K) :
    PolynomialRing K →ₐ[K] PolynomialRing K := MvPolynomial.aeval (linear c)

@[simp] theorem linear_zero (c : WeierstrassCurve.VariableChange K) :
    linear c 0 = C ((c.u : K)^2)*X 0+C c.r*X 2 := rfl
@[simp] theorem linear_one (c : WeierstrassCurve.VariableChange K) :
    linear c 1 = C ((c.u : K)^3)*X 1+C ((c.u : K)^2*c.s)*X 0+C c.t*X 2 := rfl
@[simp] theorem linear_two (c : WeierstrassCurve.VariableChange K) : linear c 2 = X 2 := rfl

theorem linear_homogeneous (c : WeierstrassCurve.VariableChange K) (i : Fin 3) :
    (linear c i).IsHomogeneous 1 := by
  have hx := isHomogeneous_X K (0 : Fin 3)
  have hy := isHomogeneous_X K (1 : Fin 3)
  have hz := isHomogeneous_X K (2 : Fin 3)
  have h0 : (linear c 0).IsHomogeneous 1 := by
    rw [linear_zero]
    exact (hx.C_mul ((c.u : K)^2)).add (hz.C_mul c.r)
  have h1 : (linear c 1).IsHomogeneous 1 := by
    rw [linear_one]
    exact ((hy.C_mul ((c.u : K)^3)).add (hx.C_mul ((c.u : K)^2*c.s))).add (hz.C_mul c.t)
  have h2 : (linear c 2).IsHomogeneous 1 := by
    rw [linear_two]
    exact hz
  exact Fin.cases h0 (fun j => Fin.cases h1
    (fun k => Fin.cases h2 (fun z => Fin.elim0 z) k) j) i

theorem substitution_homogeneous (c : WeierstrassCurve.VariableChange K)
    {p : PolynomialRing K} {n : ℕ} (hp : p.IsHomogeneous n) :
    (substitution c p).IsHomogeneous n := by
  simpa only [substitution, one_mul] using hp.aeval (linear c) (linear_homogeneous c)

variable [Infinite K]

theorem substitution_relation (W : WeierstrassCurve K)
    (c : WeierstrassCurve.VariableChange K) :
    substitution c (relation W) = C ((c.u : K)^6)*relation (c • W) := by
  apply MvPolynomial.funext
  intro v
  simp [substitution, relation, linear, WeierstrassCurve.variableChange_def,
    Units.val_inv_eq_inv_val]
  field_simp
  all_goals ring

theorem substitution_inv_linear (c : WeierstrassCurve.VariableChange K) (i : Fin 3) :
    substitution c⁻¹ (linear c i) = X i := by
  apply MvPolynomial.funext
  intro v
  fin_cases i <;>
    simp [substitution, linear, WeierstrassCurve.VariableChange.inv_def,
      Units.val_inv_eq_inv_val]
  all_goals field_simp
  all_goals ring

theorem substitution_inv_comp (c : WeierstrassCurve.VariableChange K) :
    (substitution c⁻¹).comp (substitution c) = AlgHom.id K (PolynomialRing K) := by
  apply MvPolynomial.algHom_ext
  intro i
  simpa only [AlgHom.comp_apply, substitution, MvPolynomial.aeval_X, AlgHom.id_apply] using
    substitution_inv_linear c i

theorem substitution_comp_inv (c : WeierstrassCurve.VariableChange K) :
    (substitution c).comp (substitution c⁻¹) = AlgHom.id K (PolynomialRing K) := by
  simpa only [inv_inv] using substitution_inv_comp c⁻¹

/-- Forward map on the homogeneous quotients. -/
def quotientMap (W : WeierstrassCurve K) (c : WeierstrassCurve.VariableChange K) :
    CoordinateRing W →ₐ[K] CoordinateRing (c • W) :=
  Ideal.Quotient.liftₐ (definingIdeal W)
    ((Ideal.Quotient.mkₐ K (definingIdeal (c • W))).comp (substitution c)) (by
      have hker : definingIdeal W ≤ RingHom.ker
          (((Ideal.Quotient.mkₐ K (definingIdeal (c • W))).comp (substitution c)).toRingHom) := by
        apply Ideal.span_le.mpr
        rintro p (rfl : p = relation W)
        change Ideal.Quotient.mk (definingIdeal (c • W)) (substitution c (relation W)) = 0
        rw [substitution_relation, map_mul]
        have hz : Ideal.Quotient.mk (definingIdeal (c • W)) (relation (c • W)) = 0 :=
          Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
        rw [hz, mul_zero]
      intro p hp
      exact hker hp)

/-- Inverse map on the homogeneous quotients, avoiding dependent casts. -/
def quotientInverse (W : WeierstrassCurve K) (c : WeierstrassCurve.VariableChange K) :
    CoordinateRing (c • W) →ₐ[K] CoordinateRing W :=
  Ideal.Quotient.liftₐ (definingIdeal (c • W))
    ((Ideal.Quotient.mkₐ K (definingIdeal W)).comp (substitution c⁻¹)) (by
      have hker : definingIdeal (c • W) ≤ RingHom.ker
          (((Ideal.Quotient.mkₐ K (definingIdeal W)).comp (substitution c⁻¹)).toRingHom) := by
        apply Ideal.span_le.mpr
        rintro p (rfl : p = relation (c • W))
        change Ideal.Quotient.mk (definingIdeal W) (substitution c⁻¹ (relation (c • W))) = 0
        rw [substitution_relation, inv_smul_smul, map_mul]
        have hz : Ideal.Quotient.mk (definingIdeal W) (relation W) = 0 :=
          Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
        rw [hz, mul_zero]
      intro p hp
      exact hker hp)

@[simp] theorem quotientMap_mk (W : WeierstrassCurve K)
    (c : WeierstrassCurve.VariableChange K) (p : PolynomialRing K) :
    quotientMap W c (Ideal.Quotient.mk (definingIdeal W) p) =
      Ideal.Quotient.mk (definingIdeal (c • W)) (substitution c p) := rfl

@[simp] theorem quotientInverse_mk (W : WeierstrassCurve K)
    (c : WeierstrassCurve.VariableChange K) (p : PolynomialRing K) :
    quotientInverse W c (Ideal.Quotient.mk (definingIdeal (c • W)) p) =
      Ideal.Quotient.mk (definingIdeal W) (substitution c⁻¹ p) := rfl

theorem quotientInverse_quotientMap (W : WeierstrassCurve K)
    (c : WeierstrassCurve.VariableChange K) (x : CoordinateRing W) :
    quotientInverse W c (quotientMap W c x) = x := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp only [quotientMap_mk, quotientInverse_mk]
  exact congrArg (Ideal.Quotient.mk (definingIdeal W))
    (DFunLike.congr_fun (substitution_inv_comp c) p)

theorem quotientMap_quotientInverse (W : WeierstrassCurve K)
    (c : WeierstrassCurve.VariableChange K) (x : CoordinateRing (c • W)) :
    quotientMap W c (quotientInverse W c x) = x := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp only [quotientInverse_mk, quotientMap_mk]
  exact congrArg (Ideal.Quotient.mk (definingIdeal (c • W)))
    (DFunLike.congr_fun (substitution_comp_inv c) p)

def gradedMap (W : WeierstrassCurve K) (c : WeierstrassCurve.VariableChange K) :
    grading W →+*ᵍ grading (c • W) where
  __ := (quotientMap W c).toRingHom
  map_mem := by
    intro n x hx
    obtain ⟨p, hp, rfl⟩ := hx
    exact ⟨substitution c p, substitution_homogeneous c hp, rfl⟩

def gradedInverse (W : WeierstrassCurve K) (c : WeierstrassCurve.VariableChange K) :
    grading (c • W) →+*ᵍ grading W where
  __ := (quotientInverse W c).toRingHom
  map_mem := by
    intro n x hx
    obtain ⟨p, hp, rfl⟩ := hx
    exact ⟨substitution c⁻¹ p, substitution_homogeneous c⁻¹ hp, rfl⟩

theorem gradedInverse_comp_gradedMap (W : WeierstrassCurve K)
    (c : WeierstrassCurve.VariableChange K) :
    (gradedInverse W c).comp (gradedMap W c) = GradedRingHom.id (grading W) :=
  GradedRingHom.ext (quotientInverse_quotientMap W c)

theorem gradedMap_comp_gradedInverse (W : WeierstrassCurve K)
    (c : WeierstrassCurve.VariableChange K) :
    (gradedMap W c).comp (gradedInverse W c) = GradedRingHom.id (grading (c • W)) :=
  GradedRingHom.ext (quotientMap_quotientInverse W c)

end
end WeierstrassScheme.VariableChange
