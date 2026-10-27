import Z2Z4Rank6.GusicTadicCriterion
import Z2Z4Rank6.RationalFunctionFamily
import Z2Z4Rank6.JInvariant
import Mathlib.FieldTheory.RatFunc.AsPolynomial

/-!
# The four integral-root families in the specialization criterion

Models and hypotheses for Propositions 2.3 and 5.2 of M. Jaswal,
DOI 10.5281/zenodo.23437117. All polynomial divisor tests are proved in
`GusicTadicCriterion`; this file checks the smooth models and their
nonconstant j-invariant.
-/

namespace Z2Z4Rank6.GusicTadic

open Polynomial
noncomputable section

abbrev RF := RatFunc ℚ

/-- The integral split model y² = (x-e₀)(x-e₁)(x-e₂). -/
def splitModel {R : Type*} [CommRing R] (e : Fin 3 → R) : WeierstrassCurve R :=
  ⟨0, -(e 0+e 1+e 2), 0, e 0*e 1+e 0*e 2+e 1*e 2, -(e 0*e 1*e 2)⟩

/-- The standard quadratic twist with roots 0, -d a², -d b². -/
def twistModel {R : Type*} [CommRing R] (d A B : R) : WeierstrassCurve R :=
  ⟨0, d*(A^2+B^2), 0, d^2*A^2*B^2, 0⟩

def roots (q : ℤ[X]) : Fin 3 → ℤ[X] := ![0,-q*aPoly^2,-q*bPoly^2]

def differenceProducts (e : Fin 3 → ℤ[X]) : Fin 3 → ℤ[X] :=
  ![(e 0-e 1)*(e 0-e 2), (e 1-e 0)*(e 1-e 2), (e 2-e 0)*(e 2-e 1)]

def integralModel (q : ℤ[X]) : WeierstrassCurve ℤ[X] := twistModel q aPoly bPoly

/-- The coefficient embedding of the integer polynomial model into Q(t). -/
def polyToRF : ℤ[X] →+* RF :=
  (algebraMap ℚ[X] RF).comp (Polynomial.mapRingHom (Int.castRingHom ℚ))

def genericModel (q : ℤ[X]) : WeierstrassCurve RF :=
  twistModel (polyToRF q) (a RatFunc.X) (b RatFunc.X)

def fiberModel (q : ℤ[X]) (r : ℚ) : WeierstrassCurve ℚ :=
  twistModel (evalAt r q) (a r) (b r)

@[simp] theorem polyToRF_a : polyToRF aPoly = a (RatFunc.X : RF) := by
  simp [polyToRF, aPoly, a, map_ofNat]

@[simp] theorem polyToRF_b : polyToRF bPoly = b (RatFunc.X : RF) := by
  simp [polyToRF, bPoly, b, map_ofNat]

@[simp] theorem evalAt_a (r : ℚ) : evalAt r aPoly = a r := by
  simp [evalAt, aPoly, a]

@[simp] theorem evalAt_b (r : ℚ) : evalAt r bPoly = b r := by
  simp [evalAt, bPoly, b]

@[simp] theorem integralModel_map (q : ℤ[X]) :
    (integralModel q).map polyToRF = genericModel q := by
  ext <;> simp [integralModel, genericModel, twistModel, WeierstrassCurve.map]

@[simp] theorem integralModel_eval (q : ℤ[X]) (r : ℚ) :
    (integralModel q).map (evalAt r) = fiberModel q r := by
  ext <;> simp [integralModel, fiberModel, twistModel, WeierstrassCurve.map]

theorem integralModel_split (q : ℤ[X]) : integralModel q = splitModel (roots q) := by
  apply WeierstrassCurve.ext <;> dsimp [integralModel, splitModel, roots, twistModel] <;> ring

theorem roots_differenceProducts (q : ℤ[X]) :
    differenceProducts (roots q) = fun i => q^2*rootDifferenceProducts i :=
  twisted_products_identity q

@[simp] theorem genericModel_one : genericModel 1 = RationalFunctionFamily.curve := by
  ext <;> simp [genericModel, twistModel, RationalFunctionFamily.curve,
    RationalFunctionFamily.parameter, X, E]

@[simp] theorem fiberModel_one (r : ℚ) : fiberModel 1 r = X r := by
  ext <;> simp [fiberModel, twistModel, X, E]

theorem twistModel_discriminant {F : Type*} [CommRing F] (d A B : F) :
    (twistModel d A B).Δ = d^6*(E A B).Δ := by
  simp only [twistModel, E, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

theorem twistModel_c4 {F : Type*} [CommRing F] (d A B : F) :
    (twistModel d A B).c₄ = d^2*(E A B).c₄ := by
  simp only [twistModel, E, WeierstrassCurve.c₄, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄]
  ring

/-- The field-valued j-expression, without requiring a typeclass in its type. -/
def jExpression {F : Type*} [Field F] (W : WeierstrassCurve F) : F := W.c₄^3/W.Δ

theorem twistModel_jExpression {F : Type*} [Field F] (d A B : F) (hd : d ≠ 0) :
    jExpression (twistModel d A B) = jExpression (E A B) := by
  rw [jExpression, twistModel_discriminant, twistModel_c4, jExpression]
  rw [mul_pow, ← pow_mul, show 2*3=6 by decide]
  exact mul_div_mul_left _ _ (pow_ne_zero 6 hd)

/-- Nonconstant here means not isomorphic over Q(t) to a constant Weierstrass
curve. An admissible variable change expresses such an isomorphism. -/
def Nonconstant (W : WeierstrassCurve RF) : Prop :=
  ∀ (W₀ : WeierstrassCurve ℚ) (C : WeierstrassCurve.VariableChange RF),
    W ≠ C • W₀.map RatFunc.C

theorem jExpression_variableChange {F : Type*} [Field F]
    (W : WeierstrassCurve F) (C : WeierstrassCurve.VariableChange F) :
    jExpression (C • W) = jExpression W := by
  rw [jExpression, WeierstrassCurve.variableChange_c₄,
    WeierstrassCurve.variableChange_Δ, jExpression, mul_pow, ← pow_mul]
  exact mul_div_mul_left _ _ (pow_ne_zero 12 C.u⁻¹.ne_zero)

theorem jExpression_map {F L : Type*} [Field F] [Field L]
    (f : F →+* L) (W : WeierstrassCurve F) :
    jExpression (W.map f) = f (jExpression W) := by
  simp [jExpression, WeierstrassCurve.map_c₄, WeierstrassCurve.map_Δ]

private theorem rf_j_numerator :
    algebraMap ℚ[X] RF jNumerator = 256*((a (RatFunc.X : RF))^4-
      (a RatFunc.X)^2*(b RatFunc.X)^2+(b RatFunc.X)^4)^3 := by
  simp [jNumerator, a, b, map_ofNat]

private theorem rf_j_denominator :
    algebraMap ℚ[X] RF jDenominator = (a (RatFunc.X : RF))^4*(b RatFunc.X)^4*
      ((a RatFunc.X)^2-(b RatFunc.X)^2)^2 := by
  simp [jDenominator, a, b, map_ofNat]

private theorem base_discriminant : RationalFunctionFamily.curve.Δ =
    16*algebraMap ℚ[X] RF jDenominator := by
  rw [rf_j_denominator]
  dsimp [RationalFunctionFamily.curve, RationalFunctionFamily.parameter, X, E]
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

private theorem base_c4_cube : RationalFunctionFamily.curve.c₄^3 =
    16*algebraMap ℚ[X] RF jNumerator := by
  rw [rf_j_numerator]
  dsimp [RationalFunctionFamily.curve, RationalFunctionFamily.parameter, X, E]
  simp only [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]
  ring

private theorem base_jExpression : jExpression RationalFunctionFamily.curve =
    algebraMap ℚ[X] RF jNumerator / algebraMap ℚ[X] RF jDenominator := by
  rw [jExpression, base_c4_cube, base_discriminant]
  exact mul_div_mul_left _ _ (by norm_num : (16 : RF) ≠ 0)

theorem base_j_nonconstant (c : ℚ) :
    jExpression RationalFunctionFamily.curve ≠ RatFunc.C c := by
  have hD : algebraMap ℚ[X] RF jDenominator ≠ 0 := by
    intro h
    have hΔ := (WeierstrassCurve.isUnit_Δ RationalFunctionFamily.curve).ne_zero
    rw [base_discriminant, h, mul_zero] at hΔ
    exact hΔ rfl
  rw [base_jExpression]
  intro he
  have he' := (div_eq_iff hD).mp he
  have hz : algebraMap ℚ[X] RF (jNumerator-Polynomial.C c*jDenominator)=0 := by
    simp only [map_sub, map_mul, RatFunc.algebraMap_C]
    exact sub_eq_zero.mpr he'
  exact j_fiber_polynomial_ne_zero c ((RatFunc.algebraMap_injective ℚ) (by simpa using hz))

theorem genericModel_nonconstant (q : ℤ[X]) (hq : polyToRF q ≠ 0) :
    Nonconstant (genericModel q) := by
  intro W₀ C h
  have hj := congrArg jExpression h
  rw [genericModel, twistModel_jExpression _ _ _ hq,
    jExpression_variableChange, jExpression_map] at hj
  exact base_j_nonconstant (jExpression W₀) hj

theorem genericModel_elliptic (q : ℤ[X]) (hq : polyToRF q ≠ 0) :
    (genericModel q).IsElliptic := by
  constructor
  rw [isUnit_iff_ne_zero]
  change (twistModel (polyToRF q) (a RatFunc.X) (b RatFunc.X)).Δ ≠ 0
  rw [twistModel_discriminant]
  exact mul_ne_zero (pow_ne_zero 6 hq)
    (WeierstrassCurve.isUnit_Δ RationalFunctionFamily.curve).ne_zero

/-- The original family and its three twists, in the order X, q₁, q₂, q₁₂. -/
def familyPolynomials : Fin 4 → ℤ[X] := ![1,q1Poly,q2Poly,q12Poly]

def familyParameters : Fin 4 → ℚ := ![14/3,14/3,50/3,50/3]

theorem polyToRF_injective : Function.Injective polyToRF := by
  intro p q hpq
  apply Polynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
  exact RatFunc.algebraMap_injective ℚ hpq

theorem familyPolynomial_ne_zero (k : Fin 4) : familyPolynomials k ≠ 0 := by
  intro h
  have he := congrArg (evalAt (familyParameters k)) h
  fin_cases k <;> norm_num [familyPolynomials, familyParameters, evalAt,
    q1Poly, q2Poly, q12Poly, q1, q2, q12] at he

theorem family_generic_elliptic (k : Fin 4) :
    (genericModel (familyPolynomials k)).IsElliptic :=
  genericModel_elliptic _ (fun h => familyPolynomial_ne_zero k
    (polyToRF_injective (by simpa using h)))

theorem family_nonconstant (k : Fin 4) :
    Nonconstant (genericModel (familyPolynomials k)) :=
  genericModel_nonconstant _ (fun h => familyPolynomial_ne_zero k
    (polyToRF_injective (by simpa using h)))

theorem family_fiber_elliptic (k : Fin 4) :
    (fiberModel (familyPolynomials k) (familyParameters k)).IsElliptic := by
  constructor
  rw [isUnit_iff_ne_zero]
  dsimp [fiberModel]
  rw [twistModel_discriminant]
  apply mul_ne_zero
  · apply pow_ne_zero
    fin_cases k <;> norm_num [familyPolynomials, familyParameters, evalAt,
      q1Poly, q2Poly, q12Poly, q1, q2, q12]
  · fin_cases k <;> norm_num [familyParameters, E, a, b, WeierstrassCurve.Δ,
      WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

theorem family_divisor_test (k : Fin 4) (i : Fin 3) (g : ℤ[X])
    (hsq : Squarefree g) (hdiv : g ∣ differenceProducts (roots (familyPolynomials k)) i)
    (hnonconstant : g.natDegree ≠ 0) :
    ¬IsSquare (evalAt (familyParameters k) g) := by
  rw [roots_differenceProducts] at hdiv
  fin_cases k
  · exact base14_divisor_test i g hsq (by simpa [familyPolynomials] using hdiv) hnonconstant
  · exact twist14_divisor_test i g hsq hdiv hnonconstant
  · exact twist50_divisor_test i g hsq hdiv hnonconstant
  · exact product50_divisor_test i g hsq hdiv hnonconstant

/-- The rational fibers use the printed standard quadratic-twist equation. -/
theorem q1_fiber_14 : fiberModel q1Poly (14/3) =
    twistModel (4610/3 : ℚ) (a (14/3)) (b (14/3)) := by
  unfold fiberModel
  congr 1
  norm_num [evalAt, q1Poly, q1]

theorem q2_fiber_50 : fiberModel q2Poly (50/3) =
    twistModel (35935/9 : ℚ) (a (50/3)) (b (50/3)) := by
  unfold fiberModel
  congr 1
  norm_num [evalAt, q2Poly, q2]

theorem q12_fiber_50 : fiberModel q12Poly (50/3) =
    twistModel (23185262/27 : ℚ) (a (50/3)) (b (50/3)) := by
  unfold fiberModel
  congr 1
  norm_num [evalAt, q12Poly, q12]


/-- The j-expression used in the nonconstant proof is the Mathlib
j-invariant on a smooth curve. -/
theorem jExpression_eq_j {F : Type*} [Field F] (W : WeierstrassCurve F) [W.IsElliptic] :
    jExpression W=W.j := by
  rw [jExpression, WeierstrassCurve.j_eq, div_eq_mul_inv, mul_comm]

/-- The split coefficients encode the factored equation in the source theorem. -/
theorem splitModel_equation {R : Type*} [CommRing R] (e : Fin 3 → R) (x y : R) :
    (splitModel e).toAffine.Equation x y ↔ y^2=(x-e 0)*(x-e 1)*(x-e 2) := by
  rw [WeierstrassCurve.Affine.equation_iff]
  change (y^2+0*x*y+0*y=x^3+(-(e 0+e 1+e 2))*x^2+
    (e 0*e 1+e 0*e 2+e 1*e 2)*x+(-(e 0*e 1*e 2))) ↔ _
  constructor <;> intro h <;> linear_combination h


end
end Z2Z4Rank6.GusicTadic
