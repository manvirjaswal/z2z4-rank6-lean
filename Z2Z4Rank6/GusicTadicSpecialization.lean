module

public import Z2Z4Rank6.GusicTadicModels

@[expose] public section

/-!
# The published Gusić–Tadić theorem and the four specialization applications

Source: I. Gusić and P. Tadić, *Injectivity of the specialization
homomorphism of elliptic curves*, J. Number Theory 148 (2015), 137–152,
DOI 10.1016/j.jnt.2014.09.023; arXiv:1409.7189v2, 28 September 2014,
Theorem 1.1, printed page 2. The canonical specialization homomorphism is
introduced on printed page 1, with reference to Silverman's Appendix C §20.
https://arxiv.org/pdf/1409.7189v2

The theorem is passed as a hypothesis. Its source groups are Mathlib point groups over
RatFunc ℚ. Its canonical map evaluates reduced rational-function coordinates
at regular affine points, and sends poles to infinity.

Form differences: the three roots are indexed by Fin 3, and the equation is
encoded by its Weierstrass coefficients. Nonconstant means no admissible
variable change over Q(t) identifies the curve with one over Q, which is the
paper's non-isotrivial condition. Smoothness of the specialized fibers is
proved separately; the published arithmetic condition already implies it.
The source statement and applications assert injectivity only, with no rank
upper bound or Selmer computation.
-/

namespace Z2Z4Rank6.GusicTadic

open Polynomial Common.WeierstrassCoordinates
noncomputable section

/-- A reduced rational function is regular at r when its reduced denominator
has nonzero value there. -/
def RegularAt (r : ℚ) (f : RF) : Prop := (RatFunc.denom f).eval r ≠ 0

/-- The canonical specialization map: integral affine coordinates evaluate,
while a pole in the affine coordinates gives the point at infinity. -/
def CanonicalSpecializationAt (W : WeierstrassCurve RF)
    (V : WeierstrassCurve ℚ) (r : ℚ)
    (σ : W.toAffine.Point →+ V.toAffine.Point) : Prop := by
  classical
  exact ∀ (x y : RF) (h : W.toAffine.Nonsingular x y),
    encode (σ (.some x y h)) =
      if RegularAt r x ∧ RegularAt r y then
        some (RatFunc.eval (RingHom.id ℚ) r x, RatFunc.eval (RingHom.id ℚ) r y)
      else none

/-- An injective canonical homomorphism between the point groups. -/
def InjectiveSpecializationAt (W : WeierstrassCurve RF)
    (V : WeierstrassCurve ℚ) (r : ℚ) : Prop :=
  ∃ σ : W.toAffine.Point →+ V.toAffine.Point,
    CanonicalSpecializationAt W V r σ ∧ Function.Injective σ

/-- Theorem 1.1 of Gusić–Tadić is available for every nonconstant
elliptic split integral-root family. If each nonconstant squarefree divisor
of any root-difference product has nonsquare value at r, the canonical
specialization on the Q(t)-point group is injective. -/
def GusicTadicTheorem11 : Prop :=
  ∀ (e : Fin 3 → ℤ[X]) (r : ℚ),
    ((splitModel e).map polyToRF).IsElliptic →
    Nonconstant ((splitModel e).map polyToRF) →
    (∀ (i : Fin 3) (g : ℤ[X]), Squarefree g →
      g ∣ differenceProducts e i → g.natDegree ≠ 0 → ¬IsSquare (evalAt r g)) →
    InjectiveSpecializationAt ((splitModel e).map polyToRF)
      ((splitModel e).map (evalAt r)) r

/-- All four printed specializations are injective, using the published theorem and the
family-specific divisor tests. -/
theorem family_injective_specialization (hGT : GusicTadicTheorem11) (k : Fin 4) :
    InjectiveSpecializationAt (genericModel (familyPolynomials k))
      (fiberModel (familyPolynomials k) (familyParameters k)) (familyParameters k) := by
  have hE : ((splitModel (roots (familyPolynomials k))).map polyToRF).IsElliptic := by
    simpa only [← integralModel_split, integralModel_map] using family_generic_elliptic k
  have hN : Nonconstant ((splitModel (roots (familyPolynomials k))).map polyToRF) := by
    simpa only [← integralModel_split, integralModel_map] using family_nonconstant k
  have h := hGT (roots (familyPolynomials k)) (familyParameters k) hE hN
    (family_divisor_test k)
  simpa only [← integralModel_split, integralModel_map, integralModel_eval] using h

/-- The original X specializes injectively at m=14/3. -/
theorem X_injective_specialization_14 (hGT : GusicTadicTheorem11) :
    InjectiveSpecializationAt RationalFunctionFamily.curve (X (14/3 : ℚ)) (14/3) := by
  simpa only [familyPolynomials, familyParameters, Matrix.cons_val_zero,
    genericModel_one, fiberModel_one] using family_injective_specialization hGT 0

/-- The q₁ twist specializes injectively at m=14/3. -/
theorem q1_injective_specialization_14 (hGT : GusicTadicTheorem11) :
    InjectiveSpecializationAt (genericModel q1Poly) (fiberModel q1Poly (14/3)) (14/3) := by
  simpa only [familyPolynomials, familyParameters, Matrix.cons_val_one,
    Matrix.cons_val_zero] using family_injective_specialization hGT 1

/-- The q₂ twist specializes injectively at m=50/3. -/
theorem q2_injective_specialization_50 (hGT : GusicTadicTheorem11) :
    InjectiveSpecializationAt (genericModel q2Poly) (fiberModel q2Poly (50/3)) (50/3) := by
  simpa only [familyPolynomials, familyParameters, Matrix.cons_val,
    Matrix.head_cons, Matrix.cons_val_zero] using family_injective_specialization hGT 2

/-- The q₁₂ twist specializes injectively at m=50/3. -/
theorem q12_injective_specialization_50 (hGT : GusicTadicTheorem11) :
    InjectiveSpecializationAt (genericModel q12Poly) (fiberModel q12Poly (50/3)) (50/3) := by
  simpa only [familyPolynomials, familyParameters, Matrix.cons_val,
    Matrix.head_cons, Matrix.cons_val_zero] using family_injective_specialization hGT 3

/-- The q₁ conclusion with its concrete rational twist coefficient. -/
theorem q1_concrete_injective_specialization_14 (hGT : GusicTadicTheorem11) :
    InjectiveSpecializationAt (genericModel q1Poly)
      (twistModel (4610/3 : ℚ) (a (14/3)) (b (14/3))) (14/3) := by
  rw [← q1_fiber_14]
  exact q1_injective_specialization_14 hGT

/-- The q₂ conclusion with its concrete rational twist coefficient. -/
theorem q2_concrete_injective_specialization_50 (hGT : GusicTadicTheorem11) :
    InjectiveSpecializationAt (genericModel q2Poly)
      (twistModel (35935/9 : ℚ) (a (50/3)) (b (50/3))) (50/3) := by
  rw [← q2_fiber_50]
  exact q2_injective_specialization_50 hGT

/-- The q₁₂ conclusion with its concrete rational twist coefficient. -/
theorem q12_concrete_injective_specialization_50 (hGT : GusicTadicTheorem11) :
    InjectiveSpecializationAt (genericModel q12Poly)
      (twistModel (23185262/27 : ℚ) (a (50/3)) (b (50/3))) (50/3) := by
  rw [← q12_fiber_50]
  exact q12_injective_specialization_50 hGT

/-- Canonical specialization is determined by its coordinate rule. -/
theorem CanonicalSpecializationAt.unique {W : WeierstrassCurve RF}
    {V : WeierstrassCurve ℚ} {r : ℚ} {σ τ : W.toAffine.Point →+ V.toAffine.Point}
    (hσ : CanonicalSpecializationAt W V r σ) (hτ : CanonicalSpecializationAt W V r τ) : σ=τ := by
  ext P
  apply encode_injective
  cases P with
  | zero =>
    change encode (σ 0) = encode (τ 0)
    rw [map_zero, map_zero]
  | some x y h => exact (hσ x y h).trans (hτ x y h).symm

end
end Z2Z4Rank6.GusicTadic
