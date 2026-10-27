import Z2Z4Rank6.JTranscendence
import Z2Z4Rank6.SecondJDegree
import Z2Z4Rank6.SecondFunctionField

/-!
# Transcendence of the second-family j-invariant

The checked degree 12 rational function is nonconstant and transcendental
over Q. Its image in the degree-eight function field is exactly
Mathlib's j-invariant of F. This is the nonconstant-j input used in the
specialization discussion in Jaswal, Theorem 8.1(c),
DOI 10.5281/zenodo.23437117.
-/
namespace Z2Z4Rank6
noncomputable section
open Polynomial

namespace SecondFamily
section Reduced
local instance secondJTranscendenceRatDecidableEq : DecidableEq ℚ := Classical.decEq ℚ

/-- The checked reduced denominator degree excludes every rational constant. -/
theorem jRationalFunction_ne_constant (q:ℚ) :
    jRationalFunction≠algebraMap ℚ (RatFunc ℚ) q := by
  intro h
  have hd:=jRationalFunction_denom_natDegree
  have he : jRationalFunction=algebraMap ℚ[X] (RatFunc ℚ) (C q) := by
    rw [h]
    exact IsScalarTower.algebraMap_apply ℚ ℚ[X] (RatFunc ℚ) q
  rw [he,RatFunc.denom_algebraMap,Polynomial.natDegree_one] at hd
  contradiction

/-- The degree 12 rational function is transcendental over Q. -/
theorem jRationalFunction_transcendental : Transcendental ℚ jRationalFunction := by
  have h := RatFunc.transcendental_of_ne_C jRationalFunction (by
    rintro ⟨q,hq⟩
    have hC : (RatFunc.C : ℚ→+*RatFunc ℚ)=algebraMap ℚ (RatFunc ℚ) := Subsingleton.elim _ _
    exact jRationalFunction_ne_constant q (hq.trans (RingHom.congr_fun hC q)))
  convert h using 1
  exact Subsingleton.elim _ _
end Reduced
end SecondFamily

namespace SecondFunctionField
open SecondFamily

private theorem embedded_numerator :
    algebraMap Base K (algebraMap ℚ[X] Base SecondFamily.jNumerator)=
      256*((U W)^2-3*(V W)^2)^3 := by
  rw [polynomial_embedding]
  norm_num [SecondFamily.jNumerator,uPolynomial,vPolynomial,U,V,lambda,map_ofNat]

private theorem embedded_denominator :
    algebraMap Base K (algebraMap ℚ[X] Base SecondFamily.jDenominator)=
      (V W)^4*((U W)^2-4*(V W)^2) := by
  rw [polynomial_embedding]
  norm_num [SecondFamily.jDenominator,uPolynomial,vPolynomial,U,V,lambda,map_ofNat]

/-- The generic invariant equals the image of the checked rational
function under the coefficient-field embedding. -/
theorem j_eq_base_embedding :
    (F W).j=algebraMap Base K SecondFamily.jRationalFunction := by
  rw [SecondFamily.jRationalFunction,map_div₀]
  apply j_eq_of_scaled_invariant_parts _ _ _ 16 (by norm_num)
  · rw [embedded_numerator]
    simp only [F,twistedF,WeierstrassCurve.c₄,WeierstrassCurve.b₂,WeierstrassCurve.b₄]
    ring
  · rw [embedded_denominator,F_discriminant]
    ring

/-- Mathlib's j-invariant of F over Q(G₂) is transcendental over Q. -/
theorem j_transcendental : Transcendental ℚ (F W).j := by
  rw [j_eq_base_embedding]
  apply (transcendental_algebraMap_iff (R:=ℚ) (algebraMap Base K).injective).mpr
  exact SecondFamily.jRationalFunction_transcendental

end SecondFunctionField
end
end Z2Z4Rank6
