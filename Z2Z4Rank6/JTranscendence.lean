import Z2Z4Rank6.JDegree
import Z2Z4Rank6.FunctionField
import Mathlib.FieldTheory.RatFunc.IntermediateField

/-!
# Transcendence of the generic j-invariant

The nonconstant j-invariant used in the specialization arguments of Jaswal,
DOI 10.5281/zenodo.23437117. The checked reduced rational-function
degrees imply transcendence over Q; the proved coefficient embedding then
identifies its image with Mathlib's j of X over Q(C).
-/
namespace Z2Z4Rank6
noncomputable section
open Polynomial

/-- A convenient invariant identity over any coefficient field. -/
theorem j_eq_of_scaled_invariant_parts {L:Type*} [Field L]
    (W:WeierstrassCurve L) [W.IsElliptic] (N D c:L) (hc:c≠0)
    (hN:W.c₄^3=c*N) (hD:W.Δ=c*D) : W.j=N/D := by
  rw [WeierstrassCurve.j_eq,hN,hD]
  calc
    (c*D)⁻¹*(c*N)=(c*N)/(c*D) := by rw [div_eq_mul_inv]; ring
    _=N/D := mul_div_mul_left N D hc

/-- The degree 48 rational function is transcendental over Q. -/
theorem jRationalFunction_transcendental : Transcendental ℚ jRationalFunction := by
  have h := RatFunc.transcendental_of_ne_C jRationalFunction (by
    rintro ⟨q,hq⟩
    have hC : (RatFunc.C : ℚ→+*RatFunc ℚ)=algebraMap ℚ (RatFunc ℚ) := Subsingleton.elim _ _
    exact jRationalFunction_ne_constant q (hq.trans (RingHom.congr_fun hC q)))
  convert h using 1
  exact Subsingleton.elim _ _

namespace FunctionField

private theorem embedded_numerator :
    algebraMap Base K (algebraMap ℚ[X] Base jNumerator)=
      256*((a m)^4-(a m)^2*(b m)^2+(b m)^4)^3 := by
  rw [polynomial_embedding]
  simp [jNumerator,a,b,map_ofNat]

private theorem embedded_denominator :
    algebraMap Base K (algebraMap ℚ[X] Base jDenominator)=
      (a m)^4*(b m)^4*((a m)^2-(b m)^2)^2 := by
  rw [polynomial_embedding]
  simp [jDenominator,a,b,map_ofNat]

/-- The embedded rational function equals the invariant of the generic
elliptic curve over the constructed function field. -/
theorem j_eq_base_embedding :
    (X m).j=algebraMap Base K jRationalFunction := by
  rw [jRationalFunction,map_div₀]
  apply j_eq_of_scaled_invariant_parts _ _ _ 16 (by norm_num)
  · rw [embedded_numerator]
    simp only [X,E,WeierstrassCurve.c₄,WeierstrassCurve.b₂,WeierstrassCurve.b₄]
    ring
  · rw [embedded_denominator]
    simp only [X,E,WeierstrassCurve.Δ,WeierstrassCurve.b₂,WeierstrassCurve.b₄,
      WeierstrassCurve.b₆,WeierstrassCurve.b₈]
    ring

/-- Mathlib's j-invariant of X over Q(C) is transcendental over Q. -/
theorem j_transcendental : Transcendental ℚ (X m).j := by
  rw [j_eq_base_embedding]
  apply (transcendental_algebraMap_iff (R:=ℚ) (algebraMap Base K).injective).mpr
  exact jRationalFunction_transcendental

end FunctionField
end
end Z2Z4Rank6
