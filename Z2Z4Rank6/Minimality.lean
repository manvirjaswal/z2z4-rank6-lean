module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction
public import Mathlib.Tactic

@[expose] public section

/-!
# Minimality from a unit Weierstrass invariant

An integral Weierstrass equation with unit c₄ or unit discriminant is minimal
over a discrete valuation ring. The proof uses the weights 4 and 12 under an
admissible change, and the Mathlib minimal-model predicate. This supplies a criterion used to check
the
minimal equation in Jaswal, Proposition 7.1(b), DOI 10.5281/zenodo.23437117.
-/

namespace Z2Z4Rank6.Minimality

open WeierstrassCurve WithZero Multiplicative
open IsDiscreteValuationRing IsDedekindDomain.HeightOneSpectrum

noncomputable section
variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

private theorem c4_val_le_one (W : WeierstrassCurve K) [IsIntegral R W] :
    valuation K (maximalIdeal R) W.c₄ ≤ 1 := by
  have he : algebraMap R K (integralModel R W).c₄ = W.c₄ := by
    conv_rhs => rw [←baseChange_integralModel_eq R W]
    simp [WeierstrassCurve.baseChange]
  rw [←he]
  exact valuation_le_one (maximalIdeal R) _

private theorem disc_val_le_one (W : WeierstrassCurve K) [IsIntegral R W] :
    valuation K (maximalIdeal R) W.Δ ≤ 1 := by
  obtain ⟨r,hr⟩ := Δ_integral_of_isIntegral R W
  rw [←hr]
  exact valuation_le_one (maximalIdeal R) r

/-- A unit invariant forces every integral variable change to have
discriminant valuation at most the original multiplicative valuation. -/
theorem isMinimal_of_unit_invariant (W : WeierstrassCurve K) [IsIntegral R W]
    (hunit : valuation K (maximalIdeal R) W.c₄=1 ∨
      valuation K (maximalIdeal R) W.Δ=1) : IsMinimal R W := by
  refine ⟨⟨by simpa only [one_smul] using (inferInstance : IsIntegral R W),?_⟩⟩
  intro C hC _
  let : IsIntegral R (C • W) := hC
  have hu : valuation K (maximalIdeal R) ((C.u⁻¹ : Kˣ) : K) ≤ 1 := by
    rcases hunit with hc | hd
    · have hv := c4_val_le_one R (C • W)
      rw [variableChange_c₄,map_mul,map_pow,hc,mul_one] at hv
      exact (pow_le_one_iff_of_nonneg zero_le (by decide : 4≠0)).mp hv
    · have hv := disc_val_le_one R (C • W)
      rw [variableChange_Δ,map_mul,map_pow,hd,mul_one] at hv
      exact (pow_le_one_iff_of_nonneg zero_le (by decide : 12≠0)).mp hv
  change (valuation_Δ_aux R (C • W) : ℤᵐ⁰) ≤ (valuation_Δ_aux R (1 • W) : ℤᵐ⁰)
  rw [one_smul,valuation_Δ_aux_eq_of_isIntegral,valuation_Δ_aux_eq_of_isIntegral,
    variableChange_Δ,map_mul,map_pow]
  exact mul_le_of_le_one_left zero_le (pow_le_one₀ zero_le hu)

private theorem valuation_unit (a : R) (ha : IsUnit a) :
    valuation K (maximalIdeal R) (algebraMap R K a)=1 := by
  obtain ⟨u,rfl⟩ := ha
  apply le_antisymm (valuation_le_one (maximalIdeal R) _)
  calc
    1 = valuation K (maximalIdeal R) (algebraMap R K (u:R))*
        valuation K (maximalIdeal R) (algebraMap R K ((u⁻¹:Rˣ):R)) := by
      rw [←map_mul,←map_mul,Units.mul_inv,map_one,map_one]
    _ ≤ valuation K (maximalIdeal R) (algebraMap R K (u:R))*1 :=
      mul_le_mul_of_nonneg_left (valuation_le_one (maximalIdeal R) _) zero_le
    _ = _ := mul_one _

/-- Coprime integral c₄ and discriminant give local minimality. -/
theorem baseChange_isMinimal_of_isCoprime (W : WeierstrassCurve R)
    (hcop : IsCoprime W.c₄ W.Δ) : IsMinimal R (W.baseChange K) := by
  let : IsIntegral R (W.baseChange K) := ⟨W,rfl⟩
  apply isMinimal_of_unit_invariant R
  obtain ⟨r,s,h⟩ := hcop
  have hunit : IsUnit W.c₄ ∨ IsUnit W.Δ := by
    rcases IsLocalRing.isUnit_or_isUnit_of_add_one h with hr | hs
    · exact Or.inl (isUnit_of_mul_isUnit_right hr)
    · exact Or.inr (isUnit_of_mul_isUnit_right hs)
  simpa only [WeierstrassCurve.baseChange,map_c₄,map_Δ] using
    hunit.imp (valuation_unit R W.c₄) (valuation_unit R W.Δ)

end
end Z2Z4Rank6.Minimality
