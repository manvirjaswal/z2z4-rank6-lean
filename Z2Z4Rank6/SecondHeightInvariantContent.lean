import Z2Z4Rank6.SecondHeightInvariantContentCharts
import Z2Z4Rank6.HeightInvariantContent

/-! Uniform integral content and normalization-scale bound for the second
family in Jaswal Remark 6.3, DOI 10.5281/zenodo.23437117. The generic two-chart
homogeneous-content theorem is reused with the degree 12 powers. -/
namespace Z2Z4Rank6.SecondHeightInvariantContent
noncomputable section
open scoped Classical

/-- A fixed nonzero integer controls every common divisor of the two
short-invariant powers at primitive integer pairs. -/
theorem actual_content_constant :
    ∃ M : ℤ, M≠0 ∧ ∀ x₀ x₁ : ℤ, IsCoprime x₀ x₁ → ∀ d : ℤ,
      d∣(-27*SecondHeightInvariantForms.c4 x₀ x₁)^3 →
      d∣(-54*SecondHeightInvariantForms.c6 x₀ x₁)^2 → d∣M := by
  obtain ⟨M,hM,h⟩ := HeightInvariantContent.exists_primitive_content_constant shortC4Cube shortC6Square 12
    shortC4Cube_homogeneous shortC6Square_homogeneous short_chart_coprime short_swapped_chart_coprime
  refine ⟨M,hM,?_⟩
  intro x₀ x₁ hprim d hd4 hd6
  apply h x₀ x₁ hprim d
  · simpa only [eval_shortC4Cube,Matrix.cons_val_zero,Matrix.cons_val_one] using hd4
  · simpa only [eval_shortC6Square,Matrix.cons_val_zero,Matrix.cons_val_one] using hd6

/-- In particular, the common divisors of the integer c4,c6 values
at primitive pairs divide a fixed nonzero integer. -/
theorem c4_c6_content_constant :
    ∃ M : ℤ, M≠0 ∧ ∀ x₀ x₁ : ℤ, IsCoprime x₀ x₁ → ∀ d : ℤ,
      d∣SecondHeightInvariantForms.c4 x₀ x₁ → d∣SecondHeightInvariantForms.c6 x₀ x₁ → d∣M := by
  obtain ⟨M,hM,h⟩ := actual_content_constant
  refine ⟨M,hM,?_⟩
  intro x₀ x₁ hprim d hd4 hd6
  apply h x₀ x₁ hprim d
  · simpa only [pow_one] using pow_dvd_pow_of_dvd_of_le
      (dvd_mul_of_dvd_right hd4 (-27)) (by decide : 1≤3)
  · simpa only [pow_one] using pow_dvd_pow_of_dvd_of_le
      (dvd_mul_of_dvd_right hd6 (-54)) (by decide : 1≤2)

/-- Positive natural form of the uniform invariant common-divisor bound. -/
theorem exists_invariant_content_bound :
    ∃ M : ℕ, 0<M ∧ ∀ x₀ x₁ : ℤ, Nat.Coprime x₀.natAbs x₁.natAbs → ∀ d : ℕ,
      (d:ℤ)∣SecondHeightInvariantForms.c4 x₀ x₁ →
      (d:ℤ)∣SecondHeightInvariantForms.c6 x₀ x₁ → d∣M := by
  obtain ⟨M,hM,h⟩ := c4_c6_content_constant
  refine ⟨M.natAbs,Int.natAbs_pos.mpr hM,?_⟩
  intro x₀ x₁ hprim d hd4 hd6
  have hd := h x₀ x₁ (Int.isCoprime_iff_nat_coprime.mpr hprim) (d:ℤ) hd4 hd6
  simpa only [Int.natAbs_natCast] using Int.natAbs_dvd_natAbs.mpr hd

/-- The twelfth power of every short-model normalization scale is
uniformly bounded on primitive integer parameter pairs. -/
theorem exists_normalization_bound :
    ∃ C : ℕ, 0<C ∧ ∀ x₀ x₁ : ℤ, Nat.Coprime x₀.natAbs x₁.natAbs → ∀ d : ℕ,
      (d:ℤ)^4∣-27*SecondHeightInvariantForms.c4 x₀ x₁ →
      (d:ℤ)^6∣-54*SecondHeightInvariantForms.c6 x₀ x₁ → d^12≤C := by
  obtain ⟨M,hM,h⟩ := actual_content_constant
  refine ⟨M.natAbs,Int.natAbs_pos.mpr hM,?_⟩
  intro x₀ x₁ hprim d hd4 hd6
  have he : (d:ℤ)^12∣M := by
    apply h x₀ x₁ (Int.isCoprime_iff_nat_coprime.mpr hprim)
    · simpa only [←pow_mul] using pow_dvd_pow_of_dvd hd4 3
    · simpa only [←pow_mul] using pow_dvd_pow_of_dvd hd6 2
  have hd : d^12∣M.natAbs := by
    simpa only [Int.natAbs_pow,Int.natAbs_natCast] using Int.natAbs_dvd_natAbs.mpr he
  exact Nat.le_of_dvd (Int.natAbs_pos.mpr hM) hd

end
end Z2Z4Rank6.SecondHeightInvariantContent
