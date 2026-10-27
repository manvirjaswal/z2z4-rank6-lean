module

public import Z2Z4Rank6.CountingExponentHeight

@[expose] public section

/-!
# Squeezing height counts and removing finitely many objects

Elementary counting consequences for Jaswal Remark 6.3,
DOI 10.5281/zenodo.23437117. All inequalities concern natural
counting functions.
-/

namespace Z2Z4Rank6
noncomputable section
open Filter

namespace HasLogarithmicCountingExponent

/-- Positive logarithmic exponent forces the counts to infinity. -/
theorem tendsto_atTop {A : ℕ→ℕ} {a : ℝ}
    (hA : HasLogarithmicCountingExponent A a) (ha : 0<a) :
    Tendsto A atTop atTop := by
  have hLogLimit : Tendsto (fun H : ℕ => Real.log (A H : ℝ)) atTop atTop := by
    apply (hA.pos_mul_atTop ha loglog_nat_atTop).congr'
    filter_upwards [loglog_nat_atTop.eventually_gt_atTop 0] with H hD
    field_simp [hD.ne']
  have hCastLimit : Tendsto (fun H : ℕ => (A H : ℝ)) atTop atTop := by
    apply (Real.tendsto_exp_atTop.comp hLogLimit).congr'
    filter_upwards [hA.eventually_pos ha] with H hPos
    dsimp only [Function.comp_def]
    exact Real.exp_log (by exact_mod_cast hPos)
  exact tendsto_natCast_atTop_iff.mp hCastLimit

/-- Removing at most a fixed number of objects preserves a positive
logarithmic exponent. The zero-count initial bounds are harmless. -/
theorem of_eventually_add_sandwich {A B : ℕ→ℕ} {a : ℝ} {C : ℕ}
    (hA : HasLogarithmicCountingExponent A a) (ha : 0<a)
    (hBounds : ∀ᶠ H in atTop,B H≤A H ∧ A H≤B H+C) :
    HasLogarithmicCountingExponent B a := by
  have hBTop : Tendsto B atTop atTop := by
    refine Filter.tendsto_atTop.2 fun n => ?_
    filter_upwards [(hA.tendsto_atTop ha).eventually_ge_atTop (n+C),hBounds]
      with H hN hB
    omega
  apply hA.of_eventually_mul_sandwich ha (show 0<(2 : ℕ) by decide)
  filter_upwards [hBounds,hBTop.eventually_ge_atTop C] with H hB hC
  exact ⟨hB.1,by omega⟩

/-- Counts bounded between two positive-power reindexings have the same
positive logarithmic exponent. This is the analytic part of replacing a
parameter height by any height comparable to a positive power of it. -/
theorem of_eventually_powerHeight_sandwich {A B : ℕ→ℕ} {a cL dL cU dU : ℝ}
    (hA : HasLogarithmicCountingExponent A a) (ha : 0<a)
    (hcL : 0<cL) (hdL : 0<dL) (hcU : 0<cU) (hdU : 0<dU)
    (hBounds : ∀ᶠ H in atTop,
      A (powerHeightIndex cL dL H)≤B H ∧ B H≤A (powerHeightIndex cU dU H)) :
    HasLogarithmicCountingExponent B a := by
  have hLower := hA.comp_powerHeightIndex hcL hdL
  have hUpper := hA.comp_powerHeightIndex hcU hdU
  have hCompare : ∀ᶠ H in atTop,
      Real.log (A (powerHeightIndex cL dL H) : ℝ)/Real.log (Real.log (H : ℝ))≤
        Real.log (B H : ℝ)/Real.log (Real.log (H : ℝ)) ∧
      Real.log (B H : ℝ)/Real.log (Real.log (H : ℝ))≤
        Real.log (A (powerHeightIndex cU dU H) : ℝ)/Real.log (Real.log (H : ℝ)) := by
    filter_upwards [hBounds,hLower.eventually_pos ha,loglog_nat_atTop.eventually_gt_atTop 0]
      with H hB hPos hD
    change 0<A (powerHeightIndex cL dL H) at hPos
    have hBpos : 0<B H := lt_of_lt_of_le hPos hB.1
    have hLowerReal : 0<(A (powerHeightIndex cL dL H) : ℝ) := by exact_mod_cast hPos
    have hBReal : 0<(B H : ℝ) := by exact_mod_cast hBpos
    have hLowerBound : (A (powerHeightIndex cL dL H) : ℝ)≤(B H : ℝ) := by
      exact_mod_cast hB.1
    have hUpperBound : (B H : ℝ)≤(A (powerHeightIndex cU dU H) : ℝ) := by
      exact_mod_cast hB.2
    exact ⟨div_le_div_of_nonneg_right (Real.log_le_log hLowerReal hLowerBound) hD.le,
      div_le_div_of_nonneg_right (Real.log_le_log hBReal hUpperBound) hD.le⟩
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hLower hUpper
    (hCompare.mono fun _ h => h.1) (hCompare.mono fun _ h => h.2)

end HasLogarithmicCountingExponent
end
end Z2Z4Rank6
