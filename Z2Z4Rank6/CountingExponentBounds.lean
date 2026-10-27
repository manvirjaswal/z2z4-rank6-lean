module

public import Z2Z4Rank6.NeronRigidCounting
public import Mathlib.Topology.Order.Basic
public import Mathlib.Tactic

@[expose] public section

/-!
# Elementary bounds for logarithmic counting exponents

Pure analytic transport lemmas for the counting step in Jaswal,
Remark 6.3, DOI 10.5281/zenodo.23437117.
Positive exponent gives eventual positive counts before logarithms of
multiplicative bounds are taken.
-/

namespace Z2Z4Rank6
noncomputable section
open Filter

theorem loglog_nat_atTop :
    Tendsto (fun H : ℕ => Real.log (Real.log (H : ℝ))) atTop atTop :=
  Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

namespace HasLogarithmicCountingExponent

/-- Positive logarithmic exponent forces eventual positive counts.
Thus totalized log at zero cannot affect the later comparisons. -/
theorem eventually_pos {A : ℕ→ℕ} {a : ℝ}
    (hA : HasLogarithmicCountingExponent A a) (ha : 0<a) :
    ∀ᶠ H in atTop,0<A H := by
  have hRatio : ∀ᶠ H in atTop,
      0<Real.log (A H : ℝ)/Real.log (Real.log (H : ℝ)) :=
    hA.eventually (Ioi_mem_nhds ha)
  filter_upwards [hRatio,loglog_nat_atTop.eventually_gt_atTop 0] with H hR hD
  have hlog : 0<Real.log (A H : ℝ) := (div_pos_iff_of_pos_right hD).mp hR
  have hOne : 1<(A H : ℝ) := (Real.log_pos_iff (Nat.cast_nonneg _)).mp hlog
  have hPos : 0<(A H : ℝ) := lt_trans zero_lt_one hOne
  exact_mod_cast hPos

/-- A fixed positive multiplicative factor does not change a positive
logarithmic counting exponent. The bounds need hold only eventually. -/
theorem of_eventually_real_mul_sandwich {A B : ℕ→ℕ} {a C : ℝ}
    (hA : HasLogarithmicCountingExponent A a) (ha : 0<a) (hC : 0<C)
    (hBounds : ∀ᶠ H in atTop,B H≤A H ∧ (A H : ℝ)≤C*(B H : ℝ)) :
    HasLogarithmicCountingExponent B a := by
  have hCdiv : Tendsto
      (fun H : ℕ => Real.log C/Real.log (Real.log (H : ℝ))) atTop (nhds 0) :=
    loglog_nat_atTop.const_div_atTop (Real.log C)
  have hLower : Tendsto
      (fun H : ℕ => Real.log (A H : ℝ)/Real.log (Real.log (H : ℝ))-
        Real.log C/Real.log (Real.log (H : ℝ))) atTop (nhds a) := by
    simpa only [sub_zero] using hA.sub hCdiv
  have hPositive : ∀ᶠ H in atTop,0<A H ∧ 0<B H := by
    filter_upwards [hA.eventually_pos ha,hBounds] with H hApos hB
    refine ⟨hApos,?_⟩
    by_contra h
    have hZero : B H=0 := Nat.eq_zero_of_not_pos h
    have hAreal : 0<(A H : ℝ) := by exact_mod_cast hApos
    simp only [hZero,Nat.cast_zero,mul_zero] at hB
    exact (not_le_of_gt hAreal) hB.2
  have hCompare : ∀ᶠ H in atTop,
      (Real.log (A H : ℝ)/Real.log (Real.log (H : ℝ))-
        Real.log C/Real.log (Real.log (H : ℝ))≤
          Real.log (B H : ℝ)/Real.log (Real.log (H : ℝ))) ∧
      Real.log (B H : ℝ)/Real.log (Real.log (H : ℝ))≤
        Real.log (A H : ℝ)/Real.log (Real.log (H : ℝ)) := by
    filter_upwards [hBounds,hPositive,loglog_nat_atTop.eventually_gt_atTop 0]
      with H hB hPos hD
    have hAr : 0<(A H : ℝ) := by exact_mod_cast hPos.1
    have hBr : 0<(B H : ℝ) := by exact_mod_cast hPos.2
    have hBA : (B H : ℝ)≤(A H : ℝ) := by exact_mod_cast hB.1
    have hLogLower := Real.log_le_log hAr hB.2
    rw [Real.log_mul hC.ne' hBr.ne'] at hLogLower
    have hDiv := div_le_div_of_nonneg_right hLogLower hD.le
    rw [add_div] at hDiv
    refine ⟨by linarith,?_⟩
    exact div_le_div_of_nonneg_right (Real.log_le_log hBr hBA) hD.le
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hLower hA
    (hCompare.mono fun _ h => h.1) (hCompare.mono fun _ h => h.2)

/-- Natural-count version of the fixed-fiber comparison. -/
theorem of_eventually_mul_sandwich {A B : ℕ→ℕ} {a : ℝ} {C : ℕ}
    (hA : HasLogarithmicCountingExponent A a) (ha : 0<a) (hC : 0<C)
    (hBounds : ∀ᶠ H in atTop,B H≤A H ∧ A H≤C*B H) :
    HasLogarithmicCountingExponent B a := by
  apply hA.of_eventually_real_mul_sandwich (C:=(C : ℝ)) ha (by exact_mod_cast hC)
  filter_upwards [hBounds] with H h
  exact ⟨h.1,by exact_mod_cast h.2⟩

end HasLogarithmicCountingExponent
end
end Z2Z4Rank6
