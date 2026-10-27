module

public import Z2Z4Rank6.BoundedHeightCounting

@[expose] public section

/-!
# Adding finitely many objects to bounded counts

The reverse finite-exception bridge for Jaswal Remark 6.3,
DOI 10.5281/zenodo.23437117. The known count is the smaller one here.
-/

namespace Z2Z4Rank6
noncomputable section
open Filter

namespace HasLogarithmicCountingExponent

/-- Increasing a count by at most a fixed positive factor preserves a
positive logarithmic exponent. The known count is the lower one. -/
theorem of_eventually_real_mul_upper_sandwich {N M : ℕ→ℕ} {a C : ℝ}
    (hN : HasLogarithmicCountingExponent N a) (ha : 0<a) (hC : 0<C)
    (hBounds : ∀ᶠ H in atTop,N H≤M H ∧ (M H : ℝ)≤C*(N H : ℝ)) :
    HasLogarithmicCountingExponent M a := by
  have hError : Tendsto (fun H : ℕ => Real.log C/Real.log (Real.log (H : ℝ)))
      atTop (nhds 0) := loglog_nat_atTop.const_div_atTop (Real.log C)
  have hUpper : Tendsto (fun H : ℕ =>
      Real.log (N H : ℝ)/Real.log (Real.log (H : ℝ))+
        Real.log C/Real.log (Real.log (H : ℝ))) atTop (nhds a) := by
    simpa only [add_zero] using hN.add hError
  have hCompare : ∀ᶠ H in atTop,
      Real.log (N H : ℝ)/Real.log (Real.log (H : ℝ))≤
        Real.log (M H : ℝ)/Real.log (Real.log (H : ℝ)) ∧
      Real.log (M H : ℝ)/Real.log (Real.log (H : ℝ))≤
        Real.log (N H : ℝ)/Real.log (Real.log (H : ℝ))+
          Real.log C/Real.log (Real.log (H : ℝ)) := by
    filter_upwards [hBounds,hN.eventually_pos ha,loglog_nat_atTop.eventually_gt_atTop 0]
      with H hB hPos hD
    have hNReal : 0<(N H : ℝ) := by exact_mod_cast hPos
    have hMReal : 0<(M H : ℝ) := by exact_mod_cast (lt_of_lt_of_le hPos hB.1)
    have hNM : (N H : ℝ)≤(M H : ℝ) := by exact_mod_cast hB.1
    have hLog := Real.log_le_log hMReal hB.2
    rw [Real.log_mul hC.ne' hNReal.ne'] at hLog
    have hDiv := div_le_div_of_nonneg_right hLog hD.le
    rw [add_div] at hDiv
    exact ⟨div_le_div_of_nonneg_right (Real.log_le_log hNReal hNM) hD.le,by linarith⟩
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hN hUpper
    (hCompare.mono fun _ h => h.1) (hCompare.mono fun _ h => h.2)

theorem of_eventually_mul_upper_sandwich {N M : ℕ→ℕ} {a : ℝ} {C : ℕ}
    (hN : HasLogarithmicCountingExponent N a) (ha : 0<a) (hC : 0<C)
    (hBounds : ∀ᶠ H in atTop,N H≤M H ∧ M H≤C*N H) :
    HasLogarithmicCountingExponent M a := by
  apply hN.of_eventually_real_mul_upper_sandwich (C:=(C : ℝ)) ha (by exact_mod_cast hC)
  filter_upwards [hBounds] with H h
  exact ⟨h.1,by exact_mod_cast h.2⟩

/-- Adding at most a fixed number of objects preserves a positive
logarithmic exponent. The original smaller count tends to infinity. -/
theorem of_eventually_add_upper_sandwich {N M : ℕ→ℕ} {a : ℝ} {C : ℕ}
    (hN : HasLogarithmicCountingExponent N a) (ha : 0<a)
    (hBounds : ∀ᶠ H in atTop,N H≤M H ∧ M H≤N H+C) :
    HasLogarithmicCountingExponent M a := by
  apply hN.of_eventually_mul_upper_sandwich ha (show 0<(2 : ℕ) by decide)
  filter_upwards [hBounds,(hN.tendsto_atTop ha).eventually_ge_atTop C] with H hB hC
  exact ⟨hB.1,by omega⟩

end HasLogarithmicCountingExponent

namespace BoundedHeightCounting
variable {α : Type*}

/-- Recover all bounded objects from a cofinite restriction. Finiteness
of the full bounded sets is proved from a finite union. -/
theorem counting_of_cofinite_restriction {h : α→ℕ} {S : Set α} {a : ℝ}
    (hFinite : ∀ H,(boundedSet h H∩S).Finite)
    (hCount : HasLogarithmicCountingExponent (restrictedCount h S) a) (ha : 0<a)
    (hExceptional : Sᶜ.Finite) :
    (∀ H,(boundedSet h H).Finite) ∧ HasLogarithmicCountingExponent (count h) a := by
  have hFull : ∀ H,(boundedSet h H).Finite := by
    intro H
    apply ((hFinite H).union hExceptional).subset
    intro x hx
    by_cases hS : x∈S
    · exact Or.inl ⟨hx,hS⟩
    · exact Or.inr hS
  refine ⟨hFull,?_⟩
  apply hCount.of_eventually_add_upper_sandwich (C:=Sᶜ.ncard) ha
  apply Eventually.of_forall
  intro H
  refine ⟨Set.ncard_le_ncard Set.inter_subset_left (hFull H),?_⟩
  simpa only [count,restrictedCount,Set.sdiff_compl] using
    Set.ncard_le_ncard_sdiff_add_ncard (boundedSet h H) Sᶜ hExceptional

end BoundedHeightCounting
end
end Z2Z4Rank6
