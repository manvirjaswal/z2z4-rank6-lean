module

public import Z2Z4Rank6.CountingExponentBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

/-!
# Power changes of parameter height

Elementary transport of the logarithmic exponent in Jaswal Remark 6.3,
DOI 10.5281/zenodo.23437117. Floors, positive real powers and constants
are handled explicitly.
-/

namespace Z2Z4Rank6
noncomputable section
open Filter

theorem log_nat_atTop : Tendsto (fun H : ℕ => Real.log (H : ℝ)) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

/-- Positive-power reindexing of a natural height bound. -/
def powerHeightIndex (c d : ℝ) (H : ℕ) : ℕ := ⌊c*(H : ℝ)^d⌋₊

theorem powerHeightIndex_atTop {c d : ℝ} (hc : 0<c) (hd : 0<d) :
    Tendsto (powerHeightIndex c d) atTop atTop :=
  tendsto_nat_floor_atTop.comp
    ((tendsto_rpow_atTop hd).comp tendsto_natCast_atTop_atTop |>.const_mul_atTop hc)

/-- The first logarithm changes by the positive power d; the floor and
constant contribute a vanishing error after division by log H. -/
theorem log_powerHeightIndex_ratio {c d : ℝ} (hc : 0<c) (hd : 0<d) :
    Tendsto (fun H : ℕ => Real.log (powerHeightIndex c d H : ℝ)/Real.log (H : ℝ))
      atTop (nhds d) := by
  let x : ℕ→ℝ := fun H => c*(H : ℝ)^d
  have hx : Tendsto x atTop atTop :=
    ((tendsto_rpow_atTop hd).comp tendsto_natCast_atTop_atTop).const_mul_atTop hc
  have hFloor : Tendsto (fun H : ℕ => (powerHeightIndex c d H : ℝ)/x H)
      atTop (nhds 1) := tendsto_nat_floor_div_atTop.comp hx
  have hLogError : Tendsto (fun H : ℕ =>
      Real.log ((powerHeightIndex c d H : ℝ)/x H)) atTop (nhds 0) := by
    simpa only [Real.log_one] using hFloor.log one_ne_zero
  have hError : Tendsto (fun H : ℕ =>
      Real.log ((powerHeightIndex c d H : ℝ)/x H)/Real.log (H : ℝ))
      atTop (nhds 0) := hLogError.div_atTop log_nat_atTop
  have hConst : Tendsto (fun H : ℕ => Real.log c/Real.log (H : ℝ))
      atTop (nhds 0) := log_nat_atTop.const_div_atTop (Real.log c)
  have hLimit : Tendsto (fun H : ℕ =>
      Real.log ((powerHeightIndex c d H : ℝ)/x H)/Real.log (H : ℝ)+
        Real.log c/Real.log (H : ℝ)+d) atTop (nhds d) := by
    simpa only [zero_add] using (hError.add hConst).add_const d
  apply hLimit.congr'
  filter_upwards [powerHeightIndex_atTop hc hd |>.eventually_gt_atTop 0,
    log_nat_atTop.eventually_gt_atTop 0,eventually_gt_atTop (0 : ℕ)] with H hF hLogH hH
  have hFr : (powerHeightIndex c d H : ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt hF)
  have hHr : 0<(H : ℝ) := by exact_mod_cast hH
  have hxne : x H≠0 := mul_ne_zero hc.ne' (Real.rpow_pos_of_pos hHr d).ne'
  rw [Real.log_div hFr hxne]
  dsimp only [x]
  rw [Real.log_mul hc.ne' (Real.rpow_pos_of_pos hHr d).ne',Real.log_rpow hHr d]
  field_simp [hLogH.ne']; ring

/-- A positive first-log ratio implies a unit second-log ratio. -/
theorem loglog_ratio_of_log_ratio {f : ℕ→ℕ} {d : ℝ}
    (hf : Tendsto f atTop atTop) (hd : 0<d)
    (hLog : Tendsto (fun H : ℕ => Real.log (f H : ℝ)/Real.log (H : ℝ))
      atTop (nhds d)) :
    Tendsto (fun H : ℕ => Real.log (Real.log (f H : ℝ))/
      Real.log (Real.log (H : ℝ))) atTop (nhds 1) := by
  have hLogRatio : Tendsto (fun H : ℕ =>
      Real.log (Real.log (f H : ℝ)/Real.log (H : ℝ))) atTop (nhds (Real.log d)) :=
    hLog.log hd.ne'
  have hSmall := hLogRatio.div_atTop loglog_nat_atTop
  have hLimit : Tendsto (fun H : ℕ => 1+
      Real.log (Real.log (f H : ℝ)/Real.log (H : ℝ))/
        Real.log (Real.log (H : ℝ))) atTop (nhds 1) := by
    simpa only [add_zero] using hSmall.const_add 1
  apply hLimit.congr'
  filter_upwards [(log_nat_atTop.comp hf).eventually_gt_atTop 0,
    log_nat_atTop.eventually_gt_atTop 0,loglog_nat_atTop.eventually_gt_atTop 0]
      with H hLogF hLogH hLogLogH
  change 0<Real.log (f H : ℝ) at hLogF
  rw [Real.log_div hLogF.ne' hLogH.ne']
  field_simp [hLogLogH.ne']; ring

theorem loglog_powerHeightIndex_ratio {c d : ℝ} (hc : 0<c) (hd : 0<d) :
    Tendsto (fun H : ℕ => Real.log (Real.log (powerHeightIndex c d H : ℝ))/
      Real.log (Real.log (H : ℝ))) atTop (nhds 1) :=
  loglog_ratio_of_log_ratio (powerHeightIndex_atTop hc hd) hd (log_powerHeightIndex_ratio hc hd)

namespace HasLogarithmicCountingExponent

/-- Reindex a count whenever the second logarithms of the indices have
unit asymptotic ratio. This lemma has no positive-exponent restriction. -/
theorem comp_of_loglog_ratio {A f : ℕ→ℕ} {a : ℝ}
    (hA : HasLogarithmicCountingExponent A a) (hf : Tendsto f atTop atTop)
    (hRatio : Tendsto (fun H : ℕ => Real.log (Real.log (f H : ℝ))/
      Real.log (Real.log (H : ℝ))) atTop (nhds 1)) :
    HasLogarithmicCountingExponent (A ∘ f) a := by
  have hLimit := (hA.comp hf).mul hRatio
  simp only [mul_one] at hLimit
  apply hLimit.congr'
  filter_upwards [(loglog_nat_atTop.comp hf).eventually_gt_atTop 0] with H hD
  change 0<Real.log (Real.log (f H : ℝ)) at hD
  dsimp only [Function.comp_def]
  field_simp [hD.ne']

/-- A positive real power and a positive constant in a height bound leave
the logarithmic counting exponent unchanged, including the natural floor. -/
theorem comp_powerHeightIndex {A : ℕ→ℕ} {a c d : ℝ}
    (hA : HasLogarithmicCountingExponent A a) (hc : 0<c) (hd : 0<d) :
    HasLogarithmicCountingExponent (A ∘ powerHeightIndex c d) a :=
  hA.comp_of_loglog_ratio (powerHeightIndex_atTop hc hd) (loglog_powerHeightIndex_ratio hc hd)

end HasLogarithmicCountingExponent
end
end Z2Z4Rank6
