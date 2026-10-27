import Z2Z4Rank6.HeightInvariantForms
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Order.Compact

/-!
# Raw archimedean invariant-height growth

Jaswal, DOI 10.5281/zenodo.23437117, Remark 6.3.
For the binary integral model, max(|c4|³,|c6|²) is bounded above
and below by positive constant multiples of max(|x0|,|x1|)^48. The proof
uses the proved degree 48 scaling and absence of common projective zeros,
then compactness of the max-norm unit sphere. This file treats raw invariants. Primitive short-model normalization and
point counting are proved in the corresponding family-height and counting
modules.
-/
namespace Z2Z4Rank6.HeightInvariantForms
noncomputable section

/-- Raw weighted invariant size of the displayed binary model. -/
def rawHeight (x : ℝ×ℝ) : ℝ := max (|c4 x.1 x.2|^3) (|c6 x.1 x.2|^2)

theorem rawHeight_nonneg (x : ℝ×ℝ) : 0≤rawHeight x :=
  le_max_of_le_left (pow_nonneg (abs_nonneg _) _)

theorem rawHeight_pos (x : ℝ×ℝ) (hx : x≠0) : 0<rawHeight x := by
  have hcoord : x.1≠0 ∨ x.2≠0 := by
    by_contra h
    push Not at h
    exact hx (Prod.ext h.1 h.2)
  have h := invariants_not_both_zero x.1 x.2 hcoord
  by_cases h4 : c4 x.1 x.2=0
  · have h6 : c6 x.1 x.2≠0 := fun h6 => h ⟨h4,h6⟩
    exact lt_max_iff.mpr (Or.inr (pow_pos (abs_pos.mpr h6) 2))
  · exact lt_max_iff.mpr (Or.inl (pow_pos (abs_pos.mpr h4) 3))

@[simp] theorem rawHeight_zero : rawHeight 0=0 := by
  norm_num [rawHeight,c4,c6,binaryModel,E_c4,E_c6,binaryA,binaryB]

theorem rawHeight_continuous : Continuous rawHeight := by
  unfold rawHeight c4 c6 binaryModel
  simp only [E_c4,E_c6,binaryA,binaryB]
  fun_prop

/-- Exact real degree 48 scaling, including negative and zero scalars. -/
theorem rawHeight_scale (t : ℝ) (x : ℝ×ℝ) :
    rawHeight (t • x)=|t|^48*rawHeight x := by
  simp only [rawHeight,Prod.smul_fst,Prod.smul_snd,smul_eq_mul,c4_scale,c6_scale,
    abs_mul,abs_pow,mul_pow,←pow_mul]
  exact (mul_max_of_nonneg _ _ (pow_nonneg (abs_nonneg t) 48)).symm

/-- Compactness gives uniform positive lower and upper constants for the
raw invariant height on every real pair, including the zero pair. -/
theorem rawHeight_bounds_norm : ∃ L U : ℝ, 0<L ∧ 0<U ∧
    ∀ x : ℝ×ℝ, L*‖x‖^48≤rawHeight x ∧ rawHeight x≤U*‖x‖^48 := by
  have hcompact : IsCompact (Metric.sphere (0 : ℝ×ℝ) 1) := isCompact_sphere 0 1
  have hnonempty : (Metric.sphere (0 : ℝ×ℝ) 1).Nonempty := by
    refine ⟨(1,0),?_⟩
    simp [Prod.norm_def]
  have hpos : ∀ x∈Metric.sphere (0 : ℝ×ℝ) 1, 0<rawHeight x := by
    intro x hx
    apply rawHeight_pos
    intro h
    simp [h] at hx
  obtain ⟨L,hL,hLower⟩ := hcompact.exists_forall_le' rawHeight_continuous.continuousOn hpos
  obtain ⟨z,hz,hUpper⟩ := hcompact.exists_isMaxOn hnonempty rawHeight_continuous.continuousOn
  refine ⟨L,rawHeight z,hL,hpos z hz,?_⟩
  intro x
  by_cases hx : x=0
  · simp [hx]
  · let y : ℝ×ℝ := ‖x‖⁻¹ • x
    have hnorm : 0<‖x‖ := norm_pos_iff.mpr hx
    have hy : y∈Metric.sphere (0 : ℝ×ℝ) 1 := by
      simp only [Metric.mem_sphere,dist_zero_right,y,norm_smul,norm_inv,Real.norm_eq_abs,
        abs_of_pos hnorm,inv_mul_cancel₀ hnorm.ne']
    have hxy : ‖x‖ • y=x := by
      dsimp [y]
      rw [smul_smul,mul_inv_cancel₀ hnorm.ne',one_smul]
    have hheight : rawHeight x=‖x‖^48*rawHeight y := by
      calc
        rawHeight x=rawHeight (‖x‖ • y) := congrArg rawHeight hxy.symm
        _=|‖x‖|^48*rawHeight y := rawHeight_scale _ _
        _=‖x‖^48*rawHeight y := by rw [abs_of_pos hnorm]
    rw [hheight]
    constructor
    · simpa [mul_comm] using mul_le_mul_of_nonneg_left (hLower y hy) (pow_nonneg (norm_nonneg x) 48)
    · simpa [mul_comm] using mul_le_mul_of_nonneg_left (hUpper hy) (pow_nonneg (norm_nonneg x) 48)

/-- The raw invariant size is comparable to max(|x0|,|x1|)^48. This does
not assert the comparison with minimal normalized elliptic-curve height. -/
theorem rawHeight_bounds : ∃ L U : ℝ, 0<L ∧ 0<U ∧
    ∀ x₀ x₁ : ℝ, L*(max |x₀| |x₁|)^48≤rawHeight (x₀,x₁) ∧
      rawHeight (x₀,x₁)≤U*(max |x₀| |x₁|)^48 := by
  obtain ⟨L,U,hL,hU,h⟩ := rawHeight_bounds_norm
  refine ⟨L,U,hL,hU,?_⟩
  intro x₀ x₁
  simpa only [Prod.norm_def,Real.norm_eq_abs] using h (x₀,x₁)

end
end Z2Z4Rank6.HeightInvariantForms
