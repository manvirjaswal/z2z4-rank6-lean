import Z2Z4Rank6.ProjectiveBaseSchemeIntegral
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.Ideal.GoingUp

/-!
# Dimension of the projective base

Jaswal, DOI 10.5281/zenodo.23437117, Lemma 4.1(a), Theorem 1.2(a).
The chart coordinate rings are finite over one-variable polynomial
rings. Integral incomparability bounds their prime chains. A nonconstant
parameter in a rational-point kernel supplies a strict chain. The two open
charts then compute the topological Krull dimension of Proj.
-/
namespace Z2Z4Rank6.ProjectiveBaseScheme
noncomputable section
open AlgebraicGeometry CategoryTheory
open ProjectiveBaseSchemeCharts
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

private theorem integral_ringKrullDim_le (R A:Type*) [CommRing R] [CommRing A]
    [Algebra R A] [Algebra.IsIntegral R A] : ringKrullDim A≤ringKrullDim R := by
  apply Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap R A))
  intro I J hIJ
  exact Ideal.IsIntegral.under_lt_under hIJ

private theorem polynomial_dimension : ringKrullDim (Polynomial ℚ)=1 := by
  rw [Polynomial.ringKrullDim_of_isNoetherianRing,ringKrullDim_eq_zero_of_field]
  simp

/-- The affine coordinate ring has dimension at most one. -/
theorem affine_ringKrullDim_le_one : ringKrullDim AffineBaseScheme.CoordinateRing≤1 := by
  let : Module.Finite (Polynomial ℚ) AffineBaseScheme.CoordinateRing :=
    Module.Finite.of_basis AffineBaseFunctionFieldIso.coordinateBasis
  exact (integral_ringKrullDim_le (Polynomial ℚ) AffineBaseScheme.CoordinateRing).trans
    polynomial_dimension.le

/-- The infinity-chart ring has dimension at most one. -/
theorem infinity_ringKrullDim_le_one : ringKrullDim InfinityCoordinateRing≤1 := by
  let : Module.Finite (Polynomial ℚ) InfinityCoordinateRing :=
    Module.Finite.of_basis InfinityBaseNormalForm.coordinateBasis
  exact (integral_ringKrullDim_le (Polynomial ℚ) InfinityCoordinateRing).trans
    polynomial_dimension.le

/-- A parameter minus its rational base-point value gives a nonzero element
in the rational-point kernel. Thus the affine chart really has dimension one. -/
theorem affine_ringKrullDim : ringKrullDim AffineBaseScheme.CoordinateRing=1 := by
  apply le_antisymm affine_ringKrullDim_le_one
  apply Order.one_le_krullDim_iff.mpr
  let I : Ideal AffineBaseScheme.CoordinateRing :=
    RingHom.ker (AffineBaseScheme.evaluation baseC0).toRingHom
  let J : PrimeSpectrum AffineBaseScheme.CoordinateRing := ⟨I,RingHom.ker_isPrime _⟩
  refine ⟨⟨⊥,inferInstance⟩,J,?_⟩
  change (⊥:Ideal AffineBaseScheme.CoordinateRing)<I
  apply bot_lt_iff_ne_bot.mpr
  intro hI
  have hz : AffineBaseScheme.m-algebraMap ℚ AffineBaseScheme.CoordinateRing baseC0.m=0 := by
    have hmem : AffineBaseScheme.m-algebraMap ℚ AffineBaseScheme.CoordinateRing baseC0.m∈I := by
      change (AffineBaseScheme.evaluation baseC0)
        (AffineBaseScheme.m-algebraMap ℚ AffineBaseScheme.CoordinateRing baseC0.m)=0
      simp
    simpa only [hI,Ideal.mem_bot] using hmem
  have he := congrArg AffineBaseFunctionFieldIso.coordinateMap hz
  have hm : FunctionField.m=algebraMap ℚ FunctionField.K baseC0.m := by
    simpa only [map_sub,AffineBaseFunctionFieldIso.coordinateMap_m,
      AlgHom.commutes,map_zero,sub_eq_zero] using he
  exact FunctionField.m_transcendental (hm ▸ isAlgebraic_algebraMap baseC0.m)

/-- Topological dimension of the displayed affine scheme. -/
theorem affine_topologicalKrullDim : topologicalKrullDim AffineBaseScheme.scheme=1 := by
  change topologicalKrullDim (PrimeSpectrum AffineBaseScheme.CoordinateRing)=1
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,affine_ringKrullDim]

/-- Topological upper bound on the infinity chart. -/
theorem infinity_topologicalKrullDim_le_one : topologicalKrullDim infinityScheme≤1 := by
  change topologicalKrullDim (PrimeSpectrum InfinityCoordinateRing)≤1
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  exact infinity_ringKrullDim_le_one

private theorem zOpen_dimension : topologicalKrullDim zOpen.toScheme=1 := by
  rw [zChartSchemeIso.hom.homeomorph.isHomeomorph.topologicalKrullDim_eq]
  exact affine_topologicalKrullDim

private theorem mOpen_dimension : topologicalKrullDim mOpen.toScheme≤1 := by
  rw [mChartSchemeIso.hom.homeomorph.isHomeomorph.topologicalKrullDim_eq]
  exact infinity_topologicalKrullDim_le_one

attribute [local instance] specializationOrder

private theorem sober_dimension (Y:Scheme) :
    topologicalKrullDim Y=Order.krullDim Y :=
  Order.krullDim_eq_of_orderIso irreducibleSetEquivPoints

/-- The projective intersection has Krull dimension exactly one. -/
theorem scheme_topologicalKrullDim : topologicalKrullDim scheme=1 := by
  apply le_antisymm
  · rw [sober_dimension,Order.krullDim_eq_iSup_coheight]
    apply iSup_le
    intro x
    have hx : x∈zOpen ∨ x∈mOpen := by
      have h : x∈zOpen⊔mOpen := two_chart_cover.symm ▸ Set.mem_univ x
      exact h
    rcases hx with hx|hx
    · let y : zOpen.toScheme := ⟨x,hx⟩
      have h := Order.coheight_le_krullDim y
      rw [←sober_dimension,zOpen_dimension] at h
      change (Order.coheight (zOpen.ι y):WithBot ℕ∞)≤1
      rw [coheight_eq_of_isOpenImmersion zOpen.ι]
      exact h
    · let y : mOpen.toScheme := ⟨x,hx⟩
      have h := (Order.coheight_le_krullDim y).trans
        ((sober_dimension mOpen.toScheme).symm.le.trans mOpen_dimension)
      change (Order.coheight (mOpen.ι y):WithBot ℕ∞)≤1
      rw [coheight_eq_of_isOpenImmersion mOpen.ι]
      exact h
  · rw [←zOpen_dimension]
    exact zOpen.ι.isOpenEmbedding.isInducing.topologicalKrullDim_le

/-- The base is a nonempty integral proper smooth one-dimensional
rational scheme. -/
theorem actual_curve_geometry : IsIntegral scheme ∧ IsProper structureMap ∧
    SmoothOfRelativeDimension 1 structureMap ∧ topologicalKrullDim scheme=1 :=
  ⟨inferInstance,inferInstance,inferInstance,scheme_topologicalKrullDim⟩

end
end Z2Z4Rank6.ProjectiveBaseScheme
