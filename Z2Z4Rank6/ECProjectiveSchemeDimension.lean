module

public import Z2Z4Rank6.ECProjectiveSchemeIntegral
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.Ideal.GoingUp

@[expose] public section

/-!
# Dimension of the projective printed EC cubic

Jaswal, DOI 10.5281/zenodo.23437117, Lemma 4.1(a), Theorem 1.2(a).
The chart coordinate rings are finite over one-variable polynomial
rings. Integral incomparability bounds their prime chains. A nonconstant
parameter in a rational-point kernel supplies a strict chain. The two open
charts then compute the topological Krull dimension of Proj.
-/
namespace Z2Z4Rank6.ECProjectiveScheme
noncomputable section
open AlgebraicGeometry CategoryTheory
open ECProjectiveSchemeCharts ECProjectiveSchemeInfinity
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
theorem affine_ringKrullDim_le_one : ringKrullDim ECProjectiveSchemeAffine.CoordinateRing≤1 := by
  let : Module.Finite (Polynomial ℚ) ECProjectiveSchemeAffine.CoordinateRing :=
    Module.Finite.of_basis ECProjectiveAffineFunctionField.coordinateBasis
  exact (integral_ringKrullDim_le (Polynomial ℚ) ECProjectiveSchemeAffine.CoordinateRing).trans
    polynomial_dimension.le

/-- The infinity-chart ring has dimension at most one. -/
theorem infinity_ringKrullDim_le_one : ringKrullDim ECProjectiveSchemeInfinity.CoordinateRing≤1 := by
  exact (integral_ringKrullDim_le (Polynomial ℚ) ECProjectiveSchemeInfinity.CoordinateRing).trans
    polynomial_dimension.le

/-- A parameter minus its rational base-point value gives a nonzero element
in the rational-point kernel. Thus the affine chart really has dimension one. -/
theorem affine_ringKrullDim : ringKrullDim ECProjectiveSchemeAffine.CoordinateRing=1 := by
  apply le_antisymm affine_ringKrullDim_le_one
  apply Order.one_le_krullDim_iff.mpr
  let phi := ECProjectiveSchemeAffine.evaluation 404 0
    ((ec_equation_iff 404 0).mpr (by norm_num))
  let I : Ideal ECProjectiveSchemeAffine.CoordinateRing := RingHom.ker phi.toRingHom
  let J : PrimeSpectrum ECProjectiveSchemeAffine.CoordinateRing := ⟨I,RingHom.ker_isPrime _⟩
  refine ⟨⟨⊥,inferInstance⟩,J,?_⟩
  change (⊥:Ideal ECProjectiveSchemeAffine.CoordinateRing)<I
  apply bot_lt_iff_ne_bot.mpr
  intro hI
  have hphi : phi ECProjectiveSchemeAffine.x=404 := by
    change (MvPolynomial.aeval ![(404:ℚ),0]) (MvPolynomial.X 0)=404
    simp
  have hz : ECProjectiveSchemeAffine.x-algebraMap ℚ ECProjectiveSchemeAffine.CoordinateRing 404=0 := by
    have hmem : ECProjectiveSchemeAffine.x-algebraMap ℚ ECProjectiveSchemeAffine.CoordinateRing 404∈I := by
      change phi (ECProjectiveSchemeAffine.x-algebraMap ℚ ECProjectiveSchemeAffine.CoordinateRing 404)=0
      simp [hphi]
    simpa only [hI,Ideal.mem_bot] using hmem
  have he := congrArg ECProjectiveAffineFunctionField.coordinateMap hz
  have hx : ECFunctionField.x=algebraMap ℚ ECFunctionField.K 404 := by
    simpa only [map_sub,ECProjectiveAffineFunctionField.coordinateMap_x,
      AlgHom.commutes,map_zero,sub_eq_zero] using he
  exact ECFunctionField.x_transcendental (hx ▸ isAlgebraic_algebraMap (404:ℚ))

/-- Topological dimension of the displayed affine scheme. -/
theorem affine_topologicalKrullDim : topologicalKrullDim ECProjectiveSchemeAffine.scheme=1 := by
  change topologicalKrullDim (PrimeSpectrum ECProjectiveSchemeAffine.CoordinateRing)=1
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,affine_ringKrullDim]

/-- Topological upper bound on the infinity chart. -/
theorem infinity_topologicalKrullDim_le_one : topologicalKrullDim ECProjectiveSchemeInfinity.scheme≤1 := by
  change topologicalKrullDim (PrimeSpectrum ECProjectiveSchemeInfinity.CoordinateRing)≤1
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  exact infinity_ringKrullDim_le_one

private theorem zOpen_dimension : topologicalKrullDim zOpen.toScheme=1 := by
  rw [zChartSchemeIso.hom.homeomorph.isHomeomorph.topologicalKrullDim_eq]
  exact affine_topologicalKrullDim

private theorem yOpen_dimension : topologicalKrullDim yOpen.toScheme≤1 := by
  rw [yChartSchemeIso.hom.homeomorph.isHomeomorph.topologicalKrullDim_eq]
  exact infinity_topologicalKrullDim_le_one

attribute [local instance] specializationOrder

private theorem sober_dimension (Y:Scheme) :
    topologicalKrullDim Y=Order.krullDim Y :=
  Order.krullDim_eq_of_orderIso irreducibleSetEquivPoints

/-- The projective cubic has Krull dimension exactly one. -/
theorem scheme_topologicalKrullDim : topologicalKrullDim scheme=1 := by
  apply le_antisymm
  · rw [sober_dimension,Order.krullDim_eq_iSup_coheight]
    apply iSup_le
    intro x
    have hx : x∈zOpen ∨ x∈yOpen := by
      have h : x∈zOpen⊔yOpen := two_chart_cover.symm ▸ Set.mem_univ x
      exact h
    rcases hx with hx|hx
    · let y : zOpen.toScheme := ⟨x,hx⟩
      have h := Order.coheight_le_krullDim y
      rw [←sober_dimension,zOpen_dimension] at h
      change (Order.coheight (zOpen.ι y):WithBot ℕ∞)≤1
      rw [coheight_eq_of_isOpenImmersion zOpen.ι]
      exact h
    · let y : yOpen.toScheme := ⟨x,hx⟩
      have h := (Order.coheight_le_krullDim y).trans
        ((sober_dimension yOpen.toScheme).symm.le.trans yOpen_dimension)
      change (Order.coheight (yOpen.ι y):WithBot ℕ∞)≤1
      rw [coheight_eq_of_isOpenImmersion yOpen.ι]
      exact h
  · rw [←zOpen_dimension]
    exact zOpen.ι.isOpenEmbedding.isInducing.topologicalKrullDim_le

/-- The cubic is a nonempty integral proper smooth one-dimensional
rational scheme. -/
theorem actual_curve_geometry : IsIntegral scheme ∧ IsProper structureMap ∧
    SmoothOfRelativeDimension 1 structureMap ∧ topologicalKrullDim scheme=1 :=
  ⟨inferInstance,inferInstance,inferInstance,scheme_topologicalKrullDim⟩

end
end Z2Z4Rank6.ECProjectiveScheme
