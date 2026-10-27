import Z2Z4Rank6.ProjectiveBaseSchemeSmooth
import Z2Z4Rank6.ProjectiveBaseSchemeRationalPoints
import Z2Z4Rank6.InfinityBaseOverlapInjective

/-!
# Integrality of the projective base

Jaswal, DOI 10.5281/zenodo.23437117, Lemma 4.1(a) and Theorem 1.2(a).
The two affine chart rings are domains. Their nonempty overlap and
the proved two-chart cover establish integrality of the Proj scheme.
-/
namespace Z2Z4Rank6.AffineBaseFunctionFieldIso
noncomputable section

/-- The displayed affine parameter is nonzero in the coordinate ring. -/
theorem affine_m_ne_zero : AffineBaseScheme.m≠0 := by
  intro h
  have hm := congrArg coordinateMap h
  apply FunctionField.m_ne_zero
  simpa only [coordinateMap_m,map_zero] using hm

/-- The overlap localization is a domain. -/
instance overlapRingIsDomain : IsDomain OverlapRing := by
  apply IsLocalization.isDomain_of_le_nonZeroDivisors (R:=CoordinateRing) (M:=overlapDenominators) OverlapRing
  rw [overlapDenominators_eq]
  rintro x ⟨n,rfl⟩
  exact mem_nonZeroDivisors_iff_ne_zero.mpr (pow_ne_zero n affine_m_ne_zero)

/-- The chart at infinity embeds in the domain overlap. -/
instance infinityCoordinateRingIsDomain : IsDomain ProjectiveBaseSchemeCharts.InfinityCoordinateRing :=
  infinityRestriction_injective.isDomain infinityRestriction

end
end Z2Z4Rank6.AffineBaseFunctionFieldIso

namespace Z2Z4Rank6.ProjectiveBaseScheme
noncomputable section
open AlgebraicGeometry CategoryTheory
open ProjectiveBaseSchemeCharts ProjectiveBaseSchemeRationalPoints
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

instance affineSchemeIntegral : IsIntegral AffineBaseScheme.scheme := by
  dsimp [AffineBaseScheme.scheme]
  infer_instance

instance infinitySchemeIntegral : IsIntegral infinityScheme := by
  dsimp [infinityScheme]
  infer_instance

instance zOpenIntegral : IsIntegral zOpen.toScheme :=
  IsIntegral.of_isIso zChartSchemeIso.inv

instance mOpenIntegral : IsIntegral mOpen.toScheme :=
  IsIntegral.of_isIso mChartSchemeIso.inv

/-- The homogeneous ratio m/z describes the chart overlap. -/
theorem zChart_preimage_mOpen :
    chartInclusion 3 ⁻¹ᵁ mOpen=PrimeSpectrum.basicOpen (ratio 3 0) := by
  change Proj.awayι grading z (coordinate_degree 3) (by decide : 0<1) ⁻¹ᵁ
    Proj.basicOpen grading m=_
  rw [Proj.awayι_preimage_basicOpen grading (coordinate_degree 3) (by decide : 0<1)
    (coordinate_degree 0) (by decide : 0<1)]
  congr 1
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.Away.isLocalizationElem,HomogeneousLocalization.Away.val_mk,
    ratio,pow_one]

/-- The overlap, in the displayed affine coordinates, is m≠0. -/
theorem zInclusion_preimage_mOpen :
    zInclusion ⁻¹ᵁ mOpen=PrimeSpectrum.basicOpen AffineBaseScheme.m := by
  have hf : zInclusion=Spec.map (CommRingCat.ofHom zChartRingEquiv.toRingHom) ≫
      chartInclusion 3 := by
    rfl
  rw [hf,Scheme.Hom.comp_preimage,zChart_preimage_mOpen]
  change PrimeSpectrum.basicOpen (zChartRingEquiv (ratio 3 0))=_
  change PrimeSpectrum.basicOpen (chartToAffine (ratio 3 0))=_
  rw [chartToAffine_ratio]
  rfl

/-- A printed rational point has m≠0, so the two charts meet. -/
theorem chart_overlap_nonempty : ((zOpen: Set scheme)∩mOpen).Nonempty := by
  let q : AffineBaseScheme.scheme := PrimeSpectrum.comap
    (AffineBaseScheme.evaluation baseC0).toRingHom ⟨⊥,inferInstance⟩
  have hq : q∈PrimeSpectrum.basicOpen AffineBaseScheme.m := by
    change (AffineBaseScheme.evaluation baseC0) AffineBaseScheme.m∉(⊥:Ideal ℚ)
    simp [baseC0]
  refine ⟨zInclusion q,?_,?_⟩
  · rw [←zInclusion_opensRange]
    exact ⟨q,rfl⟩
  · exact show q∈zInclusion ⁻¹ᵁ mOpen from zInclusion_preimage_mOpen.symm ▸ hq

/-- The projective scheme is reduced, checked on its two affine charts. -/
instance schemeReduced : IsReduced scheme := by
  have hstalk (x:scheme) : _root_.IsReduced (scheme.presheaf.stalk x) := by
    have hx : x∈zOpen ∨ x∈mOpen := by
      have h : x∈zOpen⊔mOpen := two_chart_cover.symm ▸ Set.mem_univ x
      exact h
    rcases hx with hx|hx
    · let y : zOpen.toScheme := ⟨x,hx⟩
      exact isReduced_of_injective (zOpen.ι.stalkMap y).hom
        (asIso (zOpen.ι.stalkMap y)).commRingCatIsoToRingEquiv.injective
    · let y : mOpen.toScheme := ⟨x,hx⟩
      exact isReduced_of_injective (mOpen.ι.stalkMap y).hom
        (asIso (mOpen.ι.stalkMap y)).commRingCatIsoToRingEquiv.injective
  exact isReduced_of_isReduced_stalk scheme

/-- An open cover by two irreducible charts with nonempty overlap is irreducible. -/
instance schemeIrreducible : IrreducibleSpace scheme := by
  let : IrreducibleSpace (zOpen:Set scheme) := by
    change IrreducibleSpace zOpen.toScheme
    infer_instance
  let : IrreducibleSpace (mOpen:Set scheme) := by
    change IrreducibleSpace mOpen.toScheme
    infer_instance
  have hz : IsIrreducible (zOpen:Set scheme) := IsIrreducible.of_subtype
  have hm : IsIrreducible (mOpen:Set scheme) := IsIrreducible.of_subtype
  have hcover (x:scheme) : x∈zOpen ∨ x∈mOpen := by
    have h : x∈zOpen⊔mOpen := two_chart_cover.symm ▸ Set.mem_univ x
    exact h
  refine { isPreirreducible_univ := ?_, toNonempty := ⟨chart_overlap_nonempty.choose⟩ }
  intro U V hU hV hUn hVn
  obtain ⟨x,_,hx⟩ := hUn
  obtain ⟨y,_,hy⟩ := hVn
  rcases hcover x with hxz|hxm <;> rcases hcover y with hyz|hym
  · obtain ⟨t,_,ht⟩ := hz.2 U V hU hV ⟨x,hxz,hx⟩ ⟨y,hyz,hy⟩
    exact ⟨t,Set.mem_univ t,ht⟩
  · obtain ⟨t,htz,htU,htm⟩ := hz.2 U mOpen hU mOpen.isOpen
      ⟨x,hxz,hx⟩ chart_overlap_nonempty
    obtain ⟨s,_,hs⟩ := hm.2 U V hU hV ⟨t,htm,htU⟩ ⟨y,hym,hy⟩
    exact ⟨s,Set.mem_univ s,hs⟩
  · obtain ⟨t,htz,htV,htm⟩ := hz.2 V mOpen hV mOpen.isOpen
      ⟨y,hyz,hy⟩ chart_overlap_nonempty
    obtain ⟨s,_,hs⟩ := hm.2 U V hU hV ⟨x,hxm,hx⟩ ⟨t,htm,htV⟩
    exact ⟨s,Set.mem_univ s,hs⟩
  · obtain ⟨t,_,ht⟩ := hm.2 U V hU hV ⟨x,hxm,hx⟩ ⟨y,hym,hy⟩
    exact ⟨t,Set.mem_univ t,ht⟩

/-- Integrality is the Mathlib predicate for the Proj scheme. -/
instance schemeIntegral : IsIntegral scheme :=
  isIntegral_of_irreducibleSpace_of_isReduced scheme

end
end Z2Z4Rank6.ProjectiveBaseScheme
