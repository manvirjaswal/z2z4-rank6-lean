module

public import Z2Z4Rank6.ECProjectiveSchemeSmooth
public import Z2Z4Rank6.ECProjectiveInfinityCoordinate
public import Z2Z4Rank6.ECProjectiveAffineNormalForm

@[expose] public section

/-! Integrality of the projective printed EC cubic. Both
chart rings are domains; the standard affine chart meets the chart at
infinity, so the proved two-chart cover gives a reduced irreducible scheme.
Source: Jaswal, DOI 10.5281/zenodo.23437117, Theorem 1.2(a), Lemma 4.1. -/
namespace Z2Z4Rank6.ECProjectiveScheme
noncomputable section
open AlgebraicGeometry CategoryTheory
open ECProjectiveSchemeCharts ECProjectiveSchemeInfinity
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

theorem affine_y_ne_zero : ECProjectiveSchemeAffine.y≠0 := by
  intro h
  have he := congrArg ECProjectiveAffineFunctionField.coordinateMap h
  have hi := congrArg QuadraticAlgebra.im he
  norm_num [ECProjectiveAffineFunctionField.coordinateMap_y,ECFunctionField.y] at hi

def zInclusion : ECProjectiveSchemeAffine.scheme ⟶ scheme := zChartSchemeIso.inv ≫ zOpen.ι
instance zInclusionOpenImmersion : IsOpenImmersion zInclusion := by
  dsimp only [zInclusion]
  infer_instance

theorem zInclusion_opensRange : zInclusion.opensRange=zOpen := by
  dsimp only [zInclusion]
  rw [Scheme.Hom.opensRange_comp_of_isIso,Scheme.Opens.opensRange_ι]

instance affineSchemeIntegral : IsIntegral ECProjectiveSchemeAffine.scheme := by
  dsimp [ECProjectiveSchemeAffine.scheme]
  infer_instance

instance infinitySchemeIntegral : IsIntegral ECProjectiveSchemeInfinity.scheme := by
  dsimp [ECProjectiveSchemeInfinity.scheme]
  infer_instance

instance zOpenIntegral : IsIntegral zOpen.toScheme :=
  IsIntegral.of_isIso zChartSchemeIso.inv

instance yOpenIntegral : IsIntegral yOpen.toScheme :=
  IsIntegral.of_isIso yChartSchemeIso.inv

/-- The homogeneous ratio y/z describes the chart overlap. -/
theorem zChart_preimage_yOpen :
    chartInclusion 2 ⁻¹ᵁ yOpen=PrimeSpectrum.basicOpen (ratio 2 1) := by
  change Proj.awayι grading z (coordinate_degree 2) (by decide : 0<1) ⁻¹ᵁ
    Proj.basicOpen grading y=_
  rw [Proj.awayι_preimage_basicOpen grading (coordinate_degree 2) (by decide : 0<1)
    (coordinate_degree 1) (by decide : 0<1)]
  congr 1
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.Away.isLocalizationElem,HomogeneousLocalization.Away.val_mk,
    ratio,pow_one]

/-- The overlap, in the displayed affine coordinates, is y≠0. -/
theorem zInclusion_preimage_yOpen :
    zInclusion ⁻¹ᵁ yOpen=PrimeSpectrum.basicOpen ECProjectiveSchemeAffine.y := by
  have hf : zInclusion=Spec.map (CommRingCat.ofHom zChartRingEquiv.toRingHom) ≫
      chartInclusion 2 := by
    rfl
  rw [hf,Scheme.Hom.comp_preimage,zChart_preimage_yOpen]
  change PrimeSpectrum.basicOpen (zChartRingEquiv (ratio 2 1))=_
  change PrimeSpectrum.basicOpen (chartToAffine (ratio 2 1))=_
  rw [chartToAffine_ratio]
  rfl

/-- The nonempty standard affine chart meets the chart containing infinity. -/
theorem chart_overlap_nonempty : ((zOpen: Set scheme)∩yOpen).Nonempty := by
  let q : ECProjectiveSchemeAffine.scheme := ⟨⊥,inferInstance⟩
  have hq : q∈PrimeSpectrum.basicOpen ECProjectiveSchemeAffine.y := by
    change ECProjectiveSchemeAffine.y∉(⊥:Ideal ECProjectiveSchemeAffine.CoordinateRing)
    simpa only [Ideal.mem_bot] using affine_y_ne_zero
  refine ⟨zInclusion q,?_,?_⟩
  · rw [←zInclusion_opensRange]
    exact ⟨q,rfl⟩
  · exact show q∈zInclusion ⁻¹ᵁ yOpen from zInclusion_preimage_yOpen.symm ▸ hq

/-- The projective scheme is reduced, checked on its two affine charts. -/
instance schemeReduced : IsReduced scheme := by
  have hstalk (x:scheme) : _root_.IsReduced (scheme.presheaf.stalk x) := by
    have hx : x∈zOpen ∨ x∈yOpen := by
      have h : x∈zOpen⊔yOpen := two_chart_cover.symm ▸ Set.mem_univ x
      exact h
    rcases hx with hx|hx
    · let y : zOpen.toScheme := ⟨x,hx⟩
      exact isReduced_of_injective (zOpen.ι.stalkMap y).hom
        (asIso (zOpen.ι.stalkMap y)).commRingCatIsoToRingEquiv.injective
    · let y : yOpen.toScheme := ⟨x,hx⟩
      exact isReduced_of_injective (yOpen.ι.stalkMap y).hom
        (asIso (yOpen.ι.stalkMap y)).commRingCatIsoToRingEquiv.injective
  exact isReduced_of_isReduced_stalk scheme

/-- An open cover by two irreducible charts with nonempty overlap is irreducible. -/
instance schemeIrreducible : IrreducibleSpace scheme := by
  let : IrreducibleSpace (zOpen:Set scheme) := by
    change IrreducibleSpace zOpen.toScheme
    infer_instance
  let : IrreducibleSpace (yOpen:Set scheme) := by
    change IrreducibleSpace yOpen.toScheme
    infer_instance
  have hz : IsIrreducible (zOpen:Set scheme) := IsIrreducible.of_subtype
  have hm : IsIrreducible (yOpen:Set scheme) := IsIrreducible.of_subtype
  have hcover (x:scheme) : x∈zOpen ∨ x∈yOpen := by
    have h : x∈zOpen⊔yOpen := two_chart_cover.symm ▸ Set.mem_univ x
    exact h
  refine { isPreirreducible_univ := ?_, toNonempty := ⟨chart_overlap_nonempty.choose⟩ }
  intro U V hU hV hUn hVn
  obtain ⟨x,_,hx⟩ := hUn
  obtain ⟨y,_,hy⟩ := hVn
  rcases hcover x with hxz|hxm <;> rcases hcover y with hyz|hym
  · obtain ⟨t,_,ht⟩ := hz.2 U V hU hV ⟨x,hxz,hx⟩ ⟨y,hyz,hy⟩
    exact ⟨t,Set.mem_univ t,ht⟩
  · obtain ⟨t,htz,htU,htm⟩ := hz.2 U yOpen hU yOpen.isOpen
      ⟨x,hxz,hx⟩ chart_overlap_nonempty
    obtain ⟨s,_,hs⟩ := hm.2 U V hU hV ⟨t,htm,htU⟩ ⟨y,hym,hy⟩
    exact ⟨s,Set.mem_univ s,hs⟩
  · obtain ⟨t,htz,htV,htm⟩ := hz.2 V yOpen hV yOpen.isOpen
      ⟨y,hyz,hy⟩ chart_overlap_nonempty
    obtain ⟨s,_,hs⟩ := hm.2 U V hU hV ⟨x,hxm,hx⟩ ⟨t,htm,htV⟩
    exact ⟨s,Set.mem_univ s,hs⟩
  · obtain ⟨t,_,ht⟩ := hm.2 U V hU hV ⟨x,hxm,hx⟩ ⟨y,hym,hy⟩
    exact ⟨t,Set.mem_univ t,ht⟩

/-- Integrality is the Mathlib predicate for the Proj scheme. -/
instance schemeIntegral : IsIntegral scheme :=
  isIntegral_of_irreducibleSpace_of_isReduced scheme

end
end Z2Z4Rank6.ECProjectiveScheme
