import Z2Z4Rank6.ThirdTwistCoverRingDimension
import Z2Z4Rank6.ThirdTwistCoverProjectiveCharts

/-!
# Dimension of the weighted projective third-twist base

The two-chart cover and chart isomorphisms transfer the
proved exact ring dimensions to topological Krull dimension 1 of both Proj
schemes.
Source: Jaswal, Section 7, DOI 10.5281/zenodo.23437117.
-/
namespace Z2Z4Rank6.ThirdTwistCoverDimension
noncomputable section
open AlgebraicGeometry CategoryTheory
open ThirdTwistCoverProjective ThirdTwistCoverProjectiveCharts
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

theorem zOpen_topologicalKrullDim  :
    topologicalKrullDim (zOpen).toScheme=1 := by
  rw [(zChartSchemeIso).hom.homeomorph.isHomeomorph.topologicalKrullDim_eq]
  exact affine_topologicalKrullDim

theorem mOpen_topologicalKrullDim  :
    topologicalKrullDim (mOpen).toScheme=1 := by
  rw [(mChartSchemeIso).hom.homeomorph.isHomeomorph.topologicalKrullDim_eq]
  exact infinity_topologicalKrullDim

attribute [local instance] specializationOrder

private theorem sober_dimension (Y : Scheme) :
    topologicalKrullDim Y=Order.krullDim Y :=
  Order.krullDim_eq_of_orderIso irreducibleSetEquivPoints

/-- The third-twist projective base has dimension exactly 1.
The result is unconditional, before any geometric-integrality criterion. -/
theorem scheme_topologicalKrullDim  : topologicalKrullDim (scheme)=1 := by
  apply le_antisymm
  · rw [sober_dimension,Order.krullDim_eq_iSup_coheight]
    apply iSup_le
    intro x
    have hx : x∈zOpen ∨ x∈mOpen := by
      have h : x∈zOpen⊔mOpen := (two_chart_cover).symm ▸ Set.mem_univ x
      exact h
    rcases hx with hx|hx
    · let y : (zOpen).toScheme := ⟨x,hx⟩
      have h := Order.coheight_le_krullDim y
      rw [←sober_dimension,zOpen_topologicalKrullDim] at h
      change (Order.coheight ((zOpen).ι y):WithBot ℕ∞)≤1
      rw [coheight_eq_of_isOpenImmersion (zOpen).ι]
      exact h
    · let y : (mOpen).toScheme := ⟨x,hx⟩
      have h := Order.coheight_le_krullDim y
      rw [←sober_dimension,mOpen_topologicalKrullDim] at h
      change (Order.coheight ((mOpen).ι y):WithBot ℕ∞)≤1
      rw [coheight_eq_of_isOpenImmersion (mOpen).ι]
      exact h
  · rw [←zOpen_topologicalKrullDim]
    exact (zOpen).ι.isOpenEmbedding.isInducing.topologicalKrullDim_le

end
end Z2Z4Rank6.ThirdTwistCoverDimension
