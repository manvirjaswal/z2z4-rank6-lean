module

public import Z2Z4Rank6.GTorsionCoverRingDimension
public import Z2Z4Rank6.GTorsionCoverProjectiveCharts

@[expose] public section

/-!
# Dimension of the weighted projective signed torsion covers

The two-chart cover and chart isomorphisms transfer the
proved exact ring dimensions to topological Krull dimension 1 of both Proj
schemes.
Source: Jaswal, Section 7, DOI 10.5281/zenodo.23437117.
-/
namespace Z2Z4Rank6.GTorsionCoverDimension
noncomputable section
open AlgebraicGeometry CategoryTheory
open GTorsionCoverProjective GTorsionCoverProjectiveCharts
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

theorem zOpen_topologicalKrullDim (ε : Bool) :
    topologicalKrullDim (zOpen ε).toScheme=1 := by
  rw [(zChartSchemeIso ε).hom.homeomorph.isHomeomorph.topologicalKrullDim_eq]
  exact affine_topologicalKrullDim ε

theorem mOpen_topologicalKrullDim (ε : Bool) :
    topologicalKrullDim (mOpen ε).toScheme=1 := by
  rw [(mChartSchemeIso ε).hom.homeomorph.isHomeomorph.topologicalKrullDim_eq]
  exact infinity_topologicalKrullDim ε

attribute [local instance] specializationOrder

private theorem sober_dimension (Y : Scheme) :
    topologicalKrullDim Y=Order.krullDim Y :=
  Order.krullDim_eq_of_orderIso irreducibleSetEquivPoints

/-- The signed weighted projective cover has dimension exactly 1.
The result is unconditional, before any geometric-integrality criterion. -/
theorem scheme_topologicalKrullDim (ε : Bool) : topologicalKrullDim (scheme ε)=1 := by
  apply le_antisymm
  · rw [sober_dimension,Order.krullDim_eq_iSup_coheight]
    apply iSup_le
    intro x
    have hx : x∈zOpen ε ∨ x∈mOpen ε := by
      have h : x∈zOpen ε⊔mOpen ε := (two_chart_cover ε).symm ▸ Set.mem_univ x
      exact h
    rcases hx with hx|hx
    · let y : (zOpen ε).toScheme := ⟨x,hx⟩
      have h := Order.coheight_le_krullDim y
      rw [←sober_dimension,zOpen_topologicalKrullDim] at h
      change (Order.coheight ((zOpen ε).ι y):WithBot ℕ∞)≤1
      rw [coheight_eq_of_isOpenImmersion (zOpen ε).ι]
      exact h
    · let y : (mOpen ε).toScheme := ⟨x,hx⟩
      have h := Order.coheight_le_krullDim y
      rw [←sober_dimension,mOpen_topologicalKrullDim] at h
      change (Order.coheight ((mOpen ε).ι y):WithBot ℕ∞)≤1
      rw [coheight_eq_of_isOpenImmersion (mOpen ε).ι]
      exact h
  · rw [←zOpen_topologicalKrullDim ε]
    exact (zOpen ε).ι.isOpenEmbedding.isInducing.topologicalKrullDim_le

end
end Z2Z4Rank6.GTorsionCoverDimension
