module

public import Z2Z4Rank6.ThirdTwistCoverProjectiveCharts
public import Z2Z4Rank6.ThirdTwistCoverSmooth

@[expose] public section

/-!
# Smoothness of the third-twist projective base

Jaswal, DOI 10.5281/zenodo.23437117, third-twist paragraph.
The weighted Proj schemes have a proved two-chart cover. Their
chart isomorphisms respect the rational structure maps, and the affine
and infinity quotients are smooth of relative dimension 1 by the checked
maximal-minor calculation. Zariski-local gluing proves the global
Mathlib smoothness predicate for both signs.
-/
namespace Z2Z4Rank6.ThirdTwistCoverProjective
noncomputable section
open AlgebraicGeometry CategoryTheory
open ThirdTwistCoverProjectiveCharts
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

theorem zOpen_structureMap_smooth  :
    SmoothOfRelativeDimension 1 ((zOpen).ι≫structureMap) := by
  rw [←zChartSchemeIso_structureMap,
    MorphismProperty.cancel_left_of_respectsIso (P:=@SmoothOfRelativeDimension.{0} 1)]
  exact ThirdTwistCoverSmooth.affine_structureMap_smooth

theorem mOpen_structureMap_smooth  :
    SmoothOfRelativeDimension 1 ((mOpen).ι≫structureMap) := by
  rw [←mChartSchemeIso_structureMap,
    MorphismProperty.cancel_left_of_respectsIso (P:=@SmoothOfRelativeDimension.{0} 1)]
  exact ThirdTwistCoverSmooth.infinity_structureMap_smooth

/-- Relative-dimension-one smoothness of the weighted Proj. -/
instance structureMap_smooth  : SmoothOfRelativeDimension 1 (structureMap) := by
  let U : Bool→(scheme).Opens := fun b=>if b then zOpen else mOpen
  have hU : iSup U=⊤ := by simpa [U,iSup_bool_eq] using two_chart_cover
  apply IsZariskiLocalAtSource.of_iSup_eq_top (P:=@SmoothOfRelativeDimension.{0} 1) U hU
  intro b
  cases b
  · exact mOpen_structureMap_smooth
  · exact zOpen_structureMap_smooth

theorem structureMap_smooth_morphism  : Smooth (structureMap) :=
  SmoothOfRelativeDimension.smooth 1 (structureMap)

/-- Properness and smoothness concern the same rational structural map. -/
theorem proper_and_smooth  :
    IsProper (structureMap) ∧ SmoothOfRelativeDimension 1 (structureMap) :=
  ⟨inferInstance,inferInstance⟩

end
end Z2Z4Rank6.ThirdTwistCoverProjective
