module

public import Z2Z4Rank6.SecondTorsionCoverProjectiveCharts
public import Z2Z4Rank6.SecondTorsionCoverSmooth

@[expose] public section

/-!
# Smoothness of the signed weighted projective torsion covers

Jaswal, DOI 10.5281/zenodo.23437117, Theorem 8.1(c).
The weighted Proj schemes have a proved two-chart cover. Their
chart isomorphisms respect the rational structure maps, and the affine
and infinity quotients are smooth of relative dimension 1 by the checked
maximal-minor calculation. Zariski-local gluing proves the global
Mathlib smoothness predicate for both signs.
-/
namespace Z2Z4Rank6.SecondTorsionCoverProjective
noncomputable section
open AlgebraicGeometry CategoryTheory
open SecondTorsionCoverProjectiveCharts
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

theorem zOpen_structureMap_smooth (ε:Bool) :
    SmoothOfRelativeDimension 1 ((zOpen ε).ι≫structureMap ε) := by
  rw [←zChartSchemeIso_structureMap,
    MorphismProperty.cancel_left_of_respectsIso (P:=@SmoothOfRelativeDimension.{0} 1)]
  exact SecondTorsionCoverSmooth.affine_structureMap_smooth ε

theorem mOpen_structureMap_smooth (ε:Bool) :
    SmoothOfRelativeDimension 1 ((mOpen ε).ι≫structureMap ε) := by
  rw [←mChartSchemeIso_structureMap,
    MorphismProperty.cancel_left_of_respectsIso (P:=@SmoothOfRelativeDimension.{0} 1)]
  exact SecondTorsionCoverSmooth.infinity_structureMap_smooth ε

/-- Relative-dimension-one smoothness of the weighted Proj. -/
instance structureMap_smooth (ε:Bool) : SmoothOfRelativeDimension 1 (structureMap ε) := by
  let U : Bool→(scheme ε).Opens := fun b=>if b then zOpen ε else mOpen ε
  have hU : iSup U=⊤ := by simpa [U,iSup_bool_eq] using two_chart_cover ε
  apply IsZariskiLocalAtSource.of_iSup_eq_top (P:=@SmoothOfRelativeDimension.{0} 1) U hU
  intro b
  cases b
  · exact mOpen_structureMap_smooth ε
  · exact zOpen_structureMap_smooth ε

theorem structureMap_smooth_morphism (ε:Bool) : Smooth (structureMap ε) :=
  SmoothOfRelativeDimension.smooth 1 (structureMap ε)

/-- Properness and smoothness concern the same rational structural map. -/
theorem proper_and_smooth (ε:Bool) :
    IsProper (structureMap ε) ∧ SmoothOfRelativeDimension 1 (structureMap ε) :=
  ⟨inferInstance,inferInstance⟩

end
end Z2Z4Rank6.SecondTorsionCoverProjective
