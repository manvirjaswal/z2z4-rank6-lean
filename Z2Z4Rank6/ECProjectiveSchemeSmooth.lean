import Z2Z4Rank6.ECProjectiveSchemeAffineSmooth
import Z2Z4Rank6.ECProjectiveSchemeInfinitySmooth

/-!
# Smoothness of the projective Weierstrass cubic

Jaswal, DOI 10.5281/zenodo.23437117, Lemma 4.1(a) and
Theorem 1.2(a), smoothness portion. The Proj of the full printed homogeneous
cubic has a proved two-chart cover and Q-scheme chart isomorphisms.
Both affine structural morphisms are proved smooth of relative dimension 1.
Zariski-local gluing therefore proves the Mathlib scheme predicate.
-/
namespace Z2Z4Rank6.ECProjectiveScheme
noncomputable section
open AlgebraicGeometry CategoryTheory
open ECProjectiveSchemeCharts ECProjectiveSchemeInfinity
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- The z-chart restriction of the rational structural map is smooth. -/
theorem zOpen_structureMap_smooth : SmoothOfRelativeDimension 1 (zOpen.ι ≫ structureMap) := by
  rw [←zChartSchemeIso_structureMap,
    MorphismProperty.cancel_left_of_respectsIso (P:=@SmoothOfRelativeDimension.{0} 1)]
  exact ECProjectiveSchemeAffine.structureMap_smooth

/-- The Y-chart restriction, including infinity, is smooth of the same dimension. -/
theorem yOpen_structureMap_smooth : SmoothOfRelativeDimension 1 (yOpen.ι ≫ structureMap) := by
  rw [←yChartSchemeIso_structureMap,
    MorphismProperty.cancel_left_of_respectsIso (P:=@SmoothOfRelativeDimension.{0} 1)]
  exact ECProjectiveSchemeInfinity.structureMap_smooth

/-- The projective intersection is smooth over Q of relative dimension 1. -/
instance structureMap_smooth : SmoothOfRelativeDimension 1 structureMap := by
  let U : Bool→scheme.Opens := fun b => if b then zOpen else yOpen
  have hU : iSup U=⊤ := by
    simpa [U,iSup_bool_eq] using two_chart_cover
  apply IsZariskiLocalAtSource.of_iSup_eq_top (P:=@SmoothOfRelativeDimension.{0} 1) U hU
  intro b
  cases b
  · exact yOpen_structureMap_smooth
  · exact zOpen_structureMap_smooth

/-- Smoothness in the ordinary Mathlib scheme-morphism sense. -/
theorem structureMap_smooth_morphism : Smooth structureMap :=
  SmoothOfRelativeDimension.smooth 1 structureMap

/-- Properness and one-dimensional smoothness concern the same
projective Q-scheme morphism. -/
theorem proper_and_smooth : IsProper structureMap ∧ SmoothOfRelativeDimension 1 structureMap :=
  ⟨inferInstance,inferInstance⟩

end
end Z2Z4Rank6.ECProjectiveScheme
