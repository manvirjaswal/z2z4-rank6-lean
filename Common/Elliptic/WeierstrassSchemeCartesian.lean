import Common.Elliptic.WeierstrassSchemeChartPushout

/-!
# The complete projective Weierstrass cubic commutes with coefficient extension

The cartesian square is proved from chart-ring pushouts and the
open cover of the homogeneous cubic. This works for every field
homomorphism and requires no ellipticity or infinite-field premise.
-/
namespace WeierstrassScheme.CoefficientMap
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits GenericCharts
set_option backward.isDefEq.respectTransparency false
variable {k K : Type} [Field k] [Field K] (f : k →+* K)
variable (W : WeierstrassCurve k)

def coordinateCover : (scheme W).AffineOpenCover where
  I₀ := Fin 3
  X i := CommRingCat.of (ChartRing W i)
  f i := chartInclusion W i
  idx x := (TopologicalSpace.Opens.mem_iSup.mp
    ((coordinate_opens_cover W).ge (show x∈(⊤ : (scheme W).Opens) from trivial))).choose
  covers x := by
    change x∈(chartInclusion W _).opensRange
    rw [chartInclusion_opensRange]
    exact (TopologicalSpace.Opens.mem_iSup.mp
      ((coordinate_opens_cover W).ge (show x∈(⊤ : (scheme W).Opens) from trivial))).choose_spec

theorem scheme_isPullback :
    IsPullback (schemeHom f W) (structureMap (W.map f)) (structureMap W)
      (Spec.map (CommRingCat.ofHom f)) := by
  apply Scheme.isPullback_of_openCover _ _ _ _ (coordinateCover W).openCover
  intro i
  change IsPullback (pullback.snd (schemeHom f W) (chartInclusion W i))
    (pullback.fst (schemeHom f W) (chartInclusion W i)≫structureMap (W.map f))
    (chartInclusion W i≫structureMap W) (Spec.map (CommRingCat.ofHom f))
  have h : IsPullback (Spec.map (CommRingCat.ofHom (chartHom f W i)))
      (chartInclusion (W.map f) i≫structureMap (W.map f))
      (chartInclusion W i≫structureMap W) (Spec.map (CommRingCat.ofHom f)) := by
    rw [chartInclusion_structureMap,chartInclusion_structureMap]
    exact chart_field_isPullback f W i
  apply h.of_iso (chart_isPullback f W i).flip.isoPullback
    (Iso.refl _) (Iso.refl _) (Iso.refl _) <;> simp

def baseChangeIso : scheme (W.map f) ≅
    pullback (structureMap W) (Spec.map (CommRingCat.ofHom f)) :=
  (scheme_isPullback f W).isoPullback

@[reassoc (attr:=simp)] theorem baseChangeIso_hom_fst :
    (baseChangeIso f W).hom≫pullback.fst _ _=schemeHom f W :=
  (scheme_isPullback f W).isoPullback_hom_fst

@[reassoc (attr:=simp)] theorem baseChangeIso_hom_snd :
    (baseChangeIso f W).hom≫pullback.snd _ _=structureMap (W.map f) :=
  (scheme_isPullback f W).isoPullback_hom_snd

end
end WeierstrassScheme.CoefficientMap
