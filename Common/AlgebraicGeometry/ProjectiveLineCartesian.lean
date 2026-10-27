import Common.AlgebraicGeometry.ProjectiveLineCartesianCharts
import Common.AlgebraicGeometry.ProjectiveLineCoordinateCover

/-!
# The projective line commutes with coefficient extension

The cartesian square is proved from the two polynomial charts.
-/
namespace AlgebraicGeometry.ProjectiveLine
noncomputable section
open CategoryTheory CategoryTheory.Limits Charts
set_option backward.isDefEq.respectTransparency false
variable (k K : Type) [Field k] [Field K] [Algebra k K]

theorem coefficient_isPullback :
    IsPullback (coefficientMap k K) (structureMap K) (structureMap k)
      (Spec.map (CommRingCat.ofHom (algebraMap k K))) := by
  apply Scheme.isPullback_of_openCover _ _ _ _ (coordinateCover k).openCover
  intro i
  change IsPullback (pullback.snd (coefficientMap k K) (chartInclusion k i))
    (pullback.fst (coefficientMap k K) (chartInclusion k i)≫structureMap K)
    (chartInclusion k i≫structureMap k)
    (Spec.map (CommRingCat.ofHom (algebraMap k K)))
  have h : IsPullback (Spec.map (CommRingCat.ofHom (chartCoefficientHom k K i)))
      (chartInclusion K i≫structureMap K) (chartInclusion k i≫structureMap k)
      (Spec.map (CommRingCat.ofHom (algebraMap k K))) := by
    rw [chartInclusion_structureMap,chartInclusion_structureMap]
    exact chart_field_isPullback k K i
  apply h.of_iso (chart_isPullback k K i).flip.isoPullback
    (Iso.refl _) (Iso.refl _) (Iso.refl _) <;> simp

def baseChangeIso : scheme K ≅
    pullback (structureMap k) (Spec.map (CommRingCat.ofHom (algebraMap k K))) :=
  (coefficient_isPullback k K).isoPullback

@[reassoc (attr:=simp)] theorem baseChangeIso_hom_fst :
    (baseChangeIso k K).hom≫pullback.fst _ _=coefficientMap k K :=
  (coefficient_isPullback k K).isoPullback_hom_fst

@[reassoc (attr:=simp)] theorem baseChangeIso_hom_snd :
    (baseChangeIso k K).hom≫pullback.snd _ _=structureMap K :=
  (coefficient_isPullback k K).isoPullback_hom_snd

end
end AlgebraicGeometry.ProjectiveLine
