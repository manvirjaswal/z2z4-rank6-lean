import Common.Elliptic.SurfaceBaseChange
import Common.Elliptic.SurfaceGenericPoint
import Common.Elliptic.WeierstrassSchemeCartesian

/-!
# The generic fiber of a constant-field surface pullback

Passing to K(n) is treated separately from the total-space field
extension. The commuting generic-point square and pullback
pasting give the isomorphism to the coefficient-extended cubic.
-/
namespace Common.Elliptic.SurfaceBaseChange
noncomputable section
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits SurfaceModel
open SurfaceWeierstrassData
set_option backward.isDefEq.respectTransparency false
variable (k K : Type) [Field k] [Field K] [Algebra k K]
variable {W : WeierstrassCurve (RatFunc k)} (M : RegularModel k W)

theorem genericIso_exists :
    Nonempty {e : pullback (projection k K M) (SurfaceModel.genericBaseMap K) ≅
      WeierstrassScheme.scheme (W.map (constantExtension k K)) //
      e.hom≫WeierstrassScheme.structureMap (W.map (constantExtension k K))=
        pullback.snd (projection k K M) (SurfaceModel.genericBaseMap K)} := by
  have hwhole := (IsPullback.of_hasPullback (projection k K M) (SurfaceModel.genericBaseMap K)).paste_horiz
    (projection_isPullback k K M)
  have he : SurfaceModel.genericBaseMap K≫ProjectiveLine.coefficientMap k K=
      Spec.map (CommRingCat.ofHom (constantExtension k K))≫SurfaceModel.genericBaseMap k :=
    genericPoint_commutes k K
  rw [he] at hwhole
  have hgeneric := hwhole.of_right' (IsPullback.of_hasPullback M.projection (SurfaceModel.genericBaseMap k))
  have hcurve : IsPullback (hgeneric.cone.fst≫M.genericIso.hom)
      (pullback.snd (projection k K M) (SurfaceModel.genericBaseMap K))
      (WeierstrassScheme.structureMap W)
      (Spec.map (CommRingCat.ofHom (constantExtension k K))) := by
    apply hgeneric.of_iso (Iso.refl _) M.genericIso (Iso.refl _) (Iso.refl _)
    · simp
    · simp
    · simpa using M.genericIso_over.symm
    · simp
  let e := hcurve.isoIsPullback _ _
    (WeierstrassScheme.CoefficientMap.scheme_isPullback (constantExtension k K) W)
  exact ⟨e,hcurve.isoIsPullback_hom_snd _ _ _⟩

def genericIso : pullback (projection k K M) (SurfaceModel.genericBaseMap K) ≅
    WeierstrassScheme.scheme (W.map (constantExtension k K)) :=
  (genericIso_exists k K M).some.val

theorem genericIso_over : (genericIso k K M).hom≫
    WeierstrassScheme.structureMap (W.map (constantExtension k K))=
      pullback.snd (projection k K M) (SurfaceModel.genericBaseMap K) :=
  (genericIso_exists k K M).some.property

/-- The field pullback is a regular model once regularity and
dimension are supplied; all other fields have been proved above. -/
def model (hr : IsRegularScheme (scheme k K M))
    (hd : topologicalKrullDim (scheme k K M)=2) :
    RegularModel K (W.map (constantExtension k K)) where
  scheme := scheme k K M
  projection := projection k K M
  proper := inferInstance
  flat := inferInstance
  regular := hr
  smooth := smooth k K M
  geometricallyIntegral := geometricallyIntegral k K M
  dimension := hd
  genericIso := genericIso k K M
  genericIso_over := genericIso_over k K M

theorem model_hasSection (hr : IsRegularScheme (scheme k K M))
    (hd : topologicalKrullDim (scheme k K M)=2) (hs : M.HasSection) :
    (model k K M hr hd).HasSection := hasSection k K M hs

end
end Common.Elliptic.SurfaceBaseChange
