import Common.Elliptic.SurfaceModel
import Common.AlgebraicGeometry.ProjectiveLineCartesian
import Common.AlgebraicGeometry.K3BaseChange

/-!
# Constant-field pullbacks of elliptic surfaces

The surface and all maps are fiber products of the projection.
The total-space square is proved cartesian from the cartesian square for
the projective line. Properness, flatness, smoothness, geometric integrality and the section are
preserved.
Regularity, dimension, generic-fiber identification and minimality are
separate from these elementary pullback facts.
-/
namespace Common.Elliptic.SurfaceBaseChange
noncomputable section
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open SurfaceModel
set_option backward.isDefEq.respectTransparency false
variable (k K : Type) [Field k] [Field K] [Algebra k K]
variable {W : WeierstrassCurve (RatFunc k)} (M : RegularModel k W)

abbrev scheme : Scheme := pullback M.projection (ProjectiveLine.coefficientMap k K)

def projection : scheme k K M ⟶ ProjectiveLine.scheme K :=
  pullback.snd M.projection (ProjectiveLine.coefficientMap k K)

def coefficientMap : scheme k K M ⟶ M.scheme :=
  pullback.fst M.projection (ProjectiveLine.coefficientMap k K)

def structureMap : scheme k K M ⟶ Spec (CommRingCat.of K) :=
  projection k K M ≫ ProjectiveLine.structureMap K

theorem projection_isPullback :
    IsPullback (coefficientMap k K M) (projection k K M)
      M.projection (ProjectiveLine.coefficientMap k K) :=
  .of_hasPullback _ _

theorem structure_isPullback :
    IsPullback (coefficientMap k K M) (structureMap k K M)
      M.structureMap (Common.AlgebraicGeometry.K3BaseChange.extensionMap k K) :=
  (projection_isPullback k K M).paste_vert (ProjectiveLine.coefficient_isPullback k K)

def totalSpaceIso : scheme k K M ≅
    Common.AlgebraicGeometry.K3BaseChange.scheme k K M.scheme M.structureMap :=
  (structure_isPullback k K M).isoPullback

@[reassoc (attr:=simp)] theorem totalSpaceIso_hom_fst :
    (totalSpaceIso k K M).hom ≫ pullback.fst _ _ = coefficientMap k K M :=
  (structure_isPullback k K M).isoPullback_hom_fst

@[reassoc (attr:=simp)] theorem totalSpaceIso_hom_snd :
    (totalSpaceIso k K M).hom ≫ pullback.snd _ _ = structureMap k K M :=
  (structure_isPullback k K M).isoPullback_hom_snd

instance : IsProper (projection k K M) := by
  dsimp [projection]
  infer_instance

instance : Flat (projection k K M) := by
  dsimp [projection]
  infer_instance

theorem smooth : SmoothOfRelativeDimension 2 (structureMap k K M) :=
  MorphismProperty.of_isPullback (structure_isPullback k K M) M.smooth

theorem geometricallyIntegral : GeometricallyIntegral (structureMap k K M) :=
  MorphismProperty.of_isPullback (structure_isPullback k K M) M.geometricallyIntegral

/-- Pull back the section, retaining its right-inverse equation. -/
theorem hasSection (h : M.HasSection) :
    Nonempty {s : ProjectiveLine.scheme K ⟶ scheme k K M //
      s ≫ projection k K M = 𝟙 _} := by
  obtain ⟨s,hs⟩ := h
  refine ⟨pullback.lift (ProjectiveLine.coefficientMap k K ≫ s) (𝟙 _) ?_, ?_⟩
  · simp [Category.assoc,hs]
  · simp [projection]

end
end Common.Elliptic.SurfaceBaseChange
