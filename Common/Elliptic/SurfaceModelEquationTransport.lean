import Common.Elliptic.SurfaceModel

/-! Reidentify a regular surface model by an equation equality. -/
namespace Common.Elliptic.SurfaceModel.RegularModel
noncomputable section
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false
variable {k : Type} [Field k] {W V : WeierstrassCurve (RatFunc k)}

def changeEquation (M : RegularModel k W) (h : W=V) : RegularModel k V where
  scheme := M.scheme
  projection := M.projection
  proper := M.proper
  flat := M.flat
  regular := M.regular
  smooth := M.smooth
  geometricallyIntegral := M.geometricallyIntegral
  dimension := M.dimension
  genericIso := M.genericIso≪≫eqToIso (congrArg WeierstrassScheme.scheme h)
  genericIso_over := by
    subst V
    simpa using M.genericIso_over

@[simp] theorem changeEquation_rfl (M : RegularModel k W) : M.changeEquation rfl=M := by
  cases M
  simp [changeEquation]

theorem changeEquation_isRelativelyMinimal (M : RegularModel k W) (h : W=V)
    (hmin : M.IsRelativelyMinimal) : (M.changeEquation h).IsRelativelyMinimal := by
  subst V
  simpa using hmin

theorem changeEquation_hasSection (M : RegularModel k W) (h : W=V)
    (hs : M.HasSection) : (M.changeEquation h).HasSection := hs

@[simp] theorem changeEquation_scheme (M : RegularModel k W) (h : W=V) :
    (M.changeEquation h).scheme=M.scheme := rfl

@[simp] theorem changeEquation_projection (M : RegularModel k W) (h : W=V) :
    (M.changeEquation h).projection=M.projection := rfl

@[simp] theorem changeEquation_structureMap (M : RegularModel k W) (h : W=V) :
    (M.changeEquation h).structureMap=M.structureMap := rfl

end
end Common.Elliptic.SurfaceModel.RegularModel
