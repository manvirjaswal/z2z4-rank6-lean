module

public import Common.AlgebraicGeometry.ProjectiveLine
public import Common.Elliptic.RegularProperModel
public import Common.Elliptic.WeierstrassScheme
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.Topology.KrullDimension

@[expose] public section

/-!
# Regular proper models over the projective line

The total space, projection, generic-fiber isomorphism and regular
local rings are retained. Relative minimality means absence of any
nontrivial contraction to another regular model of the same generic
curve. This is the model-theoretic version of the usual absence of
vertical (-1)-curves.

References: C. Liedtke, Semi-stable reduction for curves, Mordell seminar
notes, Definitions 2,4,8,10 and Theorems 3,6,14, pp. 1–4;
https://math.stanford.edu/~conrad/mordellsem/Notes/L12.pdf.
Also Q. Liu, Algebraic Geometry and Arithmetic Curves, Theorem 9.3.21.
-/
namespace Common.Elliptic.SurfaceModel
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false
variable (k : Type) [Field k]

abbrev Base := ProjectiveLine.scheme k
abbrev FunctionField := RatFunc k
abbrev FieldBase := Spec (CommRingCat.of (FunctionField k))

def genericBaseMap : FieldBase k ⟶ Base k := ProjectiveLine.genericPoint k

structure RegularModel (W : WeierstrassCurve (FunctionField k)) where
  scheme : Scheme.{0}
  projection : scheme ⟶ Base k
  proper : IsProper projection
  flat : Flat projection
  regular : IsRegularScheme scheme
  smooth : SmoothOfRelativeDimension 2 (projection≫ProjectiveLine.structureMap k)
  geometricallyIntegral : GeometricallyIntegral (projection≫ProjectiveLine.structureMap k)
  dimension : topologicalKrullDim scheme=2
  genericIso : pullback projection (genericBaseMap k) ≅ WeierstrassScheme.scheme W
  genericIso_over : genericIso.hom≫WeierstrassScheme.structureMap W=
    pullback.snd projection (genericBaseMap k)

namespace RegularModel
variable {k}
attribute [instance] proper flat

def structureMap {W : WeierstrassCurve (FunctionField k)} (M : RegularModel k W) :=
  M.projection≫ProjectiveLine.structureMap k

def genericInclusion {W : WeierstrassCurve (FunctionField k)} (M : RegularModel k W) :
    WeierstrassScheme.scheme W ⟶ M.scheme :=
  M.genericIso.inv≫pullback.fst M.projection (genericBaseMap k)

structure Hom {W : WeierstrassCurve (FunctionField k)} (M N : RegularModel k W) where
  hom : M.scheme ⟶ N.scheme
  over_base : hom ≫ N.projection = M.projection
  generic : M.genericInclusion ≫ hom = N.genericInclusion

/-- Relative minimality among regular models of the same generic curve. -/
def IsRelativelyMinimal {W : WeierstrassCurve (FunctionField k)} (M : RegularModel k W) : Prop :=
  ∀ (N : RegularModel k W) (f : Hom M N),IsIso f.hom

/-- A section of the surface projection. -/
def HasSection {W : WeierstrassCurve (FunctionField k)} (M : RegularModel k W) : Prop :=
  Nonempty {s : Base k ⟶ M.scheme // s≫M.projection=𝟙 (Base k)}

/-- The geometric fiber over a field-valued point of the base. -/
def fiber {W : WeierstrassCurve (FunctionField k)} (M : RegularModel k W)
    {K : Type} [Field K] (p : Spec (CommRingCat.of K) ⟶ Base k) : Scheme :=
  pullback M.projection p

def fiberStructureMap {W : WeierstrassCurve (FunctionField k)} (M : RegularModel k W)
    {K : Type} [Field K] (p : Spec (CommRingCat.of K) ⟶ Base k) :
    M.fiber p ⟶ Spec (CommRingCat.of K) := pullback.snd M.projection p

end RegularModel

end
end Common.Elliptic.SurfaceModel
