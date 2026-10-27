import Common.Elliptic.SurfaceModel
import Common.AlgebraicGeometry.ClosedSubschemeDescent
import Common.AlgebraicGeometry.CurveLineBundle

/-!
# Vertical prime curves and Castelnuovo's criterion

A vertical curve is an integral closed curve whose projection
factors through a rational base point. Over an algebraically
closed coefficient field these are precisely the vertical prime
divisors. Exceptionality retains a contraction isomorphic on
complements.

References: Liedtke, Semi-stable reduction for curves, Definition 4 and
Proposition 5/Theorem 6 p. 2, Definition 8 p. 3 and Corollary 15 p. 4.
-/
namespace Common.Elliptic.SurfaceModel
noncomputable section
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Common.AlgebraicGeometry Common.AlgebraicGeometry.ClosedSubschemeDescent
set_option backward.isDefEq.respectTransparency false
variable (k : Type) [Field k]

structure VerticalCurve {W : WeierstrassCurve (RatFunc k)} (M : RegularModel k W)
    extends ClosedCurve M.scheme where
  point : Spec (CommRingCat.of k) ⟶ Base k
  point_over : point≫ProjectiveLine.structureMap k=𝟙 _
  vertical : immersion≫M.projection=(immersion≫M.structureMap)≫point

namespace VerticalCurve
variable {k} {W : WeierstrassCurve (RatFunc k)} {M : RegularModel k W}

def structureMap (E : VerticalCurve k M) : E.scheme ⟶ Spec (CommRingCat.of k) :=
  E.immersion≫M.structureMap

def IsProjectiveLine (E : VerticalCurve k M) : Prop :=
  CurveLineBundle.IsProjectiveLine k E.scheme E.structureMap

def HasDegreeOne (E : VerticalCurve k M) : Prop :=
  ConormalDegree.HasDegreeOne E.immersion k E.structureMap

def IsExceptional (E : VerticalCurve k M) : Prop :=
  ∃ (N : RegularModel k W) (f : RegularModel.Hom M N),¬IsIso f.hom ∧
    ∃ y : N.scheme,(∀ x : E.scheme,f.hom (E.immersion x)=y) ∧
      ∃ (U : M.scheme.Opens) (V : N.scheme.Opens),
        (U : Set M.scheme)=(Set.range E.immersion)ᶜ ∧
        (V : Set N.scheme)=({y} : Set N.scheme)ᶜ ∧
        ∃ h : U≤f.hom ⁻¹ᵁ V,IsIso (f.hom.resLE V U h)

theorem not_exceptional_of_minimal (E : VerticalCurve k M)
    (hmin : M.IsRelativelyMinimal) : ¬E.IsExceptional := by
  rintro ⟨N,f,hnot,_⟩
  exact hnot (hmin N f)

end VerticalCurve

/-- Liedtke Theorem 6 p. 2, over an algebraically closed coefficient field. -/
def LiedtkeTheorem6Vertical [IsAlgClosed k] : Prop :=
  ∀ (W : WeierstrassCurve (RatFunc k)) [W.IsElliptic] (M : RegularModel k W)
    (E : VerticalCurve k M),
    ProjectiveScheme.IsProjective k M.scheme M.structureMap →
      (E.IsExceptional ↔ E.IsProjectiveLine ∧ E.HasDegreeOne)

/-- The invertibility consequence of the explicit O(-1) formula in
Liedtke Proposition 5 p. 2. -/
def LiedtkeProposition5Vertical [IsAlgClosed k] : Prop :=
  ∀ (W : WeierstrassCurve (RatFunc k)) [W.IsElliptic] (M : RegularModel k W)
    (E : VerticalCurve k M),
    ProjectiveScheme.IsProjective k M.scheme M.structureMap → E.IsExceptional →
      CurveLineBundle.IsInvertible (ConormalDegree.conormal E.immersion)

/-- Liedtke Definition 8 p. 3 and Corollary 15 p. 4. Algebraic closedness
ensures that every closed base point is represented by a k-point. -/
def LiedtkeCorollary15Vertical [IsAlgClosed k] : Prop :=
  ∀ (W : WeierstrassCurve (RatFunc k)) [W.IsElliptic] (M : RegularModel k W),
    ProjectiveScheme.IsProjective k M.scheme M.structureMap →
      (∀ E : VerticalCurve k M,¬E.IsExceptional) → M.IsRelativelyMinimal

end
end Common.Elliptic.SurfaceModel
