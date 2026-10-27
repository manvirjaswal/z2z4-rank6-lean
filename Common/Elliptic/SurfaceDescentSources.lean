import Common.Elliptic.SurfaceAlgebraicallyClosedMinimality
import Common.Elliptic.SurfaceBaseChangeRegularModel
import Common.Elliptic.SurfaceConstantTower
import Mathlib.FieldTheory.AlgebraicClosure

/-!
# Published inputs for rational elliptic-surface descent

The algebraic-closure step is Overkamp–Smeets, On logarithmic reduction
of cohomologically tame elliptic surfaces, arXiv:2212.01070v1,
Proposition 2.6 p. 6. It is stated only for an algebraic closure.
Projectivity base change is EGA II Proposition 5.5.5(iii).

-/
namespace Common.Elliptic.SurfaceDescentSources
noncomputable section
open _root_.AlgebraicGeometry CategoryTheory
open SurfaceModel SurfaceBaseChange SurfaceWeierstrassData
open Common.AlgebraicGeometry Common.AlgebraicGeometry.K3BaseChange
open Common.AlgebraicGeometry.CurveLineBundle
set_option backward.isDefEq.respectTransparency false

/-- EGA II Proposition 5.5.5(iii), specialized to base fields. -/
def EGAIIProposition555iii (k K : Type) [Field k] [Field K] [Algebra k K] : Prop :=
  ∀ (X Y : Scheme.{0}) (s : X ⟶ Spec (CommRingCat.of k))
    (t : Y ⟶ Spec (CommRingCat.of K)) (p : Y ⟶ X),
    IsPullback p t s (extensionMap k K) → ProjectiveScheme.IsProjective k X s →
      ProjectiveScheme.IsProjective K Y t

/-- Overkamp–Smeets Proposition 2.6 p. 6: an elliptic surface remains
minimal after passage to an algebraic closure of its constant field. -/
def OverkampSmeetsProposition26 (k K : Type) [Field k] [Field K] [Algebra k K]
    [CharZero k] [IsAlgClosure k K] : Prop :=
  ∀ (W : WeierstrassCurve (RatFunc k)) [W.IsElliptic] (M : RegularModel k W),
    ProjectiveScheme.IsProjective k M.scheme M.structureMap → M.HasSection →
    M.IsRelativelyMinimal → ∀ (hr : IsRegularScheme (SurfaceBaseChange.scheme k K M))
      (hd : topologicalKrullDim (SurfaceBaseChange.scheme k K M)=2),
        (model k K M hr hd).IsRelativelyMinimal

/-- All fields are arbitrary. -/
structure PublishedInputs : Prop where
  negative_curve : NegativeCurveDescent.PublishedInputs
  regular : ∀ (k : Type) [Field k],Stacks056SSmoothRegular k
  projective_baseChange : ∀ (k K : Type) [Field k] [Field K] [Algebra k K],
    EGAIIProposition555iii k K
  algebraic_minimality : ∀ (k K : Type) [Field k] [Field K] [Algebra k K]
    [CharZero k] [IsAlgClosure k K],OverkampSmeetsProposition26 k K
  line_bundle_descent : EGAIV2Proposition252iv
  projective_line : ∀ (k : Type) [Field k],Stacks0C6U k
  projective_line_h1 : ∀ (k : Type) [Field k],Stacks3081 k
  castelnuovo : ∀ (k : Type) [Field k] [IsAlgClosed k],LiedtkeTheorem6Vertical k
  exceptional_conormal : ∀ (k : Type) [Field k] [IsAlgClosed k],LiedtkeProposition5Vertical k
  minimality : ∀ (k : Type) [Field k] [IsAlgClosed k],LiedtkeCorollary15Vertical k

end
end Common.Elliptic.SurfaceDescentSources
