import Common.Elliptic.SurfaceVerticalCurveDescent
import Common.AlgebraicGeometry.ExceptionalCurveDataDescent

/-!
# Relative minimality after an algebraically closed constant extension

Negative-curve descent, constant-map descent, conormal/H1
reflection and Castelnuovo's criterion supply the proof.
-/
namespace Common.Elliptic.SurfaceBaseChange
noncomputable section
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits SurfaceModel
open SurfaceWeierstrassData
open Common.AlgebraicGeometry Common.AlgebraicGeometry.ClosedSubschemeDescent
open Common.AlgebraicGeometry.K3BaseChange Common.AlgebraicGeometry.CurveLineBundle
set_option backward.isDefEq.respectTransparency false
variable (k K : Type) [Field k] [Field K] [Algebra k K] [IsAlgClosed k] [IsAlgClosed K]

theorem minimality_algebraically_closed
    (H : NegativeCurveDescent.PublishedInputs) (hInv : EGAIV2Proposition252iv)
    (hP1 : Stacks0C6U k) (hH1 : Stacks3081 K)
    (hCast : LiedtkeTheorem6Vertical k) (hCastK : LiedtkeTheorem6Vertical K)
    (hProp5 : LiedtkeProposition5Vertical K) (hMinK : LiedtkeCorollary15Vertical K)
    (W : WeierstrassCurve (RatFunc k)) [W.IsElliptic] (M : RegularModel k W)
    (hM : M.IsRelativelyMinimal) (hProj : ProjectiveScheme.IsProjective k M.scheme M.structureMap)
    (hr : IsRegularScheme (scheme k K M)) (hd : topologicalKrullDim (scheme k K M)=2)
    (hProjK : ProjectiveScheme.IsProjective K (scheme k K M) (structureMap k K M)) :
    (model k K M hr hd).IsRelativelyMinimal := by
  let MK := model k K M hr hd
  apply hMinK (W.map (constantExtension k K)) MK hProjK
  intro E hE
  obtain ⟨hELine,hEDegree⟩ := (hCastK _ MK E hProjK).mp hE
  have hENeg : E.toClosedCurve.HasNegativeSelfIntersection K MK.structureMap := by
    refine ⟨hEDegree.1,?_⟩
    change 0<ConormalDegree.degree E.immersion K E.structureMap
    rw [hEDegree.2]
    norm_num
  have hp := structure_isPullback k K M
  have hProper : IsProper M.structureMap := by dsimp [RegularModel.structureMap]; infer_instance
  let : GeometricallyIntegral M.structureMap := M.geometricallyIntegral
  let : IsIntegral M.scheme := GeometricallyIntegral.isIntegral_of_subsingleton M.structureMap
  obtain ⟨C,hC⟩ := NegativeCurveDescent.descends H k K M.scheme MK.scheme
    M.structureMap MK.structureMap (coefficientMap k K M) hp hProper hProj M.smooth
    inferInstance E.toClosedCurve hENeg
  obtain ⟨E0,hE0⟩ := verticalCurve_descends k K M hr hd E C hC
  subst C
  obtain ⟨hLine,hDegree⟩ := ExceptionalCurveDataDescent.projective_line_and_degree_one_reflects
    k K H hInv hP1 hH1 M.scheme MK.scheme M.structureMap MK.structureMap
    (coefficientMap k K M) hp hProper E0.toClosedCurve E.toClosedCurve hC
    hELine hEDegree (hProp5 _ MK E hProjK hE)
  exact E0.not_exceptional_of_minimal hM ((hCast _ M E0 hProj).mpr ⟨hLine,hDegree⟩)

end
end Common.Elliptic.SurfaceBaseChange
