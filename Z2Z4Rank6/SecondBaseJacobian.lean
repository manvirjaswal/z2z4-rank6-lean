module

public import Z2Z4Rank6.SecondBaseGeometry
public import Common.Elliptic.WeierstrassSchemeVariableChange

@[expose] public section

/-!
# The second base and its printed Jacobian

Jaswal, Theorem 8.1(a), DOI 10.5281/zenodo.23437117. Cremona–Fisher–Stoll Theorem 2.8(iii),
arXiv:0908.1741v1 p. 6, identifies
the two-quadric Proj's Jacobian with its invariant cubic. The proved
admissible rational change induces an over-Q scheme isomorphism
to the printed J2 cubic. The conclusion uses the Jacobian
universal property among abelian group schemes.
-/

namespace Z2Z4Rank6.SecondBaseJacobian
noncomputable section
open AlgebraicGeometry CategoryTheory
open SecondBaseProjectiveScheme SecondBaseJacobianInvariants
set_option maxHeartbeats 1200000

def invariantCurveOverIso : Over.mk (WeierstrassScheme.structureMap J2) ≅
    Over.mk (WeierstrassScheme.structureMap (QuadricIntersectionModel.invariantCurve model)) := by
  have he : Over.mk (WeierstrassScheme.structureMap
      (toPrintedChange • QuadricIntersectionModel.invariantCurve model)) ≅
      Over.mk (WeierstrassScheme.structureMap (QuadricIntersectionModel.invariantCurve model)) :=
    Over.isoMk
      (WeierstrassScheme.VariableChange.schemeIso
        (QuadricIntersectionModel.invariantCurve model) toPrintedChange)
      (WeierstrassScheme.VariableChange.schemeIso_over_rat
        (QuadricIntersectionModel.invariantCurve model) toPrintedChange)
  exact eqToIso (congrArg
    (fun W : WeierstrassCurve ℚ => Over.mk (WeierstrassScheme.structureMap W))
    variableChange_eq.symm) ≪≫ he

def invariantCurveIso : WeierstrassScheme.scheme J2 ≅
    WeierstrassScheme.scheme (QuadricIntersectionModel.invariantCurve model) :=
  (Over.forget _).mapIso invariantCurveOverIso

theorem invariantCurveIso_over : invariantCurveIso.hom ≫
      WeierstrassScheme.structureMap (QuadricIntersectionModel.invariantCurve model)=
    WeierstrassScheme.structureMap J2 := by
  exact invariantCurveOverIso.hom.w

/-
  simpa only [variableChange_eq] using
    WeierstrassScheme.VariableChange.schemeIso
      (QuadricIntersectionModel.invariantCurve model) toPrintedChange

theorem invariantCurveIso_over : invariantCurveIso.hom ≫
      WeierstrassScheme.structureMap (QuadricIntersectionModel.invariantCurve model)=
    WeierstrassScheme.structureMap J2 := by
  simpa only [invariantCurveIso,variableChange_eq] using
    WeierstrassScheme.VariableChange.schemeIso_over_rat
      (QuadricIntersectionModel.invariantCurve model) toPrintedChange

def invariantCurveOverIso : Over.mk (WeierstrassScheme.structureMap J2) ≅
    Over.mk (WeierstrassScheme.structureMap (QuadricIntersectionModel.invariantCurve model)) :=
  Over.isoMk invariantCurveIso invariantCurveIso_over
-/

/-- The printed rational cubic J2 is the Jacobian variety of the
printed G2 base. The hypothesis is CFS Theorem 2.8(iii). -/
theorem J2_isJacobian (h : QuadricIntersectionModel.CFSTheorem28iii) :
    Jacobian.IsJacobian (Over.mk structureMap) (Over.mk (WeierstrassScheme.structureMap J2)) :=
  Jacobian.isJacobian_targetIso invariantCurveOverIso
    (QuadricIntersectionModel.invariantCurve_isJacobian h model discriminant_ne_zero)

end
end Z2Z4Rank6.SecondBaseJacobian
