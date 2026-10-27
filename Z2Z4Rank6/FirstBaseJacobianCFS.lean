module

public import Z2Z4Rank6.FirstBaseJacobianCFSInvariants
public import Common.Elliptic.WeierstrassSchemeVariableChange

@[expose] public section

/-!
# The first base has the printed EC as its Jacobian

Cremona–Fisher–Stoll Theorem 2.8(iii), arXiv:0908.1741v1 p. 6,
applied to the two first-base quadrics.
The conclusion is the full basepoint-free Albanese universal property
among abelian group schemes, with an over-Q scheme
identification to the full printed EC cubic.
-/
namespace Z2Z4Rank6.FirstBaseJacobianCFS
noncomputable section
open AlgebraicGeometry CategoryTheory

def invariantCurveOverIso : Over.mk (WeierstrassScheme.structureMap EC) ≅
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

/-- The EC cubic realizes the Jacobian of the
first-base Proj. The hypothesis is Cremona–Fisher–Stoll Theorem 2.8(iii). -/
theorem ec_isJacobian (hJac : QuadricIntersectionModel.CFSTheorem28iii) :
    Jacobian.IsJacobian (Over.mk ProjectiveBaseScheme.structureMap)
      (Over.mk (WeierstrassScheme.structureMap EC)) := by
  have h := QuadricIntersectionModel.invariantCurve_isJacobian hJac model discriminant_ne_zero
  change Jacobian.IsJacobian (Over.mk ProjectiveBaseScheme.structureMap)
    (Over.mk (WeierstrassScheme.structureMap (QuadricIntersectionModel.invariantCurve model))) at h
  exact Jacobian.isJacobian_targetIso invariantCurveOverIso h

end
end Z2Z4Rank6.FirstBaseJacobianCFS
