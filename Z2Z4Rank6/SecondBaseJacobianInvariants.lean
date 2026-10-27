import Z2Z4Rank6.SecondBaseProjectiveScheme
import Z2Z4Rank6.SecondJacobianBasic
import Common.Elliptic.QuadricIntersectionJacobianTheorem
import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange

/-!
# The second-base invariant Jacobian and the printed J2 equation

Jaswal, Theorem 8.1(a), DOI 10.5281/zenodo.23437117. The Hessian
pencil of the projective G2 intersection has the invariants of J2 scaled
by 58⁴ and 58⁶. The CFS invariant equation is carried to the printed model
by the Weierstrass change (u,r,s,t)=(348,40368,0,0).
-/

namespace Z2Z4Rank6.SecondBaseJacobianInvariants
noncomputable section
open SecondBaseProjectiveScheme

theorem c4_eq : QuadricIntersectionModel.c4 model=58^4*J2.c₄ := by
  norm_num [QuadricIntersectionModel.c4,QuadricIntersectionModel.invariantI,
    pencilPolynomial_expanded,Polynomial.coeff_add,Polynomial.coeff_sub,
    Polynomial.coeff_C_mul,Polynomial.coeff_X_pow,Polynomial.coeff_X,
    J2,WeierstrassCurve.c₄,WeierstrassCurve.b₂,WeierstrassCurve.b₄]

theorem c6_eq : QuadricIntersectionModel.c6 model=58^6*J2.c₆ := by
  norm_num [QuadricIntersectionModel.c6,QuadricIntersectionModel.invariantJ,
    pencilPolynomial_expanded,Polynomial.coeff_add,Polynomial.coeff_sub,
    Polynomial.coeff_C_mul,Polynomial.coeff_X_pow,Polynomial.coeff_X,
    J2,WeierstrassCurve.c₆,WeierstrassCurve.b₂,WeierstrassCurve.b₄,WeierstrassCurve.b₆]

def toPrintedChange : WeierstrassCurve.VariableChange ℚ where
  u := Units.mk0 348 (by norm_num)
  r := 40368
  s := 0
  t := 0

/-- A rational admissible variable change identifies the entire
invariant Weierstrass equation with the entire printed J2 equation. -/
theorem variableChange_eq :
    toPrintedChange • QuadricIntersectionModel.invariantCurve model=J2 := by
  ext <;>
    norm_num [WeierstrassCurve.variableChange_a₁,WeierstrassCurve.variableChange_a₂,
      WeierstrassCurve.variableChange_a₃,WeierstrassCurve.variableChange_a₄,
      WeierstrassCurve.variableChange_a₆,toPrintedChange,
      QuadricIntersectionModel.invariantCurve,c4_eq,c6_eq,J2,
      WeierstrassCurve.c₄,WeierstrassCurve.c₆,WeierstrassCurve.b₂,
      WeierstrassCurve.b₄,WeierstrassCurve.b₆]

end
end Z2Z4Rank6.SecondBaseJacobianInvariants
