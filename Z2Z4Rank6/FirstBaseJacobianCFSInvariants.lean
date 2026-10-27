import Z2Z4Rank6.ProjectiveBaseSchemeStructure
import Z2Z4Rank6.Basic
import Common.Elliptic.QuadricIntersectionJacobianTheorem
import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange

/-!
# The invariant Jacobian of the first base

The first base is the intersection u²=15m²+1210z²,
v²=10m²+1215z². Its Hessian pencil supplies the CFS degree-four
invariants. The whole invariant cubic is carried to the printed EC
equation by the admissible change (u,r,s,t)=(60,1200,0,0).
Source: Jaswal Lemma 4.1(b), DOI 10.5281/zenodo.23437117;
Cremona–Fisher–Stoll Theorem 2.8(iii), arXiv:0908.1741v1 p. 6.
-/
namespace Z2Z4Rank6.FirstBaseJacobianCFS
noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial
set_option backward.isDefEq.respectTransparency false

def model : QuadricIntersectionModel.Model where
  polynomial := ProjectiveBaseScheme.relation
  homogeneous := ProjectiveBaseScheme.relation_homogeneous

/-- The CFS source is the already constructed first-base Proj, including
its rational structure map. The two quotient gradings unfold to
the same homogeneous components. -/
def sourceOverIso : Over.mk ProjectiveBaseScheme.structureMap ≅
    Over.mk (QuadricIntersectionModel.structureMap model) := Iso.refl _

@[simp] private theorem pderiv_two (i : Fin 4) :
    MvPolynomial.pderiv i (2 : QuadricIntersectionModel.PolynomialRing)=0 := by
  rw [show (2 : QuadricIntersectionModel.PolynomialRing)=1+1 by ring]
  simp

theorem hessian_zero : QuadricIntersectionModel.hessian model 0=
    Matrix.diagonal ![(-30:ℚ),2,0,-2420] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [QuadricIntersectionModel.hessian,model,ProjectiveBaseScheme.relation,
      MvPolynomial.pderiv_pow,MvPolynomial.pderiv_mul,MvPolynomial.pderiv_X,
      Matrix.diagonal]

theorem hessian_one : QuadricIntersectionModel.hessian model 1=
    Matrix.diagonal ![(-20:ℚ),0,2,-2430] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [QuadricIntersectionModel.hessian,model,ProjectiveBaseScheme.relation,
      MvPolynomial.pderiv_pow,MvPolynomial.pderiv_mul,MvPolynomial.pderiv_X,
      Matrix.diagonal]

theorem pencilPolynomial_eq : QuadricIntersectionModel.pencilPolynomial model=
    400*Polynomial.X*(3*Polynomial.X+2)*(242*Polynomial.X+243) := by
  have hm : (fun i j=>Polynomial.C (QuadricIntersectionModel.hessian model 0 i j)*
      Polynomial.X+Polynomial.C (QuadricIntersectionModel.hessian model 1 i j))=
      Matrix.diagonal ![-30*Polynomial.X-20,2*Polynomial.X,2,-2420*Polynomial.X-2430] := by
    rw [hessian_zero,hessian_one]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.diagonal,Polynomial.C_ofNat,Polynomial.coeff_neg,sub_eq_add_neg]
  rw [QuadricIntersectionModel.pencilPolynomial,hm,Matrix.det_diagonal]
  simp [Fin.prod_univ_succ]
  ring

theorem pencilPolynomial_expanded : QuadricIntersectionModel.pencilPolynomial model=
    Polynomial.C 290400*Polynomial.X^3+Polynomial.C 485200*Polynomial.X^2+
      Polynomial.C 194400*Polynomial.X := by
  rw [pencilPolynomial_eq]
  simp only [map_ofNat]
  ring

theorem c4_eq : QuadricIntersectionModel.c4 model=10^4*EC.c₄ := by
  norm_num [QuadricIntersectionModel.c4,QuadricIntersectionModel.invariantI,
    pencilPolynomial_expanded,Polynomial.coeff_add,Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow,Polynomial.coeff_X,EC,WeierstrassCurve.c₄,
    WeierstrassCurve.b₂,WeierstrassCurve.b₄]

theorem c6_eq : QuadricIntersectionModel.c6 model=10^6*EC.c₆ := by
  norm_num [QuadricIntersectionModel.c6,QuadricIntersectionModel.invariantJ,
    pencilPolynomial_expanded,Polynomial.coeff_add,Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow,Polynomial.coeff_X,EC,WeierstrassCurve.c₆,
    WeierstrassCurve.b₂,WeierstrassCurve.b₄,WeierstrassCurve.b₆]

theorem discriminant_eq : QuadricIntersectionModel.discriminant model=
    119563310477318400000000000000 := by
  norm_num [QuadricIntersectionModel.discriminant,c4_eq,c6_eq,EC,
    WeierstrassCurve.c₄,WeierstrassCurve.c₆,WeierstrassCurve.b₂,
    WeierstrassCurve.b₄,WeierstrassCurve.b₆]

theorem discriminant_ne_zero : QuadricIntersectionModel.discriminant model≠0 := by
  rw [discriminant_eq]
  norm_num

def toPrintedChange : WeierstrassCurve.VariableChange ℚ where
  u := Units.mk0 60 (by norm_num)
  r := 1200
  s := 0
  t := 0

/-- Equality of all five Weierstrass coefficients, including the
nonzero a6; this is stronger than equality of c4,c6 or j. -/
theorem variableChange_eq :
    toPrintedChange • QuadricIntersectionModel.invariantCurve model=EC := by
  ext <;>
    norm_num [WeierstrassCurve.variableChange_a₁,WeierstrassCurve.variableChange_a₂,
      WeierstrassCurve.variableChange_a₃,WeierstrassCurve.variableChange_a₄,
      WeierstrassCurve.variableChange_a₆,toPrintedChange,
      QuadricIntersectionModel.invariantCurve,c4_eq,c6_eq,EC,
      WeierstrassCurve.c₄,WeierstrassCurve.c₆,WeierstrassCurve.b₂,
      WeierstrassCurve.b₄,WeierstrassCurve.b₆]

end
end Z2Z4Rank6.FirstBaseJacobianCFS
