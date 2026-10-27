module

public import Z2Z4Rank6.BaseCurveArithmetic
public import Z2Z4Rank6.GJacobianBasic
public import Z2Z4Rank6.SecondJacobianBasic
public import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange

@[expose] public section

/-!
# The explicit CFS quartic models and their printed Weierstrass equations

Cremona–Fisher–Stoll, arXiv:0908.1741v1, Lemma 2.9, equation (2.3), p. 7,
specialized to P=0. Theorem 2.10, p. 8 identifies this equation as the geometric
Jacobian when the quartic discriminant is nonzero. This file checks the Weierstrass models and admissible coordinate changes
for the three quartics of Jaswal, DOI 10.5281/zenodo.23437117. The scheme-level
Jacobian identifications are proved in the corresponding Jacobian modules.
-/
namespace Z2Z4Rank6
namespace QuarticCFS
variable {R : Type*} [CommRing R]

def model (a b c d e : R) : WeierstrassCurve R where
  a₁:=0
  a₂:=c
  a₃:=0
  a₄:=b*d-4*a*e
  a₆:=a*d^2+b^2*e-4*a*c*e

def invariantI (a b c d e : R) : R := 12*a*e-3*b*d+c^2
def invariantJ (a b c d e : R) : R :=
  72*a*c*e-27*a*d^2-27*b^2*e+9*b*c*d-2*c^3

theorem model_c4 (a b c d e : R) : (model a b c d e).c₄=16*invariantI a b c d e := by
  simp only [model,invariantI,WeierstrassCurve.c₄,WeierstrassCurve.b₂,WeierstrassCurve.b₄]
  ring

theorem model_c6 (a b c d e : R) : (model a b c d e).c₆=32*invariantJ a b c d e := by
  simp only [model,invariantJ,WeierstrassCurve.c₆,WeierstrassCurve.b₂,
    WeierstrassCurve.b₄,WeierstrassCurve.b₆]
  ring
end QuarticCFS

def baseQuarticCFSChange : WeierstrassCurve.VariableChange ℚ where
  u:=Units.mk0 2 (by norm_num)
  r:=-170
  s:=0
  t:=0

def gQuarticCFSChange : WeierstrassCurve.VariableChange ℚ where
  u:=Units.mk0 2 (by norm_num)
  r:=3334
  s:=0
  t:=0

def secondQuarticCFSChange : WeierstrassCurve.VariableChange ℚ where
  u:=1
  r:=25870384814
  s:=0
  t:=0

theorem baseQuarticCFSModel_to_EC :
    baseQuarticCFSChange • QuarticCFS.model 49 (-56) 514 (-840) 11025=EC := by
  ext <;> norm_num [baseQuarticCFSChange,QuarticCFS.model,WeierstrassCurve.variableChange_def,EC]

theorem gQuarticCFSModel_to_JG :
    gQuarticCFSChange • QuarticCFS.model 99 0 (-9998) 0 970299=JG := by
  ext <;> norm_num [gQuarticCFSChange,QuarticCFS.model,WeierstrassCurve.variableChange_def,JG]

theorem secondQuarticCFSModel_to_J2 :
    secondQuarticCFSChange • QuarticCFS.model 1326538900 0 (-77611154441) 0 1115619214900=J2 := by
  ext <;> norm_num [secondQuarticCFSChange,QuarticCFS.model,WeierstrassCurve.variableChange_def,J2]

end Z2Z4Rank6
