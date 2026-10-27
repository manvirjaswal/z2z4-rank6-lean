module

public import Z2Z4Rank6.TwistSelmerData
public import Z2Z4Rank6.VariableChangePoints

@[expose] public section

/-!
# The extra h-twist fiber in Proposition 7.2(b)

Exact integer model and rational scaling for the specialization m=-80/3
in Jaswal, DOI 10.5281/zenodo.23437117.
-/

namespace Z2Z4Rank6.GTwistSelmer

noncomputable section
open Polynomial

def hPolynomial : ℤ[X] := 99*Polynomial.X^4-9998*Polynomial.X^2+970299
def parameter : ℚ := -80/3
def D : ℤ := 8067459
def A : ℤ := 24836383
def B : ℤ := 12939617
def C : ℕ := 2*3*5*7*593*787*1433
def scale : ℚ := 343/243
def r2 : ℤ := D*A^2
def r3 : ℤ := D*B^2
def curve : WeierstrassCurve ℚ := splitWeierstrass 0 (-(r2:ℚ)) (-(r3:ℚ))
def fiber : WeierstrassCurve ℚ := GusicTadic.fiberModel hPolynomial parameter

theorem parameter_values :
    a parameter=(49/81:ℚ)*A ∧ b parameter=(49/81:ℚ)*B := by
  norm_num [parameter,a,b,A,B]

theorem twist_squareclass : GusicTadic.evalAt parameter hPolynomial=(D:ℚ)*(7/3:ℚ)^2 := by
  norm_num [GusicTadic.evalAt,parameter,hPolynomial,D]

theorem A_factorization : A=11*13*29*53*113 := by decide
theorem B_factorization : B=31*47*83*107 := by decide
theorem D_factorization : D=3*1291*2083 := by decide
theorem difference_factorization : A^2-B^2=2^8*3*5^3*7*593*787*1433 := by
  norm_num [A,B]

theorem scale_ne_zero : scale≠0 := by norm_num [scale]
theorem roots_nonzero_distinct : r2≠0 ∧ r3≠0 ∧ r2≠r3 := by norm_num [r2,r3,D,A,B]
theorem roots_ordered : 0<r3 ∧ r3<r2 := by norm_num [r2,r3,D,A,B]

theorem curve_eq_twistModel : curve=GusicTadic.twistModel (D:ℚ) A B := by
  ext <;> simp [curve,splitWeierstrass,GusicTadic.twistModel,r2,r3] <;> ring

theorem normalized_scaling :
    scalingChange (Units.mk0 scale scale_ne_zero) • curve=fiber := by
  ext <;> norm_num [scalingChange,curve,splitWeierstrass,r2,r3,D,A,B,scale,
    fiber,GusicTadic.fiberModel,GusicTadic.twistModel,parameter,hPolynomial,
    GusicTadic.evalAt,a,b,WeierstrassCurve.variableChange_a₁,
    WeierstrassCurve.variableChange_a₂,WeierstrassCurve.variableChange_a₃,
    WeierstrassCurve.variableChange_a₄,WeierstrassCurve.variableChange_a₆]

instance curveElliptic : curve.IsElliptic := by
  rw [curve_eq_twistModel]
  constructor
  rw [isUnit_iff_ne_zero,GusicTadic.twistModel_discriminant]
  norm_num [D,A,B,E,WeierstrassCurve.Δ,WeierstrassCurve.b₂,
    WeierstrassCurve.b₄,WeierstrassCurve.b₆,WeierstrassCurve.b₈]

def fiberEquiv : RationalPoints fiber ≃+ RationalPoints curve :=
  (PointScaling.pointCongr normalized_scaling.symm).trans
    (VariableChangePoints.pointEquiv curve (scalingChange (Units.mk0 scale scale_ne_zero)))

theorem supports_coprime : A.natAbs.Coprime B.natAbs ∧ A.natAbs.Coprime C ∧ B.natAbs.Coprime C := by
  norm_num [A,B,C,Nat.Coprime]

theorem supports (d : ECFullTriple) (h : d ∈ fullTwoSelmerTriples r2 r3) :
    d.1 ∣ D*A*B ∧ d.2.1 ∣ D*A*(C:ℤ) ∧ d.2.2 ∣ D*B*(C:ℤ) := by
  refine ⟨?_,?_,?_⟩
  · apply (h.1.dvd_pow_iff_dvd (by decide : 2≠0)).mp
    apply h.2.2.2.1.trans
    refine ⟨1,?_⟩
    dsimp [r2,r3]
    ring
  · apply (h.2.1.dvd_pow_iff_dvd (by decide : 10≠0)).mp
    apply h.2.2.2.2.1.trans
    norm_num [r2,r3,D,A,B,C]
  · apply (h.2.2.1.dvd_pow_iff_dvd (by decide : 10≠0)).mp
    apply h.2.2.2.2.2.1.trans
    norm_num [r2,r3,D,A,B,C]

end
end Z2Z4Rank6.GTwistSelmer
