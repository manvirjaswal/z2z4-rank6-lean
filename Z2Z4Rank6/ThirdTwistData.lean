module

public import Z2Z4Rank6.GusicTadicSpecialization
public import Z2Z4Rank6.VariableChangePoints
public import Z2Z4Rank6.TwistSelmerDataNecessary

@[expose] public section

/-!
# The third twist and its four specialized integral models

The unnumbered third-twist paragraph after Proposition 7.2 in Jaswal,
DOI 10.5281/zenodo.23437117.
-/
namespace Z2Z4Rank6.ThirdTwist
noncomputable section
open Polynomial GusicTadic
local notation "T" => (Polynomial.X : ℤ[X])

def q3 {R : Type*} [CommRing R] (m : R) : R := 4*m^2+45
def q3Poly : ℤ[X] := q3 T
def twistPolynomial : Fin 4 → ℤ[X] :=
  ![q3Poly,q3Poly*q1Poly,q3Poly*q2Poly,q3Poly*q12Poly]
def parameter : Fin 4 → ℚ := ![42,-58/3,-58/3,-46/7]
def D : Fin 4 → ℤ := ![789,34014894,24714163,3134836358146]
def A : Fin 4 → ℤ := ![1123441,2203201,2203201,115869289]
def B : Fin 4 → ℤ := ![430559,1239215,1239215,60264711]
def scale : Fin 4 → ℚ := ![189,875/729,875/729,1/117649]

def r2 (k : Fin 4) : ℤ := D k*(A k)^2
def r3 (k : Fin 4) : ℤ := D k*(B k)^2
def curve (k : Fin 4) : WeierstrassCurve ℚ :=
  splitWeierstrass 0 (-(r2 k:ℚ)) (-(r3 k:ℚ))
def fiber (k : Fin 4) : WeierstrassCurve ℚ :=
  GusicTadic.fiberModel (twistPolynomial k) (parameter k)

theorem scale_ne_zero (k : Fin 4) : scale k≠0 := by fin_cases k <;> norm_num [scale]
theorem roots_nonzero_distinct (k : Fin 4) : r2 k≠0 ∧ r3 k≠0 ∧ r2 k≠r3 k := by
  fin_cases k <;> norm_num [r2,r3,D,A,B]
theorem roots_ordered (k : Fin 4) : 0<r3 k ∧ r3 k<r2 k := by
  fin_cases k <;> norm_num [r2,r3,D,A,B]

theorem curve_eq_twistModel (k : Fin 4) :
    curve k=GusicTadic.twistModel (D k:ℚ) (A k) (B k) := by
  ext <;> simp [curve,splitWeierstrass,GusicTadic.twistModel,r2,r3] <;> ring

instance curveElliptic (k : Fin 4) : (curve k).IsElliptic := by
  rw [curve_eq_twistModel]
  constructor
  rw [isUnit_iff_ne_zero,GusicTadic.twistModel_discriminant]
  fin_cases k <;> norm_num [D,A,B,E,WeierstrassCurve.Δ,WeierstrassCurve.b₂,
    WeierstrassCurve.b₄,WeierstrassCurve.b₆,WeierstrassCurve.b₈]

theorem normalized_scaling (k : Fin 4) :
    scalingChange (Units.mk0 (scale k) (scale_ne_zero k)) • curve k=fiber k := by
  fin_cases k <;> ext <;> norm_num [scalingChange,curve,splitWeierstrass,r2,r3,D,A,B,scale,
    fiber,GusicTadic.fiberModel,GusicTadic.twistModel,parameter,twistPolynomial,q3Poly,q3,
    q1Poly,q2Poly,q12Poly,q1,q2,q12,GusicTadic.evalAt,a,b,
    WeierstrassCurve.variableChange_a₁,WeierstrassCurve.variableChange_a₂,
    WeierstrassCurve.variableChange_a₃,WeierstrassCurve.variableChange_a₄,
    WeierstrassCurve.variableChange_a₆]

def fiberEquiv (k : Fin 4) : RationalPoints (fiber k) ≃+ RationalPoints (curve k) :=
  (PointScaling.pointCongr (normalized_scaling k).symm).trans
    (VariableChangePoints.pointEquiv (curve k)
      (scalingChange (Units.mk0 (scale k) (scale_ne_zero k))))

theorem q3Poly_content : q3Poly.content=1 := by
  have ha : q3Poly.content∣45 := by simpa [q3Poly,q3] using content_dvd_coeff (p:=q3Poly) 0
  have hb : q3Poly.content∣4 := by simpa [q3Poly,q3] using content_dvd_coeff (p:=q3Poly) 2
  have h1 : q3Poly.content∣1 := by
    have h := dvd_sub ha (dvd_mul_of_dvd_right hb 11)
    norm_num at h
    exact h
  have hn : normalize q3Poly.content=1 := normalize_eq_one.mpr (isUnit_of_dvd_one h1)
  simpa only [normalize_content] using hn

theorem q3Q_irreducible : Irreducible (4*(Polynomial.X:ℚ[X])^2+45) := by
  apply irreducible_of_degree_le_three_of_not_isRoot
  · have hd : (4*(Polynomial.X:ℚ[X])^2+45).natDegree=2 := by compute_degree!
    rw [hd]
    decide
  · intro x hx
    have he : 4*x^2+45=0 := by
      simpa only [IsRoot,eval_add,eval_mul,eval_pow,eval_X,eval_ofNat] using hx
    nlinarith [sq_nonneg x]

theorem q3Poly_irreducible : Irreducible q3Poly := by
  have hp := isPrimitive_iff_content_eq_one.mpr q3Poly_content
  apply (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast hp).2
  simpa [q3Poly,q3] using q3Q_irreducible

end
end Z2Z4Rank6.ThirdTwist
