import Z2Z4Rank6.SecondFunctionFieldLocal

namespace Z2Z4Rank6.SecondFunctionFieldLocal

open Polynomial SecondFamily

noncomputable section

set_option maxHeartbeats 300000

def uPolynomial : ℚ[X] := 2*(1+C lambda)^2*Polynomial.X+2*(Polynomial.X+C lambda)^2
def vPolynomial : ℚ[X] := -(Polynomial.X-1)*(Polynomial.X-C (lambda^2))

def xNumerator : Fin 6 → ℚ[X] :=
  ![C ((mu:ℚ)^(-2:ℤ))*(Polynomial.X-C (lambda^2))^2,
    C ((1015/1089:ℚ)^2)*(Polynomial.X-1)*(Polynomial.X-C (lambda^2)),
    C ((928/1089:ℚ)^2)*(Polynomial.X-1)*(Polynomial.X-C beta),
    C ((1015/1089:ℚ)^2)*Polynomial.X^2*(Polynomial.X-1)*(Polynomial.X-C (lambda^2)),
    C ((928/1089:ℚ)^2/lambda^2)*Polynomial.X^2*
      (C (lambda^2)-Polynomial.X)*(C (lambda^2)-C beta*Polynomial.X),
    C ((240/289:ℚ)^2)*(Polynomial.X-C beta)^2*(Polynomial.X-C gamma)^2]

def yNumerator : Fin 6 → ℚ[X] :=
  ![C ((33/19:ℚ)*(1450/361))*(Polynomial.X+C lambda)*(Polynomial.X-C (lambda^2))^2,
    C ((29:ℚ)*(1015/1089))*(Polynomial.X-1)*(Polynomial.X-C (lambda^2))*
      (Polynomial.X^2-C (648517/1185921)*Polynomial.X+C (3467044/1291467969)),
    C ((29:ℚ)*(928/1089))*(Polynomial.X-1)*(Polynomial.X-C beta)^2*
      (Polynomial.X-C (625/1089)),
    C ((29:ℚ)*(1015/1089)/lambda)*Polynomial.X^2*(Polynomial.X-1)*
      (Polynomial.X-C (lambda^2))*(C (lambda^4)-C ((648517/1185921:ℚ)*lambda^2)*
        Polynomial.X+C (3467044/1291467969)*Polynomial.X^2),
    C ((29:ℚ)*(928/1089)/lambda^3)*Polynomial.X^2*(C (lambda^2)-Polynomial.X)*
      (C (lambda^2)-C beta*Polynomial.X)^2*(C (lambda^2)-C (625/1089)*Polynomial.X),
    C ((240/289:ℚ)*(161/289)^2)*(Polynomial.X-C beta)^2*(Polynomial.X-C gamma)^2*
      (Polynomial.X^2-C (14138244652530322/796818233864961)*Polynomial.X+C (lambda^2))]

def qDenominator : Fin 6 → ℚ[X] :=
  ![1,SecondFunctionField.polynomialA,SecondFunctionField.polynomialA,
    Polynomial.X*SecondFunctionField.polynomialB,Polynomial.X*SecondFunctionField.polynomialB,
    -(Polynomial.X-C beta)*(Polynomial.X-C gamma)]

variable {L : Type*} [Field L] [CharZero L]

def rootFactor (P : G2Point L) : Fin 6 → L :=
  ![1,P.s2,P.s2,P.s1*P.s3,P.s1*P.s3,1089*P.s2*P.s3/4669]

theorem uPolynomial_eval (t : L) : aeval t uPolynomial=U t := by
  norm_num [uPolynomial,U,lambda,map_ofNat]

theorem vPolynomial_eval (t : L) : aeval t vPolynomial=V t := by
  norm_num [vPolynomial,V,lambda,map_ofNat]

theorem xNumerator_eval (t : L) (ht : t ≠ 0) (j : Fin 6) :
    aeval t (xNumerator j)=![x1 t,x2 t,x3 t,x4 t,x5 t,x6 t] j := by
  fin_cases j <;>
    norm_num [xNumerator,x1,x2,x3,x4,x5,x6,mu,lambda,beta,gamma,
      sigma,iotaScale,map_ofNat] <;>
    field_simp <;> ring

theorem yNumerator_eval (t : L) (ht : t ≠ 0) (j : Fin 6) :
    aeval t (yNumerator j)=![y1 t,y2 t,y3 t,y4 t,y5 t,y6 t] j := by
  fin_cases j <;>
    norm_num [yNumerator,y1,y2,y3,y4,y5,y6,f2,f6,lambda,beta,gamma,
      sigma,iotaScale,map_ofNat] <;>
    field_simp <;> ring

theorem qDenominator_eval (t : L) (j : Fin 6) :
    aeval t (qDenominator j)=![1,qA t,qA t,t*qB t,t*qB t,qH t] j := by
  fin_cases j <;>
    norm_num [qDenominator,SecondFunctionField.polynomialA,SecondFunctionField.polynomialB,
      qA,qB,qH,beta,gamma,map_ofNat]

theorem sixX_fraction (P : G2Point L) (hW : P.W ≠ 0) (j : Fin 6) :
    P.sixX j=aeval P.W (xNumerator j)/aeval P.W (qDenominator j) := by
  rw [xNumerator_eval P.W hW j,qDenominator_eval P.W j]
  fin_cases j <;> simp [G2Point.sixX,G2Point.untwistedX2,G2Point.untwistedX3,
    G2Point.untwistedX4,G2Point.untwistedX5,G2Point.untwistedX6]

theorem sixY_fraction (P : G2Point L) (hW : P.W ≠ 0) (j : Fin 6) :
    P.sixY j=aeval P.W (yNumerator j)/(aeval P.W (qDenominator j)*rootFactor P j) := by
  rw [yNumerator_eval P.W hW j,qDenominator_eval P.W j]
  fin_cases j <;> simp [G2Point.sixY,G2Point.untwistedY2,G2Point.untwistedY3,
    G2Point.untwistedY4,G2Point.untwistedY5,G2Point.untwistedY6,rootFactor]

open SecondReductionData

-- Generic field formulas use the canonical rational algebra. Keep that
-- coefficient map when specializing them to the three-level quadratic tower.
local instance : Algebra ℚ SecondFunctionField.K := DivisionRing.toRatAlgebra

def rootSeries : Fin 6 → PS :=
  ![1,s2Series,s2Series,s1Series*s3Series,s1Series*s3Series,
    PowerSeries.C (1089/4669)*s2Series*s3Series]

def qSeries (j : Fin 6) : PS := UnivariateLocal.polynomialSeries baseW (qDenominator j)

theorem rootSeries_constant (j : Fin 6) :
    PowerSeries.constantCoeff (rootSeries j)=rootFactor basePoint j := by
  fin_cases j <;>
    simp [rootSeries,rootFactor,s1Series_spec.2,s2Series_spec.2,s3Series_spec.2,basePoint]
  ring

theorem qSeries_constant (j : Fin 6) :
    PowerSeries.constantCoeff (qSeries j)=aeval baseW (qDenominator j) := by
  rw [qSeries,UnivariateLocal.polynomialSeries_constant]
  rw [Polynomial.coe_aeval_eq_eval]

theorem qSeries_constant_ne_zero (j : Fin 6) :
    PowerSeries.constantCoeff (qSeries j) ≠ 0 := by
  rw [qSeries_constant,qDenominator_eval]
  have hH := qH_ne_zero_of_qA_qB baseW base_regular.2.1 base_regular.2.2
  fin_cases j
  · norm_num
  · exact base_regular.2.1
  · exact base_regular.2.1
  · exact mul_ne_zero base_regular.1 base_regular.2.2
  · exact mul_ne_zero base_regular.1 base_regular.2.2
  · exact hH

theorem rootSeries_constant_ne_zero (j : Fin 6) :
    PowerSeries.constantCoeff (rootSeries j) ≠ 0 := by
  rw [rootSeries_constant]
  fin_cases j <;> norm_num [rootFactor,basePoint,baseS1,baseS2,baseS3]

theorem ordinate_denominator_constant_ne_zero (j : Fin 6) :
    PowerSeries.constantCoeff (qSeries j*rootSeries j) ≠ 0 := by
  rw [map_mul]
  exact mul_ne_zero (qSeries_constant_ne_zero j) (rootSeries_constant_ne_zero j)

def xSeries (j : Fin 6) : PS :=
  UnivariateLocal.polynomialSeries baseW (xNumerator j)*(qSeries j)⁻¹

def ySeries (j : Fin 6) : PS :=
  UnivariateLocal.polynomialSeries baseW (yNumerator j)*(qSeries j*rootSeries j)⁻¹

theorem xSeries_constant (j : Fin 6) :
    PowerSeries.constantCoeff (xSeries j)=basePoint.sixX j := by
  rw [sixX_fraction basePoint base_regular.1 j]
  change PowerSeries.constantCoeff (xSeries j)=
    aeval baseW (xNumerator j)/aeval baseW (qDenominator j)
  simp only [xSeries,map_mul,PowerSeries.constantCoeff_inv,
    UnivariateLocal.polynomialSeries_constant,qSeries_constant,
    Polynomial.coe_aeval_eq_eval,div_eq_mul_inv]

theorem ySeries_constant (j : Fin 6) :
    PowerSeries.constantCoeff (ySeries j)=basePoint.sixY j := by
  rw [sixY_fraction basePoint base_regular.1 j]
  change PowerSeries.constantCoeff (ySeries j)=
    aeval baseW (yNumerator j)/(aeval baseW (qDenominator j)*rootFactor basePoint j)
  simp only [ySeries,map_mul,PowerSeries.constantCoeff_inv,
    UnivariateLocal.polynomialSeries_constant,qSeries_constant,rootSeries_constant,
    Polynomial.coe_aeval_eq_eval,div_eq_mul_inv]

/-- An inverse of a unit power series maps to its field inverse. -/
theorem map_series_inv (d : PS) (hd : PowerSeries.constantCoeff d ≠ 0) :
    algebraMap PS LS (d⁻¹)=(algebraMap PS LS d)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← map_mul,mul_comm d⁻¹ d,PowerSeries.mul_inv_cancel d hd,map_one]

theorem algebraMap_PS_C (r : ℚ) :
    algebraMap PS LS (PowerSeries.C r)=algebraMap ℚ LS r := by
  have h : (algebraMap PS LS).comp (PowerSeries.C : ℚ →+* PS)=algebraMap ℚ LS :=
    Subsingleton.elim _ _
  exact RingHom.congr_fun h r

theorem embedding_polynomial (p : ℚ[X]) :
    embedding (aeval SecondFunctionField.W p)=
      algebraMap PS LS (UnivariateLocal.polynomialSeries baseW p) := by
  have hpoly : algebraMap SecondFunctionField.Base SecondFunctionField.K
      (algebraMap ℚ[X] SecondFunctionField.Base p)=aeval SecondFunctionField.W p := by
    have hC : (algebraMap SecondFunctionField.Base SecondFunctionField.K).comp
        (RatFunc.C : ℚ →+* SecondFunctionField.Base)=algebraMap ℚ SecondFunctionField.K :=
      Subsingleton.elim _ _
    induction p using Polynomial.induction_on' with
    | add p q hp hq => simp only [map_add,hp,hq]
    | monomial n r =>
      have hr := RingHom.congr_fun hC r
      simp only [RingHom.comp_apply] at hr
      simp only [RatFunc.algebraMap_monomial,map_mul,map_pow,aeval_monomial,
        SecondFunctionField.W,hr]
  rw [← hpoly,embedding_base]
  exact UnivariateLocal.baseEmbedding_polynomial baseW p

theorem embedding_rootFactor (j : Fin 6) :
    embedding (rootFactor SecondFunctionField.genericBasePoint j)=
      algebraMap PS LS (rootSeries j) := by
  fin_cases j <;>
    simp [rootFactor,rootSeries,SecondFunctionField.genericBasePoint,map_ofNat]
  ring

/-- The six embedded abscissae are integral power-series values. -/
theorem embedding_sixX (j : Fin 6) :
    embedding (SecondFunctionField.genericBasePoint.sixX j)=
      algebraMap PS LS (xSeries j) := by
  rw [sixX_fraction SecondFunctionField.genericBasePoint SecondFunctionField.W_ne_zero j]
  rw [show SecondFunctionField.genericBasePoint.W=SecondFunctionField.W from rfl]
  rw [map_div₀,embedding_polynomial,embedding_polynomial]
  rw [xSeries,map_mul,map_series_inv (qSeries j) (qSeries_constant_ne_zero j)]
  simp only [qSeries,div_eq_mul_inv]

/-- The six signed embedded ordinates are integral power-series values. -/
theorem embedding_sixY (j : Fin 6) :
    embedding (SecondFunctionField.genericBasePoint.sixY j)=
      algebraMap PS LS (ySeries j) := by
  rw [sixY_fraction SecondFunctionField.genericBasePoint SecondFunctionField.W_ne_zero j]
  rw [show SecondFunctionField.genericBasePoint.W=SecondFunctionField.W from rfl]
  rw [map_div₀,map_mul,embedding_polynomial,embedding_polynomial,embedding_rootFactor]
  rw [ySeries,map_mul,map_series_inv (qSeries j*rootSeries j)
    (ordinate_denominator_constant_ne_zero j)]
  simp only [qSeries,map_mul,div_eq_mul_inv]

/-- The integral Weierstrass model over Q[[T]]. -/
def seriesCurve : WeierstrassCurve PS where
  a₁ := 0
  a₂ := UnivariateLocal.polynomialSeries baseW uPolynomial
  a₃ := 0
  a₄ := (UnivariateLocal.polynomialSeries baseW vPolynomial)^2
  a₆ := 0

theorem seriesCurve_constant :
    seriesCurve.map PowerSeries.constantCoeff=F baseW := by
  have hu : uPolynomial.eval baseW=U baseW := by
    simpa only [Polynomial.coe_aeval_eq_eval] using uPolynomial_eval baseW
  have hv : vPolynomial.eval baseW=V baseW := by
    simpa only [Polynomial.coe_aeval_eq_eval] using vPolynomial_eval baseW
  ext <;> simp [seriesCurve,F,twistedF,hu,hv]

theorem seriesCurve_laurent :
    seriesCurve.map (algebraMap PS LS)=(F SecondFunctionField.W).map embedding := by
  have hu : embedding (U SecondFunctionField.W)=
      algebraMap PS LS (UnivariateLocal.polynomialSeries baseW uPolynomial) := by
    rw [← uPolynomial_eval]
    exact embedding_polynomial _
  have hv : embedding (V SecondFunctionField.W)=
      algebraMap PS LS (UnivariateLocal.polynomialSeries baseW vPolynomial) := by
    rw [← vPolynomial_eval]
    exact embedding_polynomial _
  ext <;> simp [seriesCurve,F,twistedF,hu,hv]

instance constantFiberElliptic : (seriesCurve.map PowerSeries.constantCoeff).IsElliptic := by
  rw [seriesCurve_constant]
  infer_instance

instance laurentFiberElliptic : (seriesCurve.map (algebraMap PS LS)).IsElliptic := by
  rw [seriesCurve_laurent]
  infer_instance

end
end Z2Z4Rank6.SecondFunctionFieldLocal
