module

public import Z2Z4Rank6.SecondFunctionFieldPointPlace

@[expose] public section

/-!
# Integral second-family models at the constructed rational places

The power-series model has constant fiber F(P.W) and its Laurent
base change is the image of the generic curve.
-/
namespace Z2Z4Rank6.SecondFunctionFieldPointPlace
noncomputable section
open Polynomial SecondFamily

local instance secondPointPlaceModelRatAlgebra : Algebra ℚ SecondFunctionField.K := DivisionRing.toRatAlgebra

section Generic
variable {L : Type*} [Field L] [CharZero L]

theorem uPolynomial_aeval (t : L) : aeval t uPolynomial=U t := by
  norm_num [uPolynomial,U,lambda,map_ofNat]

theorem vPolynomial_aeval (t : L) : aeval t vPolynomial=V t := by
  norm_num [vPolynomial,V,lambda,map_ofNat]
end Generic

theorem embedding_polynomial (P : Point) (p : ℚ[X]) :
    embedding P (aeval SecondFunctionField.W p)=
      algebraMap PS LS (UnivariateLocal.polynomialSeries P.val.W p) := by
  have hpoly : algebraMap SecondFunctionField.Base SecondFunctionField.K
      (algebraMap ℚ[X] SecondFunctionField.Base p)=aeval SecondFunctionField.W p := by
    have hC : (algebraMap SecondFunctionField.Base SecondFunctionField.K).comp
        (RatFunc.C : ℚ→+*SecondFunctionField.Base)=algebraMap ℚ SecondFunctionField.K :=
      Subsingleton.elim _ _
    induction p using Polynomial.induction_on' with
    | add p q hp hq => simp only [map_add,hp,hq]
    | monomial n r =>
      have hr := RingHom.congr_fun hC r
      simp only [RingHom.comp_apply] at hr
      simp only [RatFunc.algebraMap_monomial,map_mul,map_pow,aeval_monomial,SecondFunctionField.W,hr]
  rw [←hpoly,embedding_base]
  exact UnivariateLocal.baseEmbedding_polynomial P.val.W p

/-- This integral model depends only on the rational W-coordinate. -/
def seriesCurve (P : Point) : WeierstrassCurve PS where
  a₁:=0
  a₂:=UnivariateLocal.polynomialSeries P.val.W uPolynomial
  a₃:=0
  a₄:=(UnivariateLocal.polynomialSeries P.val.W vPolynomial)^2
  a₆:=0

theorem seriesCurve_constant (P : Point) :
    (seriesCurve P).map PowerSeries.constantCoeff=F P.val.W := by
  have hu : uPolynomial.eval P.val.W=U P.val.W := by
    simpa only [Polynomial.coe_aeval_eq_eval] using uPolynomial_aeval P.val.W
  have hv : vPolynomial.eval P.val.W=V P.val.W := by
    simpa only [Polynomial.coe_aeval_eq_eval] using vPolynomial_aeval P.val.W
  ext <;> simp [seriesCurve,F,twistedF,hu,hv]

theorem seriesCurve_laurent (P : Point) :
    (seriesCurve P).map (algebraMap PS LS)=(F SecondFunctionField.W).map (embedding P) := by
  have hu : embedding P (U SecondFunctionField.W)=
      algebraMap PS LS (UnivariateLocal.polynomialSeries P.val.W uPolynomial) := by
    rw [←uPolynomial_aeval]
    exact embedding_polynomial P _
  have hv : embedding P (V SecondFunctionField.W)=
      algebraMap PS LS (UnivariateLocal.polynomialSeries P.val.W vPolynomial) := by
    rw [←vPolynomial_aeval]
    exact embedding_polynomial P _
  ext <;> simp [seriesCurve,F,twistedF,hu,hv]

theorem constantFiber_elliptic (P : Point) (hP : GoodCurve (F P.val.W)) :
    ((seriesCurve P).map PowerSeries.constantCoeff).IsElliptic := by
  rw [seriesCurve_constant]
  exact hP

theorem seriesCurve_elliptic (P : Point) (hP : GoodCurve (F P.val.W)) :
    (seriesCurve P).IsElliptic := by
  constructor
  rw [PowerSeries.isUnit_iff_constantCoeff,←WeierstrassCurve.map_Δ,seriesCurve_constant]
  exact hP.isUnit

instance laurentFiber_elliptic (P : Point) :
    ((seriesCurve P).map (algebraMap PS LS)).IsElliptic := by
  rw [seriesCurve_laurent]
  infer_instance

theorem place_model_injective :
    Function.Injective (fun P : Point => (embeddingAlgHom P,seriesCurve P)) := by
  intro P Q h
  exact embeddingAlgHom_injective_on_points (congrArg Prod.fst h)

end
end Z2Z4Rank6.SecondFunctionFieldPointPlace
