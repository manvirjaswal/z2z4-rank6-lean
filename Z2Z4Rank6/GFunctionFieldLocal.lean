import Z2Z4Rank6.GReductionRank
import Z2Z4Rank6.UnivariateLocal
import Z2Z4Rank6.FunctionFieldCoordinates

/-!
# A formal place of Q(G) at the printed rank-five specialization

A Hensel root selects η(0)=2447004/2809 at m(0)=291/53. The
involution chart and all five coordinates are integral power series there.
-/

namespace Z2Z4Rank6.GFunctionFieldLocal

open GFunctionField GReductionData
open scoped Classical

noncomputable section

abbrev PS := PowerSeries ℚ
abbrev LS := LaurentSeries ℚ

def mSeries : PS := UnivariateLocal.mSeries baseM

@[simp] theorem mSeries_constant : PowerSeries.constantCoeff mSeries=baseM := by simp [mSeries]

theorem map_h {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (t : R) :
    f (h t)=h (f t) := by simp [h,map_ofNat]

private theorem eta_constant : baseEta^2=PowerSeries.constantCoeff (h mSeries) := by
  rw [map_h,mSeries_constant]
  exact base_on_curve

def etaSeries : PS := Classical.choose (FunctionFieldLocal.exists_square_root_with_constant
  (h mSeries) baseEta eta_constant (by norm_num [baseEta]))

theorem etaSeries_spec : etaSeries^2=h mSeries ∧ PowerSeries.constantCoeff etaSeries=baseEta :=
  Classical.choose_spec (FunctionFieldLocal.exists_square_root_with_constant
    (h mSeries) baseEta eta_constant (by norm_num [baseEta]))

def baseEmbedding : Base →+* LS := UnivariateLocal.baseEmbedding baseM

private theorem local_eta_relation : (algebraMap PS LS etaSeries)^2=baseEmbedding d := by
  rw [← map_pow,etaSeries_spec.1,map_h]
  simp only [d,map_h,baseEmbedding,UnivariateLocal.baseEmbedding_X,mSeries]

def embedding : K →+* LS := FunctionFieldLocal.quadraticLift baseEmbedding d
  (algebraMap PS LS etaSeries) local_eta_relation

theorem embedding_injective : Function.Injective embedding := embedding.injective

@[simp] theorem embedding_base (r : Base) : embedding (algebraMap Base K r)=baseEmbedding r := by
  simp [embedding]

@[simp] theorem embedding_m : embedding m=algebraMap PS LS mSeries := by
  simp [m,baseEmbedding,mSeries]

@[simp] theorem embedding_eta : embedding eta=algebraMap PS LS etaSeries := by
  simp [embedding,eta]

def chartDenominatorSeries : PS := 99-mSeries^2
def mPrimeSeries : PS := (etaSeries-98*mSeries)*chartDenominatorSeries⁻¹
def deltaDenominatorSeries : PS := 14*mPrimeSeries
def deltaSeries : PS := chartDenominatorSeries*deltaDenominatorSeries⁻¹

theorem chart_denominator_constant_ne_zero :
    PowerSeries.constantCoeff chartDenominatorSeries ≠ 0 := by
  norm_num [chartDenominatorSeries,mSeries,baseM,map_ofNat]

theorem mPrimeSeries_constant :
    PowerSeries.constantCoeff mPrimeSeries=mPrime baseM baseEta := by
  simp [mPrimeSeries,chartDenominatorSeries,mPrime,mSeries_constant,etaSeries_spec.2,
    PowerSeries.constantCoeff_inv,map_ofNat,div_eq_mul_inv]

theorem delta_denominator_constant_ne_zero :
    PowerSeries.constantCoeff deltaDenominatorSeries ≠ 0 := by
  rw [deltaDenominatorSeries,map_mul,map_ofNat,mPrimeSeries_constant]
  exact mul_ne_zero (by norm_num) (mPrime_ne_zero baseM baseEta base_regular.1 base_regular.2)

theorem deltaSeries_constant : PowerSeries.constantCoeff deltaSeries=delta baseM baseEta := by
  simp [deltaSeries,deltaDenominatorSeries,chartDenominatorSeries,delta,
    mPrimeSeries_constant,mSeries_constant,PowerSeries.constantCoeff_inv,map_ofNat,div_eq_mul_inv]

theorem embedding_mPrime : embedding (mPrime m eta)=algebraMap PS LS mPrimeSeries := by
  rw [mPrimeSeries,map_mul,UnivariateLocal.map_series_inv chartDenominatorSeries
    chart_denominator_constant_ne_zero]
  simp [mPrime,chartDenominatorSeries,map_ofNat,div_eq_mul_inv]

theorem embedding_delta : embedding (delta m eta)=algebraMap PS LS deltaSeries := by
  rw [deltaSeries,map_mul,UnivariateLocal.map_series_inv deltaDenominatorSeries
    delta_denominator_constant_ne_zero]
  simp [delta,chartDenominatorSeries,deltaDenominatorSeries,embedding_mPrime,map_ofNat,div_eq_mul_inv]

def xSeries : Fin 5 → PS :=
  ![p1x mSeries,p2x mSeries,p3x mSeries,
    deltaSeries^4*p2x mPrimeSeries,deltaSeries^4*p3x mPrimeSeries]

def ySeries : Fin 5 → PS :=
  ![p1y mSeries,p2y mSeries,p3y mSeries,
    deltaSeries^6*p2y mPrimeSeries,deltaSeries^6*p3y mPrimeSeries]

theorem xSeries_constant (j : Fin 5) :
    PowerSeries.constantCoeff (xSeries j)=fiveX baseM baseEta j := by
  fin_cases j <;> simp [xSeries,fiveX,p1x,p2x,p3x,mSeries_constant,
    mPrimeSeries_constant,deltaSeries_constant,map_ofNat]

theorem ySeries_constant (j : Fin 5) :
    PowerSeries.constantCoeff (ySeries j)=fiveY baseM baseEta j := by
  fin_cases j <;> simp [ySeries,fiveY,p1y,p2y,p3y,mSeries_constant,
    mPrimeSeries_constant,deltaSeries_constant,map_ofNat]

theorem embedding_fiveX (j : Fin 5) :
    embedding (fiveX m eta j)=algebraMap PS LS (xSeries j) := by
  fin_cases j <;> simp [fiveX,xSeries,p1x,p2x,p3x,embedding_mPrime,embedding_delta,map_ofNat]

theorem embedding_fiveY (j : Fin 5) :
    embedding (fiveY m eta j)=algebraMap PS LS (ySeries j) := by
  fin_cases j <;> simp [fiveY,ySeries,p1y,p2y,p3y,embedding_mPrime,embedding_delta,map_ofNat]

def seriesCurve : WeierstrassCurve PS := X mSeries

theorem seriesCurve_constant : seriesCurve.map PowerSeries.constantCoeff=X baseM := by
  rw [seriesCurve,FunctionFieldLocal.map_family,mSeries_constant]

theorem seriesCurve_laurent : seriesCurve.map (algebraMap PS LS)=(X m).map embedding := by
  rw [seriesCurve,FunctionFieldLocal.map_family,FunctionFieldLocal.map_family,embedding_m]

instance constantFiberElliptic : (seriesCurve.map PowerSeries.constantCoeff).IsElliptic := by
  rw [seriesCurve_constant]
  infer_instance

instance laurentFiberElliptic : (seriesCurve.map (algebraMap PS LS)).IsElliptic := by
  rw [seriesCurve_laurent]
  infer_instance

end
end Z2Z4Rank6.GFunctionFieldLocal
