import Z2Z4Rank6.SecondCongruenceModels
namespace Z2Z4Rank6
open SecondFamily
set_option maxHeartbeats 10000
theorem second_scaled_integralModel (i:Fin 6) (P:G2Point ℚ) (h:SecondCongruentAt i P) :
    IntegralModelAt (SecondReductionData.primes i) (secondScaledCurve P.W) := by
  simp only [IntegralModelAt,secondScaledCurve,PointScaling.curve]
  have hc:=second_model_congruences i P h
  exact ⟨integralAt_zero,hc.1.1,integralAt_zero,hc.2.1,integralAt_zero⟩

theorem second_scaled_reducedModel (i:Fin 6) (P:G2Point ℚ) (h:SecondCongruentAt i P) :
    reducedModel (SecondReductionData.primes i) (secondScaledCurve P.W)=SecondReductionData.curve i := by
  have hc:=second_model_congruences i P h
  have he : reducedModel (SecondReductionData.primes i) (secondScaledCurve P.W)=
      reducedModel (SecondReductionData.primes i) (secondScaledCurve SecondReductionData.baseW) := by
    simp only [reducedModel,secondScaledCurve,PointScaling.curve]
    apply WeierstrassCurve.ext
    · rfl
    · exact hc.1.2.2
    · rfl
    · exact hc.2.2.2
    · rfl
  have hb : secondScaledCurve SecondReductionData.baseW=SecondReductionData.rationalCurve :=
    SecondReductionData.scaled_curve
  exact he.trans ((congrArg (fun C:WeierstrassCurve ℚ=>reducedModel (SecondReductionData.primes i) C) hb).trans
    (SecondReductionData.reduced_model i))



end Z2Z4Rank6
