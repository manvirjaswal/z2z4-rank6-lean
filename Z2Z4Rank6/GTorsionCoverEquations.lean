import Z2Z4Rank6.GTorsionCoverEquationForms
import Z2Z4Rank6.GTorsionCoverPolynomialData
namespace Z2Z4Rank6.GTorsionCoverEquations
noncomputable section
open scoped Classical
theorem aeval_affine {A : Type*} [CommRing A] [Algebra ℚ A] (ε : Bool) (m : A) (i : Fin 2) :
    Polynomial.aeval m (GTorsionCoverPolynomialData.affineRadicand ε i)=binary ε 1 m i := by
  fin_cases i <;> norm_num [GTorsionCoverPolynomialData.affineRadicand,binary,gQuarticPolynomial,a,b,
    HeightInvariantForms.binaryA,HeightInvariantForms.binaryB]
  all_goals norm_num only [map_ofNat]
theorem aeval_infinity {A : Type*} [CommRing A] [Algebra ℚ A] (ε : Bool) (z : A) (i : Fin 2) :
    Polynomial.aeval z (GTorsionCoverPolynomialData.infinityRadicand ε i)=binary ε z 1 i := by
  fin_cases i <;> norm_num [GTorsionCoverPolynomialData.infinityRadicand,binary,HeightInvariantForms.binaryA,HeightInvariantForms.binaryB]
  all_goals norm_num only [map_ofNat]

end
end Z2Z4Rank6.GTorsionCoverEquations
