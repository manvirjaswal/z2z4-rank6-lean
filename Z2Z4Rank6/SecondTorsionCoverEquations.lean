module

public import Z2Z4Rank6.SecondTorsionCoverEquationForms
public import Z2Z4Rank6.SecondTorsionCoverPolynomialData

@[expose] public section
namespace Z2Z4Rank6.SecondTorsionCoverEquations
noncomputable section
open SecondFamily
open scoped Classical
theorem aeval_affine {A : Type*} [CommRing A] [Algebra ℚ A] (ε : Bool) (m : A) (i : Fin 3) :
    Polynomial.aeval m (SecondTorsionCoverPolynomialData.affineRadicand ε i)=binary ε 1 m i := by
  fin_cases i <;> norm_num [SecondTorsionCoverPolynomialData.affineRadicand,binary]
  all_goals norm_num only [map_ofNat]
theorem aeval_infinity {A : Type*} [CommRing A] [Algebra ℚ A] (ε : Bool) (z : A) (i : Fin 3) :
    Polynomial.aeval z (SecondTorsionCoverPolynomialData.infinityRadicand ε i)=binary ε z 1 i := by
  fin_cases i <;> norm_num [SecondTorsionCoverPolynomialData.infinityRadicand,binary]
  all_goals norm_num only [map_ofNat]

end
end Z2Z4Rank6.SecondTorsionCoverEquations
