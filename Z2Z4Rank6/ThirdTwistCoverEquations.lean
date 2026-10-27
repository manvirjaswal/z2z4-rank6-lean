module

public import Z2Z4Rank6.ThirdTwistCoverEquationForms

@[expose] public section
namespace Z2Z4Rank6.ThirdTwistCoverEquations
noncomputable section
open scoped Classical

theorem aeval_affine {A : Type*} [CommRing A] [Algebra ℚ A] (m : A) (i : Fin 3) :
    Polynomial.aeval m (ThirdTwistCoverPolynomialData.affineRadicand i)=binary 1 m i := by
  fin_cases i <;> norm_num [ThirdTwistCoverPolynomialData.affineRadicand,binary]
  all_goals norm_num only [map_ofNat]

theorem aeval_infinity {A : Type*} [CommRing A] [Algebra ℚ A] (z : A) (i : Fin 3) :
    Polynomial.aeval z (ThirdTwistCoverPolynomialData.infinityRadicand i)=binary z 1 i := by
  fin_cases i <;> norm_num [ThirdTwistCoverPolynomialData.infinityRadicand,binary]
  all_goals norm_num only [map_ofNat]
end
end Z2Z4Rank6.ThirdTwistCoverEquations
