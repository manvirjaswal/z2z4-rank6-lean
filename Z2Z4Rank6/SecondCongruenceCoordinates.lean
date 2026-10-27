module

public import Z2Z4Rank6.SecondCongruenceSections

@[expose] public section
namespace Z2Z4Rank6
open SecondFamily
theorem second_scaled_coordinates (i j:Fin 6) (P:G2Point ℚ) (h:SecondCongruentAt i P) :
    IntegralAt (SecondReductionData.primes i) (SecondReductionData.scale^2*P.sixX j) ∧
    IntegralAt (SecondReductionData.primes i) (SecondReductionData.scale^3*P.sixY j) ∧
    residue (SecondReductionData.primes i) (SecondReductionData.scale^2*P.sixX j)=
      (SecondReductionData.reducedX i j:ZMod (SecondReductionData.primes i)) ∧
    residue (SecondReductionData.primes i) (SecondReductionData.scale^3*P.sixY j)=
      (SecondReductionData.reducedY i j:ZMod (SecondReductionData.primes i)) := by
  have hs : IntegralAt (SecondReductionData.primes i) SecondReductionData.scale := by
    unfold IntegralAt
    fin_cases i <;> decide +kernel
  have hc:=second_section_congruences i P h j
  have hx : residue (SecondReductionData.primes i) (SecondReductionData.scale^2*P.sixX j)=
      residue (SecondReductionData.primes i) (SecondReductionData.scale^2*SecondReductionData.basePoint.sixX j) := by
    rw [residue_mul (hs.pow 2) hc.1.1,residue_mul (hs.pow 2) hc.1.2.1,hc.1.2.2]
  have hy : residue (SecondReductionData.primes i) (SecondReductionData.scale^3*P.sixY j)=
      residue (SecondReductionData.primes i) (SecondReductionData.scale^3*SecondReductionData.basePoint.sixY j) := by
    rw [residue_mul (hs.pow 3) hc.2.1,residue_mul (hs.pow 3) hc.2.2.1,hc.2.2.2]
  have ex := congrArg (residue (SecondReductionData.primes i))
    (SecondReductionData.rationalX_eq_scaled_section j)
  have ey := congrArg (residue (SecondReductionData.primes i))
    (SecondReductionData.rationalY_eq_scaled_section j)
  exact ⟨(hs.pow 2).mul hc.1.1,(hs.pow 3).mul hc.2.1,
    hx.trans (ex.symm.trans (SecondReductionData.rational_coordinates_residue i j).1),
    hy.trans (ey.symm.trans (SecondReductionData.rational_coordinates_residue i j).2)⟩


end Z2Z4Rank6
