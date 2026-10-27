import Z2Z4Rank6.CongruenceSections
import Z2Z4Rank6.BaseCurve
import Z2Z4Rank6.ReductionCheckOriginal
import Z2Z4Rank6.Torsion

/-!
# Good reduction and coordinate transport at the printed base point

The unit checks and congruence implications of Proposition 6.2 of Manvir
Jaswal, *Infinitely many elliptic curves with torsion Z/2Z × Z/4Z and rank at
least six*, DOI 10.5281/zenodo.23437117. The base point is the point
`c₀=(7401/2399,88235/2399,86835/2399)` printed in Proposition 5.1.
-/

namespace Z2Z4Rank6

open ReductionData

/-- The printed base point has integral affine coordinates at all six primes. -/
theorem baseC0_integral (i : Fin 6) :
    IntegralAt (primes i) baseC0.m ∧ IntegralAt (primes i) baseC0.u ∧
      IntegralAt (primes i) baseC0.v := by
  fin_cases i <;> norm_num [IntegralAt, baseC0, primes]
  all_goals decide +kernel

/-- Reducing the printed rational base point gives the finite-field coordinates
used by the mod-3 certificate. -/
theorem baseC0_residues (i : Fin 6) :
    residue (primes i) baseC0.m=localM i ∧ residue (primes i) baseC0.u=localU i ∧
      residue (primes i) baseC0.v=localV i := by
  fin_cases i <;> norm_num [residue, baseC0, primes, localM, localU, localV]

/-- The common section denominator is a unit at every one of the six primes. -/
theorem baseC0_denominator_unit (i : Fin 6) :
    residue (primes i) (sectionDenominator baseC0.m) ≠ 0 := by
  rw [residue_sectionDenominator (baseC0_integral i).1, (baseC0_residues i).1]
  fin_cases i <;> decide +kernel

/-- The reduced product `ab(a²−b²)` at the base point is nonzero at each prime. -/
theorem baseC0_fiber_product_unit (i : Fin 6) :
    a (localM i)*b (localM i)*((a (localM i))^2-(b (localM i))^2) ≠ 0 := by
  fin_cases i <;> decide +kernel

/-- The rational sections at c₀ reduce to the finite-field sections
used in the mod-3 certificate, with exactly their printed signs. -/
theorem baseC0_section_residues (i j : Fin 6) :
    residue (primes i) (sixX baseC0.m j)=sixX (localM i) j ∧
      residue (primes i) (sixY baseC0.m baseC0.u baseC0.v j)=
        sixY (localM i) (localU i) (localV i) j := by
  have hbase := baseC0_integral i
  have hden := baseC0_denominator_unit i
  constructor
  · rw [residue_sixX hbase.1 (by norm_num [baseC0]) (by norm_num [baseC0]) hden,
      (baseC0_residues i).1]
    fin_cases i <;> fin_cases j <;> decide +kernel
  · rw [residue_sixY hbase.1 hbase.2.1 hbase.2.2 baseC0.u_sq baseC0.v_sq
      (by norm_num [baseC0]) baseC0.u_ne_zero baseC0.v_ne_zero
      (by norm_num [baseC0]) (by norm_num [baseC0]) hden,
      (baseC0_residues i).1, (baseC0_residues i).2.1, (baseC0_residues i).2.2]
    fin_cases i <;> fin_cases j <;> decide +kernel

/-- Congruence of m preserves the common-denominator unit condition. -/
theorem denominator_unit_of_congruent (i : Fin 6) {m : ℚ} (hm : IntegralAt (primes i) m)
    (hcongr : residue (primes i) m=residue (primes i) baseC0.m) :
    residue (primes i) (sectionDenominator m) ≠ 0 := by
  rw [residue_sectionDenominator hm, hcongr,
    ← residue_sectionDenominator (baseC0_integral i).1]
  exact baseC0_denominator_unit i

/-- Congruence to m₀ modulo one selected prime already rules out singular fibers. -/
theorem fiber_product_ne_zero_of_congruent (i : Fin 6) {m : ℚ}
    (hm : IntegralAt (primes i) m)
    (hcongr : residue (primes i) m=residue (primes i) baseC0.m) :
    a m*b m*((a m)^2-(b m)^2) ≠ 0 := by
  apply ne_zero_of_residue_ne_zero (p := primes i)
  rw [residue_fiber_product hm, hcongr, (baseC0_residues i).1]
  exact baseC0_fiber_product_unit i

/-- Every fiber congruent to c₀ modulo a selected prime is an elliptic curve. -/
theorem X_good_of_congruent (i : Fin 6) {m : ℚ} (hm : IntegralAt (primes i) m)
    (hcongr : residue (primes i) m=residue (primes i) baseC0.m) : GoodCurve (X m) :=
  E_good _ _ (fiber_product_ne_zero_of_congruent i hm hcongr)

/-- The reduced model is the nonsingular original finite-field curve used in the certificate. -/
theorem reducedModel_X_of_congruent (i : Fin 6) {m : ℚ} (hm : IntegralAt (primes i) m)
    (hcongr : residue (primes i) m=residue (primes i) baseC0.m) :
    reducedModel (primes i) (X m)=originalCurve i := by
  rw [reducedModel_X hm, hcongr, (baseC0_residues i).1]
  rfl

theorem reducedModel_X_good_of_congruent (i : Fin 6) {m : ℚ} (hm : IntegralAt (primes i) m)
    (hcongr : residue (primes i) m=residue (primes i) baseC0.m) :
    (reducedModel (primes i) (X m)).IsElliptic := by
  rw [reducedModel_X_of_congruent i hm hcongr]
  exact originalCurveElliptic i

/-- All twelve rational section coordinates are integral and reduce as at c₀. -/
theorem CPoint.reduction_data_of_congruent (c : CPoint) (i : Fin 6)
    (hm : IntegralAt (primes i) c.m) (hu : IntegralAt (primes i) c.u)
    (hv : IntegralAt (primes i) c.v)
    (hm' : residue (primes i) c.m=residue (primes i) baseC0.m)
    (hu' : residue (primes i) c.u=residue (primes i) baseC0.u)
    (hv' : residue (primes i) c.v=residue (primes i) baseC0.v) (j : Fin 6) :
    IntegralAt (primes i) (sixX c.m j) ∧ IntegralAt (primes i) (sixY c.m c.u c.v j) ∧
      residue (primes i) (sixX c.m j)=residue (primes i) (sixX baseC0.m j) ∧
      residue (primes i) (sixY c.m c.u c.v j)=residue (primes i) (sixY baseC0.m baseC0.u baseC0.v j) := by
  have hD := denominator_unit_of_congruent i hm hm'
  have hbase := baseC0_integral i
  exact ⟨c.sixX_integral hm hD j, c.sixY_integral hm hu hv hD j,
    c.six_residues_eq baseC0 hm hu hv hbase.1 hbase.2.1 hbase.2.2 hD hm' hu' hv' j⟩

/-- The congruence conditions give precisely the integral coordinates and
finite-field values required by the mod-3 independence certificate. -/
theorem CPoint.reduction_coordinates_of_congruent (c : CPoint) (i : Fin 6)
    (hm : IntegralAt (primes i) c.m) (hu : IntegralAt (primes i) c.u)
    (hv : IntegralAt (primes i) c.v)
    (hm' : residue (primes i) c.m=residue (primes i) baseC0.m)
    (hu' : residue (primes i) c.u=residue (primes i) baseC0.u)
    (hv' : residue (primes i) c.v=residue (primes i) baseC0.v) (j : Fin 6) :
    IntegralAt (primes i) (sixX c.m j) ∧ IntegralAt (primes i) (sixY c.m c.u c.v j) ∧
      residue (primes i) (sixX c.m j)=sixX (localM i) j ∧
      residue (primes i) (sixY c.m c.u c.v j)=sixY (localM i) (localU i) (localV i) j := by
  have hc := c.reduction_data_of_congruent i hm hu hv hm' hu' hv' j
  have hb := baseC0_section_residues i j
  exact ⟨hc.1, hc.2.1, hc.2.2.1.trans hb.1, hc.2.2.2.trans hb.2⟩

end Z2Z4Rank6
