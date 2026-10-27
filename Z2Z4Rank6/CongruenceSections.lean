module

public import Z2Z4Rank6.Twists
public import Z2Z4Rank6.IntegralResidue
public import Z2Z4Rank6.ReductionTheory

@[expose] public section

/-!
# A common denominator for the six sections

The coordinate regularity calculation used in Proposition 6.2 of Manvir
Jaswal, *Infinitely many elliptic curves with torsion Z/2Z × Z/4Z and rank at
least six*, DOI 10.5281/zenodo.23437117. The closed forms agree with
the deposited `paper-data/pd_sec6c.gp`. The numerator vectors use only integer
coefficients, so their values commute with reduction at every prime.
-/

namespace Z2Z4Rank6

section Ring

variable {R : Type*} [CommRing R]

/-- The denominator `25m³(3m²+242)²` from the coordinate regularity check. -/
def sectionDenominator (m : R) : R := 25*m^3*(3*m^2+242)^2

/-- Polynomial numerators of the six abscissae after multiplication by the common denominator. -/
def sectionXNumerator (m : R) : Fin 6 → R :=
  ![sectionDenominator m*p1x m,
    sectionDenominator m*p2x m,
    sectionDenominator m*p3x m,
    245*m^3*(3*m^2+242)^2*(m^2-1)*(m^2-81)*(m^2-121)^2*(2*m^2+243),
    245*m*(3*m^2+242)^3*(m^2-9801)*(m^2-121)*(m^2-81)^2,
    1225*m^3*(3*m^2+242)*(m^2-9801)*(m^2-1)*(m^2-121)^2*(2*m^2+243)]

/-- Polynomial numerators of the six ordinates, with the printed signs. -/
def sectionYNumerator (m u v : R) : Fin 6 → R :=
  ![sectionDenominator m*p1y m,
    sectionDenominator m*p2y m,
    sectionDenominator m*p3y m,
    -686*m^3*(3*m^2+242)^2*(m^2-1)*(m^2-36)*(m^2-81)*(m^2-121)^2*twistN (m^2)*v,
    -686*(3*m^2+242)^2*(m^2-9801)*(m^2-121)*(4*m^2-1089)*(m^2-81)^2*twistN (m^2)*u,
    -8575*m^3*(m^2-9801)*(m^2-1)*(m^2-99)*(m^2-121)^2*twistN (m^2)*u*v]

end Ring

section RingHom

variable {R S : Type*} [CommRing R] [CommRing S]

theorem map_a (f : R →+* S) (m : R) : f (a m)=a (f m) := by
  simp [a, map_ofNat]

theorem map_b (f : R →+* S) (m : R) : f (b m)=b (f m) := by
  simp [b, map_ofNat]

/-- The common denominator has integer coefficients. -/
theorem map_sectionDenominator (f : R →+* S) (m : R) :
    f (sectionDenominator m)=sectionDenominator (f m) := by
  simp [sectionDenominator, map_ofNat]

/-- Abscissa numerators commute with any ring homomorphism. -/
theorem map_sectionXNumerator (f : R →+* S) (m : R) (i : Fin 6) :
    f (sectionXNumerator m i)=sectionXNumerator (f m) i := by
  fin_cases i <;> simp [sectionXNumerator, sectionDenominator, p1x, p2x, p3x, map_ofNat]

/-- Ordinate numerators commute with any ring homomorphism. -/
theorem map_sectionYNumerator (f : R →+* S) (m u v : R) (i : Fin 6) :
    f (sectionYNumerator m u v i)=sectionYNumerator (f m) (f u) (f v) i := by
  fin_cases i <;> simp [sectionYNumerator, sectionDenominator, p1y, p2y, p3y, twistN, map_ofNat]

end RingHom

section Field

variable {K : Type*} [Field K] [CharZero K]

/-- The common denominator clears all six abscissae. -/
theorem denominator_mul_sixX (m : K) (hm : m ≠ 0) (_hA : 3*m^2+242 ≠ 0) (i : Fin 6) :
    sectionDenominator m*sixX m i=sectionXNumerator m i := by
  fin_cases i
  · rfl
  · rfl
  · rfl
  · change sectionDenominator m*p4x m= _
    rw [p4x_formula]
    dsimp [sectionDenominator, sectionXNumerator]
    field_simp
    ring
  · change sectionDenominator m*p5x m= _
    rw [p5x_formula]
    dsimp [sectionDenominator, sectionXNumerator]
    field_simp [hm]
    ring
  · change sectionDenominator m*p6x m= _
    rw [p6x_formula]
    dsimp [sectionDenominator, sectionXNumerator]
    field_simp
    ring

/-- The common denominator clears all six ordinates on C. -/
theorem denominator_mul_sixY (m u v : K) (hu : u^2=q1 (m^2)) (hv : v^2=q2 (m^2))
    (hm : m ≠ 0) (hu0 : u ≠ 0) (hv0 : v ≠ 0)
    (hA : 3*m^2+242 ≠ 0) (hB : 2*m^2+243 ≠ 0) (i : Fin 6) :
    sectionDenominator m*sixY m u v i=sectionYNumerator m u v i := by
  fin_cases i
  · rfl
  · rfl
  · rfl
  · change sectionDenominator m*p4y m v= _
    rw [p4y_formula m v hv hv0 hB]
    dsimp [sectionDenominator, sectionYNumerator]
    field_simp
  · change sectionDenominator m*p5y m u= _
    rw [p5y_formula m u hu hm hu0 hA]
    dsimp [sectionDenominator, sectionYNumerator]
    field_simp [hm]
  · change sectionDenominator m*p6y m u v= _
    rw [p6y_formula m u v hu hv hu0 hv0 hB hA]
    dsimp [sectionDenominator, sectionYNumerator]
    let B := -343*(m^2-9801)*(m^2-1)*(m^2-99)*(m^2-121)^2*twistN (m^2)*u*v
    calc
      _ = (25*m^3*B)*((3*m^2+242)^2/(3*m^2+242)^2) := by dsimp [B]; ring
      _ = 25*m^3*B := by rw [div_self (pow_ne_zero 2 hA), mul_one]
      _ = _ := by dsimp [B]; ring

theorem sectionDenominator_ne_zero (m : K) (hm : m ≠ 0) (hA : 3*m^2+242 ≠ 0) :
    sectionDenominator m ≠ 0 := by
  exact mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hm)) (pow_ne_zero _ hA)

end Field

section RationalReduction

variable {p : ℕ} [Fact p.Prime]

theorem a_integral {m : ℚ} (hm : IntegralAt p m) : IntegralAt p (a m) := by
  let M : IntegralRationals p := ⟨m, hm⟩
  have h := (a M).property
  change IntegralAt p ((IntegralRationals p).subtype (a M)) at h
  rwa [map_a] at h

theorem b_integral {m : ℚ} (hm : IntegralAt p m) : IntegralAt p (b m) := by
  let M : IntegralRationals p := ⟨m, hm⟩
  have h := (b M).property
  change IntegralAt p ((IntegralRationals p).subtype (b M)) at h
  rwa [map_b] at h

theorem residue_a {m : ℚ} (hm : IntegralAt p m) : residue p (a m)=a (residue p m) := by
  let M : IntegralRationals p := ⟨m, hm⟩
  have h := map_a (residueHom p) M
  change residue p ((IntegralRationals p).subtype (a M))=_ at h
  rwa [map_a] at h

theorem residue_b {m : ℚ} (hm : IntegralAt p m) : residue p (b m)=b (residue p m) := by
  let M : IntegralRationals p := ⟨m, hm⟩
  have h := map_b (residueHom p) M
  change residue p ((IntegralRationals p).subtype (b M))=_ at h
  rwa [map_b] at h

/-- Integrality of the product that detects singular fibers. -/
theorem fiber_product_integral {m : ℚ} (hm : IntegralAt p m) :
    IntegralAt p (a m*b m*((a m)^2-(b m)^2)) :=
  ((a_integral hm).mul (b_integral hm)).mul (((a_integral hm).pow 2).sub ((b_integral hm).pow 2))

/-- Reduction of the product that detects singular fibers. -/
theorem residue_fiber_product {m : ℚ} (hm : IntegralAt p m) :
    residue p (a m*b m*((a m)^2-(b m)^2)) =
      a (residue p m)*b (residue p m)*((a (residue p m))^2-(b (residue p m))^2) := by
  rw [residue_mul ((a_integral hm).mul (b_integral hm))
      (((a_integral hm).pow 2).sub ((b_integral hm).pow 2)),
    residue_mul (a_integral hm) (b_integral hm),
    residue_sub ((a_integral hm).pow 2) ((b_integral hm).pow 2),
    residue_pow (a_integral hm), residue_pow (b_integral hm), residue_a hm, residue_b hm]

/-- The polynomial family gives an integral Weierstrass model at an integral parameter. -/
theorem X_integralModel {m : ℚ} (hm : IntegralAt p m) : IntegralModelAt p (X m) := by
  refine ⟨integralAt_zero, ?_, integralAt_zero, ?_, integralAt_zero⟩
  · exact ((a_integral hm).pow 2).add ((b_integral hm).pow 2)
  · exact ((a_integral hm).pow 2).mul ((b_integral hm).pow 2)

/-- The family commutes with reduction of an integral parameter. -/
theorem reducedModel_X {m : ℚ} (hm : IntegralAt p m) :
    reducedModel p (X m)=X (residue p m) := by
  ext
  · exact residue_zero
  · change residue p ((a m)^2+(b m)^2)=(a (residue p m))^2+(b (residue p m))^2
    rw [residue_add ((a_integral hm).pow 2) ((b_integral hm).pow 2),
      residue_pow (a_integral hm), residue_pow (b_integral hm), residue_a hm, residue_b hm]
  · exact residue_zero
  · change residue p ((a m)^2*(b m)^2)=(a (residue p m))^2*(b (residue p m))^2
    rw [residue_mul ((a_integral hm).pow 2) ((b_integral hm).pow 2),
      residue_pow (a_integral hm), residue_pow (b_integral hm), residue_a hm, residue_b hm]
  · exact residue_zero

theorem sectionDenominator_integral {m : ℚ} (hm : IntegralAt p m) :
    IntegralAt p (sectionDenominator m) := by
  let M : IntegralRationals p := ⟨m, hm⟩
  have h := (sectionDenominator M).property
  change IntegralAt p ((IntegralRationals p).subtype (sectionDenominator M)) at h
  rwa [map_sectionDenominator] at h

theorem sectionXNumerator_integral {m : ℚ} (hm : IntegralAt p m) (i : Fin 6) :
    IntegralAt p (sectionXNumerator m i) := by
  let M : IntegralRationals p := ⟨m, hm⟩
  have h := (sectionXNumerator M i).property
  change IntegralAt p ((IntegralRationals p).subtype (sectionXNumerator M i)) at h
  rwa [map_sectionXNumerator] at h

theorem sectionYNumerator_integral {m u v : ℚ}
    (hm : IntegralAt p m) (hu : IntegralAt p u) (hv : IntegralAt p v) (i : Fin 6) :
    IntegralAt p (sectionYNumerator m u v i) := by
  let M : IntegralRationals p := ⟨m, hm⟩
  let U : IntegralRationals p := ⟨u, hu⟩
  let V : IntegralRationals p := ⟨v, hv⟩
  have h := (sectionYNumerator M U V i).property
  change IntegralAt p ((IntegralRationals p).subtype (sectionYNumerator M U V i)) at h
  rwa [map_sectionYNumerator] at h

theorem residue_sectionDenominator {m : ℚ} (hm : IntegralAt p m) :
    residue p (sectionDenominator m)=sectionDenominator (residue p m) := by
  let M : IntegralRationals p := ⟨m, hm⟩
  have h := map_sectionDenominator (residueHom p) M
  change residue p ((IntegralRationals p).subtype (sectionDenominator M))=_ at h
  rwa [map_sectionDenominator] at h

theorem residue_sectionXNumerator {m : ℚ} (hm : IntegralAt p m) (i : Fin 6) :
    residue p (sectionXNumerator m i)=sectionXNumerator (residue p m) i := by
  let M : IntegralRationals p := ⟨m, hm⟩
  have h := map_sectionXNumerator (residueHom p) M i
  change residue p ((IntegralRationals p).subtype (sectionXNumerator M i))=_ at h
  rwa [map_sectionXNumerator] at h

theorem residue_sectionYNumerator {m u v : ℚ}
    (hm : IntegralAt p m) (hu : IntegralAt p u) (hv : IntegralAt p v) (i : Fin 6) :
    residue p (sectionYNumerator m u v i)=
      sectionYNumerator (residue p m) (residue p u) (residue p v) i := by
  let M : IntegralRationals p := ⟨m, hm⟩
  let U : IntegralRationals p := ⟨u, hu⟩
  let V : IntegralRationals p := ⟨v, hv⟩
  have h := map_sectionYNumerator (residueHom p) M U V i
  change residue p ((IntegralRationals p).subtype (sectionYNumerator M U V i))=_ at h
  rwa [map_sectionYNumerator] at h

/-- Every abscissa is integral whenever the common denominator is a unit. -/
theorem sixX_integral {m : ℚ} (hm : IntegralAt p m) (hm0 : m ≠ 0)
    (hA : 3*m^2+242 ≠ 0) (hD : residue p (sectionDenominator m) ≠ 0) (i : Fin 6) :
    IntegralAt p (sixX m i) :=
  integralAt_of_mul_eq (sectionDenominator_integral hm) (sectionXNumerator_integral hm i)
    hD (denominator_mul_sixX m hm0 hA i)

/-- Every ordinate is integral whenever the common denominator is a unit. -/
theorem sixY_integral {m u v : ℚ}
    (hm : IntegralAt p m) (hu : IntegralAt p u) (hv : IntegralAt p v)
    (hueq : u^2=q1 (m^2)) (hveq : v^2=q2 (m^2))
    (hm0 : m ≠ 0) (hu0 : u ≠ 0) (hv0 : v ≠ 0)
    (hA : 3*m^2+242 ≠ 0) (hB : 2*m^2+243 ≠ 0)
    (hD : residue p (sectionDenominator m) ≠ 0) (i : Fin 6) :
    IntegralAt p (sixY m u v i) :=
  integralAt_of_mul_eq (sectionDenominator_integral hm) (sectionYNumerator_integral hm hu hv i)
    hD (denominator_mul_sixY m u v hueq hveq hm0 hu0 hv0 hA hB i)

theorem residue_sixX {m : ℚ} (hm : IntegralAt p m) (hm0 : m ≠ 0)
    (hA : 3*m^2+242 ≠ 0) (hD : residue p (sectionDenominator m) ≠ 0) (i : Fin 6) :
    residue p (sixX m i)=sectionXNumerator (residue p m) i/sectionDenominator (residue p m) := by
  rw [residue_of_mul_eq (sectionDenominator_integral hm) (sectionXNumerator_integral hm i)
    hD (denominator_mul_sixX m hm0 hA i), residue_sectionXNumerator hm,
    residue_sectionDenominator hm]

theorem residue_sixY {m u v : ℚ}
    (hm : IntegralAt p m) (hu : IntegralAt p u) (hv : IntegralAt p v)
    (hueq : u^2=q1 (m^2)) (hveq : v^2=q2 (m^2))
    (hm0 : m ≠ 0) (hu0 : u ≠ 0) (hv0 : v ≠ 0)
    (hA : 3*m^2+242 ≠ 0) (hB : 2*m^2+243 ≠ 0)
    (hD : residue p (sectionDenominator m) ≠ 0) (i : Fin 6) :
    residue p (sixY m u v i)=sectionYNumerator (residue p m) (residue p u) (residue p v) i/
      sectionDenominator (residue p m) := by
  rw [residue_of_mul_eq (sectionDenominator_integral hm) (sectionYNumerator_integral hm hu hv i)
    hD (denominator_mul_sixY m u v hueq hveq hm0 hu0 hv0 hA hB i),
    residue_sectionYNumerator hm hu hv, residue_sectionDenominator hm]

/-- The three unit conditions in the good-reduction paragraph of Proposition 6.2. -/
theorem sectionDenominator_residue_ne_zero {m : ℚ} (hm : IntegralAt p m)
    (h5 : (5 : ZMod p) ≠ 0) (hm' : residue p m ≠ 0)
    (hA : 3*(residue p m)^2+242 ≠ 0) : residue p (sectionDenominator m) ≠ 0 := by
  rw [residue_sectionDenominator hm]
  unfold sectionDenominator
  have h25 : (25 : ZMod p) ≠ 0 := by
    convert pow_ne_zero 2 h5 using 1
    norm_num
  exact mul_ne_zero (mul_ne_zero h25 (pow_ne_zero _ hm')) (pow_ne_zero _ hA)

private theorem rational_A_ne_zero (m : ℚ) : 3*m^2+242 ≠ 0 := by
  nlinarith [sq_nonneg m]

private theorem rational_B_ne_zero (m : ℚ) : 2*m^2+243 ≠ 0 := by
  nlinarith [sq_nonneg m]

theorem CPoint.u_ne_zero (c : CPoint) : c.u ≠ 0 := by
  intro hu
  have h := c.u_sq
  rw [hu] at h
  nlinarith [sq_nonneg c.m]

theorem CPoint.v_ne_zero (c : CPoint) : c.v ≠ 0 := by
  intro hv
  have h := c.v_sq
  rw [hv] at h
  nlinarith [sq_nonneg c.m]

private theorem parameter_ne_zero_of_denominator_unit {m : ℚ}
    (hD : residue p (sectionDenominator m) ≠ 0) : m ≠ 0 := by
  intro hm
  simp [hm, sectionDenominator] at hD

/-- The six abscissae of a rational point of C are integral at a good unit denominator. -/
theorem CPoint.sixX_integral (c : CPoint) (hm : IntegralAt p c.m)
    (hD : residue p (sectionDenominator c.m) ≠ 0) (i : Fin 6) : IntegralAt p (sixX c.m i) :=
  Z2Z4Rank6.sixX_integral hm (parameter_ne_zero_of_denominator_unit hD) (rational_A_ne_zero c.m) hD i

/-- The six ordinates of a rational point of C are integral at a good unit denominator. -/
theorem CPoint.sixY_integral (c : CPoint)
    (hm : IntegralAt p c.m) (hu : IntegralAt p c.u) (hv : IntegralAt p c.v)
    (hD : residue p (sectionDenominator c.m) ≠ 0) (i : Fin 6) : IntegralAt p (sixY c.m c.u c.v i) :=
  Z2Z4Rank6.sixY_integral hm hu hv c.u_sq c.v_sq (parameter_ne_zero_of_denominator_unit hD)
    c.u_ne_zero c.v_ne_zero (rational_A_ne_zero c.m) (rational_B_ne_zero c.m) hD i

/-- Congruent affine coordinates on C give the same six reductions, as used in Proposition 6.2. -/
theorem CPoint.six_residues_eq (c d : CPoint)
    (hcm : IntegralAt p c.m) (hcu : IntegralAt p c.u) (hcv : IntegralAt p c.v)
    (hdm : IntegralAt p d.m) (hdu : IntegralAt p d.u) (hdv : IntegralAt p d.v)
    (hDc : residue p (sectionDenominator c.m) ≠ 0)
    (hm : residue p c.m=residue p d.m) (hu : residue p c.u=residue p d.u)
    (hv : residue p c.v=residue p d.v) (i : Fin 6) :
    residue p (sixX c.m i)=residue p (sixX d.m i) ∧
      residue p (sixY c.m c.u c.v i)=residue p (sixY d.m d.u d.v i) := by
  have hDd : residue p (sectionDenominator d.m) ≠ 0 := by
    rwa [residue_sectionDenominator hcm, hm, ← residue_sectionDenominator hdm] at hDc
  have hc0 := parameter_ne_zero_of_denominator_unit hDc
  have hd0 := parameter_ne_zero_of_denominator_unit hDd
  constructor
  · rw [residue_sixX hcm hc0 (rational_A_ne_zero c.m) hDc,
      residue_sixX hdm hd0 (rational_A_ne_zero d.m) hDd, hm]
  · rw [residue_sixY hcm hcu hcv c.u_sq c.v_sq hc0 c.u_ne_zero c.v_ne_zero
      (rational_A_ne_zero c.m) (rational_B_ne_zero c.m) hDc,
      residue_sixY hdm hdu hdv d.u_sq d.v_sq hd0 d.u_ne_zero d.v_ne_zero
      (rational_A_ne_zero d.m) (rational_B_ne_zero d.m) hDd, hm, hu, hv]

end RationalReduction

end Z2Z4Rank6
