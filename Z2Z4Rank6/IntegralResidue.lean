module

public import Z2Z4Rank6.Residue

@[expose] public section

/-!
# The ring of rational numbers integral at a prime

The rational reduction arithmetic used in Proposition 6.2 of Manvir Jaswal,
*Infinitely many elliptic curves with torsion Z/2Z × Z/4Z and rank at least six*,
DOI 10.5281/zenodo.23437117. Reduction is a ring homomorphism on this
subring; an integral rational number with nonzero residue has an integral inverse.
-/

namespace Z2Z4Rank6

variable (p : ℕ) [Fact p.Prime]

/-- The subring of rational numbers whose denominators are prime to p. -/
def IntegralRationals : Subring ℚ where
  carrier := IntegralAt p
  zero_mem' := integralAt_zero
  one_mem' := integralAt_one
  add_mem' := IntegralAt.add
  mul_mem' := IntegralAt.mul
  neg_mem' := IntegralAt.neg

/-- Reduction modulo p on rational numbers integral at p. -/
def residueHom : IntegralRationals p →+* ZMod p where
  toFun q := residue p q
  map_zero' := residue_zero
  map_one' := residue_one
  map_add' q r := residue_add q.property r.property
  map_mul' q r := residue_mul q.property r.property

@[simp] theorem residueHom_apply (q : IntegralRationals p) : residueHom p q=residue p q := rfl

variable {p}

theorem ne_zero_of_residue_ne_zero {q : ℚ} (h : residue p q ≠ 0) : q ≠ 0 := by
  rintro rfl
  exact h residue_zero

private theorem natAbs_cast_ne_zero (z : ℤ) (hz : (z : ZMod p) ≠ 0) :
    (z.natAbs : ZMod p) ≠ 0 := by
  cases z with
  | ofNat n => simpa using hz
  | negSucc n =>
    intro hn
    apply hz
    have hn' : (n : ZMod p)+1=0 := by simpa using hn
    push_cast
    linear_combination -hn'

/-- An integral rational number is a unit at p when its residue is nonzero. -/
theorem IntegralAt.inv {q : ℚ} (_hq : IntegralAt p q) (h : residue p q ≠ 0) :
    IntegralAt p q⁻¹ := by
  have hq0 := ne_zero_of_residue_ne_zero h
  have hnum : (q.num : ZMod p) ≠ 0 := by
    intro hn
    apply h
    simp [residue, hn]
  unfold IntegralAt
  rw [Rat.den_inv_of_ne_zero hq0]
  exact natAbs_cast_ne_zero _ hnum

theorem residue_inv {q : ℚ} (hq : IntegralAt p q) (h : residue p q ≠ 0) :
    residue p q⁻¹=(residue p q)⁻¹ := by
  have hq0 := ne_zero_of_residue_ne_zero h
  have hinv := hq.inv h
  have he := residue_mul hq hinv
  rw [mul_inv_cancel₀ hq0, residue_one] at he
  apply (mul_left_cancel₀ h)
  rw [← he, mul_inv_cancel₀ h]

theorem IntegralAt.div {q r : ℚ} (hq : IntegralAt p q) (hr : IntegralAt p r)
    (h : residue p r ≠ 0) : IntegralAt p (q/r) := by
  simpa only [div_eq_mul_inv] using hq.mul (hr.inv h)

theorem residue_div {q r : ℚ} (hq : IntegralAt p q) (hr : IntegralAt p r)
    (h : residue p r ≠ 0) : residue p (q/r)=residue p q/residue p r := by
  rw [div_eq_mul_inv, residue_mul hq (hr.inv h), residue_inv hr h, div_eq_mul_inv]

/-- Solving an integral equation with a unit denominator gives an integral quotient. -/
theorem integralAt_of_mul_eq {D N x : ℚ} (hD : IntegralAt p D) (hN : IntegralAt p N)
    (hunit : residue p D ≠ 0) (h : D*x=N) : IntegralAt p x := by
  have hD0 := ne_zero_of_residue_ne_zero hunit
  have hx : x=N/D := by apply (eq_div_iff hD0).2; simpa [mul_comm] using h
  rw [hx]
  exact hN.div hD hunit

theorem residue_of_mul_eq {D N x : ℚ} (hD : IntegralAt p D) (hN : IntegralAt p N)
    (hunit : residue p D ≠ 0) (h : D*x=N) : residue p x=residue p N/residue p D := by
  have hD0 := ne_zero_of_residue_ne_zero hunit
  have hx : x=N/D := by apply (eq_div_iff hD0).2; simpa [mul_comm] using h
  rw [hx, residue_div hN hD hunit]

end Z2Z4Rank6
