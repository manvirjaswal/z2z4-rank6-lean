import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Reduction of integral rational numbers

The rational residue operations used in Proposition 6.2 of Manvir Jaswal,
*Infinitely many elliptic curves with torsion Z/2Z × Z/4Z and rank at least six*,
DOI 10.5281/zenodo.23437117. A rational number is integral at a prime
when its reduced denominator is nonzero modulo that prime.
-/

namespace Z2Z4Rank6

/-- A rational number has denominator prime to p. -/
def IntegralAt (p : ℕ) (q : ℚ) : Prop := (q.den : ZMod p) ≠ 0

/-- Reduction of a rational number; used as a ring operation only on integral
arguments. -/
def residue (p : ℕ) [Fact p.Prime] (q : ℚ) : ZMod p :=
  (q.num : ZMod p) / (q.den : ZMod p)

section Prime

variable {p : ℕ} [Fact p.Prime]

private theorem natCast_ne_zero_of_dvd {d n : ℕ} (h : d ∣ n)
    (hn : (n : ZMod p) ≠ 0) : (d : ZMod p) ≠ 0 := by
  rintro hd
  obtain ⟨k,rfl⟩ := h
  simp [hd] at hn

@[simp] theorem integralAt_intCast (n : ℤ) : IntegralAt p (n : ℚ) := by
  simp [IntegralAt]

@[simp] theorem integralAt_natCast (n : ℕ) : IntegralAt p (n : ℚ) := by
  simp [IntegralAt]

@[simp] theorem integralAt_zero : IntegralAt p 0 := by simp [IntegralAt]

@[simp] theorem integralAt_one : IntegralAt p 1 := by simp [IntegralAt]

theorem IntegralAt.add {q r : ℚ} (hq : IntegralAt p q) (hr : IntegralAt p r) :
    IntegralAt p (q+r) := by
  exact natCast_ne_zero_of_dvd (Rat.add_den_dvd q r)
    (by simpa using mul_ne_zero hq hr)

theorem IntegralAt.mul {q r : ℚ} (hq : IntegralAt p q) (hr : IntegralAt p r) :
    IntegralAt p (q*r) := by
  exact natCast_ne_zero_of_dvd (Rat.mul_den_dvd q r)
    (by simpa using mul_ne_zero hq hr)

omit [Fact p.Prime] in
theorem IntegralAt.neg {q : ℚ} (hq : IntegralAt p q) : IntegralAt p (-q) := by
  simpa [IntegralAt] using hq

theorem IntegralAt.sub {q r : ℚ} (hq : IntegralAt p q) (hr : IntegralAt p r) :
    IntegralAt p (q-r) := by simpa [sub_eq_add_neg] using hq.add hr.neg

theorem IntegralAt.pow {q : ℚ} (hq : IntegralAt p q) (n : ℕ) : IntegralAt p (q^n) := by
  induction n with
  | zero => simp
  | succ n ih => simpa [pow_succ] using ih.mul hq

@[simp] theorem residue_intCast (n : ℤ) : residue p (n : ℚ) = (n : ZMod p) := by
  simp [residue]

@[simp] theorem residue_natCast (n : ℕ) : residue p (n : ℚ) = (n : ZMod p) := by
  simp [residue]

@[simp] theorem residue_zero : residue p 0 = 0 := by simp [residue]

@[simp] theorem residue_one : residue p 1 = 1 := by simp [residue]

theorem residue_add {q r : ℚ} (hq : IntegralAt p q) (hr : IntegralAt p r) :
    residue p (q+r) = residue p q + residue p r := by
  have hqr := hq.add hr
  have he : ((q+r).num : ZMod p) * (q.den : ZMod p) * (r.den : ZMod p) =
      ((q.num : ZMod p)*(r.den : ZMod p)+(r.num : ZMod p)*(q.den : ZMod p))*
        ((q+r).den : ZMod p) := by
    have he := congrArg (fun z : ℤ => (z : ZMod p)) (Rat.add_num_den' q r)
    push_cast at he
    exact he
  unfold residue
  dsimp [IntegralAt] at hq hr hqr
  field_simp [hq, hr, hqr]
  linear_combination he

theorem residue_mul {q r : ℚ} (hq : IntegralAt p q) (hr : IntegralAt p r) :
    residue p (q*r) = residue p q * residue p r := by
  have hqr := hq.mul hr
  have he : ((q*r).num : ZMod p) * (q.den : ZMod p) * (r.den : ZMod p) =
      ((q.num : ZMod p)*(r.num : ZMod p))*((q*r).den : ZMod p) := by
    have he := congrArg (fun z : ℤ => (z : ZMod p)) (Rat.mul_num_den' q r)
    push_cast at he
    exact he
  unfold residue
  dsimp [IntegralAt] at hq hr hqr
  field_simp [hq, hr, hqr]
  linear_combination he

theorem residue_neg (q : ℚ) : residue p (-q) = -residue p q := by
  simp [residue, neg_div]

theorem residue_sub {q r : ℚ} (hq : IntegralAt p q) (hr : IntegralAt p r) :
    residue p (q-r) = residue p q - residue p r := by
  rw [sub_eq_add_neg, residue_add hq hr.neg, residue_neg, sub_eq_add_neg]

theorem residue_pow {q : ℚ} (hq : IntegralAt p q) (n : ℕ) :
    residue p (q^n) = (residue p q)^n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, residue_mul (hq.pow n) hq, ih, pow_succ]

end Prime

end Z2Z4Rank6
