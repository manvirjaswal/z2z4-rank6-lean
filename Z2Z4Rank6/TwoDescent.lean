import Z2Z4Rank6.Basic
import Mathlib.Algebra.Group.Subgroup.Even
import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.CharP.Two
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic

/-!
# Rational squareclasses and complete two-descent

The squareclasses used in Proposition 2.3 of Manvir Jaswal,
"Infinitely many elliptic curves with torsion Z/2Z × Z/4Z and rank at least six",
DOI: 10.5281/zenodo.23437117.

The theorem below is the homomorphism/kernel part of
J. H. Silverman, *The Arithmetic of Elliptic Curves*, 2nd ed., Springer (2009),
Proposition X.1.4, p. 315, followed by inclusion of K(S,2) into the full
squareclass group. The image refinement at places outside S and the solubility
criterion are unused here. All squareclass values for this paper are proved
separately from explicit rational square factors.
-/

namespace Z2Z4Rank6

/-- The rational multiplicative squareclass group. -/
abbrev RatSquareClass := ℚˣ ⧸ Subgroup.square ℚˣ

/-- The same group in additive notation, for linear algebra over F₂. -/
abbrev RatSquareClassAdd := Additive RatSquareClass

private theorem squareClass_two_nsmul (q : RatSquareClassAdd) : (2 : ℕ) • q = 0 := by
  change q.toMul ^ 2 = (1 : RatSquareClass)
  induction q.toMul using QuotientGroup.induction_on with
  | H u =>
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_square]
      exact ⟨u, pow_two u⟩

instance : Module (ZMod 2) RatSquareClassAdd :=
  AddCommGroup.zmodModule squareClass_two_nsmul

/-- The squareclass of a nonzero rational; the unused value at zero is set to zero. -/
noncomputable def squareClass (q : ℚ) : RatSquareClassAdd :=
  if hq : q = 0 then 0 else Additive.ofMul (QuotientGroup.mk (Units.mk0 q hq))

theorem squareClass_of_nonzero (q : ℚ) (hq : q ≠ 0) :
    squareClass q = Additive.ofMul (QuotientGroup.mk (Units.mk0 q hq)) := by
  simp only [squareClass, dite_eq_right hq]

/-- An explicit rational square factor certifies equality of squareclasses. -/
theorem squareClass_eq_of_factor (q r s : ℚ) (hq : q ≠ 0) (hr : r ≠ 0) (hs : s ≠ 0)
    (heq : q = r * s ^ 2) : squareClass q = squareClass r := by
  rw [squareClass_of_nonzero q hq, squareClass_of_nonzero r hr]
  change (QuotientGroup.mk (Units.mk0 q hq) : RatSquareClass) =
    QuotientGroup.mk (Units.mk0 r hr)
  rw [QuotientGroup.eq_iff_div_mem, Subgroup.mem_square]
  refine ⟨Units.mk0 s hs, ?_⟩
  apply Units.ext
  change q / r = s * s
  rw [heq]
  field_simp

theorem squareClass_one : squareClass (1 : ℚ) = 0 := by
  rw [squareClass_of_nonzero 1 (by norm_num)]
  have hu : Units.mk0 (1 : ℚ) (by norm_num) = 1 := by ext; rfl
  rw [hu]
  rfl

theorem squareClass_mul (q r : ℚ) (hq : q ≠ 0) (hr : r ≠ 0) :
    squareClass (q * r) = squareClass q + squareClass r := by
  rw [squareClass_of_nonzero _ (mul_ne_zero hq hr),
    squareClass_of_nonzero q hq, squareClass_of_nonzero r hr]
  have hu : Units.mk0 (q * r) (mul_ne_zero hq hr) = Units.mk0 q hq * Units.mk0 r hr := by
    ext
    rfl
  rw [hu, QuotientGroup.mk_mul]
  rfl

theorem squareClass_pow (q : ℚ) (n : ℕ) (hq : q ≠ 0) :
    squareClass (q ^ n) = n • squareClass q := by
  induction n with
  | zero => simp only [pow_zero, squareClass_one, zero_nsmul]
  | succ n hn =>
      rw [pow_succ, squareClass_mul _ _ (pow_ne_zero _ hq) hq, hn, succ_nsmul]

theorem squareClass_eq_zero_of_isSquare {q : ℚ} (hq : IsSquare q) : squareClass q = 0 := by
  by_cases hq0 : q = 0
  · subst q
    simp [squareClass]
  obtain ⟨r, hr⟩ := hq
  have hr0 : r ≠ 0 := by intro hh; exact hq0 (by rw [hr, hh, mul_zero])
  rw [squareClass_eq_of_factor q 1 r hq0 (by norm_num) hr0 (by simpa only [one_mul, pow_two] using hr)]
  exact squareClass_one

private def unitValuationModTwo (p : ℕ) [Fact p.Prime] : ℚˣ →* Multiplicative (ZMod 2) where
  toFun u := Multiplicative.ofAdd (padicValRat p (u : ℚ) : ZMod 2)
  map_one' := by
    simp only [Units.val_one, padicValRat.one, Int.cast_zero]
    rfl
  map_mul' u v := by
    change ((padicValRat p ((u : ℚ) * (v : ℚ)) : ℤ) : ZMod 2) =
      (padicValRat p (u : ℚ) : ZMod 2) + (padicValRat p (v : ℚ) : ZMod 2)
    rw [padicValRat.mul (Units.ne_zero u) (Units.ne_zero v), Int.cast_add]

private theorem squares_in_unitValuationModTwo_ker (p : ℕ) [Fact p.Prime] :
    Subgroup.square ℚˣ ≤ (unitValuationModTwo p).ker := by
  intro u hu
  obtain ⟨v, hv⟩ := (Subgroup.mem_square.mp hu)
  rw [hv]
  change ((padicValRat p ((v : ℚ) * (v : ℚ)) : ℤ) : ZMod 2) = 0
  rw [padicValRat.mul (Units.ne_zero v) (Units.ne_zero v), Int.cast_add]
  exact CharTwo.add_self_eq_zero _

/-- The parity of a prime valuation is a well-defined additive squareclass invariant. -/
noncomputable def squareClassValuation (p : ℕ) [Fact p.Prime] : RatSquareClassAdd →+ ZMod 2 where
  toFun q := Multiplicative.toAdd ((QuotientGroup.lift (Subgroup.square ℚˣ)
    (unitValuationModTwo p) (squares_in_unitValuationModTwo_ker p)) q.toMul)
  map_zero' := by
    change Multiplicative.toAdd ((QuotientGroup.lift _ _ _) 1) = 0
    rw [map_one]
    rfl
  map_add' q r := by
    change Multiplicative.toAdd ((QuotientGroup.lift _ _ _) (q.toMul * r.toMul)) = _
    rw [map_mul]
    rfl

theorem squareClassValuation_apply (p : ℕ) [Fact p.Prime] (q : ℚ) (hq : q ≠ 0) :
    squareClassValuation p (squareClass q) = (padicValRat p q : ZMod 2) := by
  rw [squareClass_of_nonzero q hq]
  rfl

private def unitSignModTwo : ℚˣ →* Multiplicative (ZMod 2) where
  toFun u := Multiplicative.ofAdd (if (u : ℚ) < 0 then 1 else 0)
  map_one' := by simp
  map_mul' u v := by
    change (if (u : ℚ) * (v : ℚ) < 0 then (1 : ZMod 2) else 0) =
      (if (u : ℚ) < 0 then 1 else 0) + (if (v : ℚ) < 0 then 1 else 0)
    rcases lt_or_gt_of_ne (Units.ne_zero u) with hu | hu <;>
      rcases lt_or_gt_of_ne (Units.ne_zero v) with hv | hv
    · have hprod := mul_pos_of_neg_of_neg hu hv
      simp only [ite_eq_right (not_lt_of_ge hprod.le), ite_eq_left hu, ite_eq_left hv]
      decide
    · have hprod := mul_neg_of_neg_of_pos hu hv
      norm_num [hu, hv.not_gt, hprod]
    · have hprod := mul_neg_of_pos_of_neg hu hv
      norm_num [hu.not_gt, hv, hprod]
    · have hprod := mul_pos hu hv
      norm_num [hu.not_gt, hv.not_gt, not_lt_of_ge hprod.le]

private theorem squares_in_unitSignModTwo_ker : Subgroup.square ℚˣ ≤ unitSignModTwo.ker := by
  intro u hu
  obtain ⟨v, hv⟩ := (Subgroup.mem_square.mp hu)
  rw [hv]
  change (if (v : ℚ) * (v : ℚ) < 0 then (1 : ZMod 2) else 0) = 0
  rw [ite_eq_right (not_lt_of_ge (mul_self_nonneg _))]

/-- Sign parity on rational squareclasses: negative representatives
map to one and positive representatives map to zero. -/
noncomputable def squareClassSign : RatSquareClassAdd →+ ZMod 2 where
  toFun q := Multiplicative.toAdd ((QuotientGroup.lift (Subgroup.square ℚˣ)
    unitSignModTwo squares_in_unitSignModTwo_ker) q.toMul)
  map_zero' := by
    change Multiplicative.toAdd ((QuotientGroup.lift _ _ _) 1) = 0
    rw [map_one]
    rfl
  map_add' q r := by
    change Multiplicative.toAdd ((QuotientGroup.lift _ _ _) (q.toMul * r.toMul)) = _
    rw [map_mul]
    rfl

theorem squareClassSign_apply (q : ℚ) (hq : q ≠ 0) :
    squareClassSign (squareClass q) = if q < 0 then 1 else 0 := by
  rw [squareClass_of_nonzero q hq]
  rfl

/-- A split cubic in the usual Weierstrass form. -/
def splitWeierstrass (e₁ e₂ e₃ : ℚ) : WeierstrassCurve ℚ where
  a₁ := 0
  a₂ := -(e₁ + e₂ + e₃)
  a₃ := 0
  a₄ := e₁ * e₂ + e₁ * e₃ + e₂ * e₃
  a₆ := -(e₁ * e₂ * e₃)

/-- The coordinate formula of Silverman X.1.4, including its printed special
values at the identity and the first two points of order two. -/
noncomputable def completeDescentCoordinates (W : WeierstrassCurve ℚ) (e₁ e₂ e₃ : ℚ) :
    RationalPoints W → RatSquareClassAdd × RatSquareClassAdd
  | .zero => (0, 0)
  | .some x _ _ =>
      if x = e₁ then (squareClass ((e₁ - e₃) / (e₁ - e₂)), squareClass (e₁ - e₂))
      else if x = e₂ then (squareClass (e₂ - e₁), squareClass ((e₂ - e₃) / (e₂ - e₁)))
      else (squareClass (x - e₁), squareClass (x - e₂))

/-- The full-squareclass homomorphism and kernel
conclusion of Silverman X.1.4, p. 315, over Q. It is stated for every smooth
split Weierstrass equation, with all coordinate cases explicit. -/
def CompleteTwoDescentTheorem : Prop :=
  ∀ (W : WeierstrassCurve ℚ) (e₁ e₂ e₃ : ℚ), GoodCurve W →
    W = splitWeierstrass e₁ e₂ e₃ →
    ∃ κ : RationalPoints W →+ (RatSquareClassAdd × RatSquareClassAdd),
      (∀ P, κ P = completeDescentCoordinates W e₁ e₂ e₃ P) ∧
      ∀ P, κ P = 0 ↔ ∃ Q : RationalPoints W, (2 : ℕ) • Q = P

theorem E_eq_splitWeierstrass (α β : ℚ) :
    E α β = splitWeierstrass 0 (-(α ^ 2)) (-(β ^ 2)) := by
  ext <;> simp only [E, splitWeierstrass] <;> ring

/-- Integral descent: divisibility of every torsion-valued relation by a fixed
integer p>1 forces all such relations to be trivial. -/
theorem coefficients_zero_of_torsion_divisibility_at
    {ι G : Type*} [Fintype ι] [AddCommGroup G] (p : ℕ) (hp : 1 < p) (P : ι → G)
    (hdiv : ∀ a : ι → ℤ, IsOfFinAddOrder (∑ i, a i • P i) → ∀ j, (p : ℤ) ∣ a j)
    (n : ι → ℤ) (ht : IsOfFinAddOrder (∑ i, n i • P i)) : ∀ i, n i = 0 := by
  classical
  intro i
  have aux : ∀ k : ℕ, ∀ a : ι → ℤ, (a i).natAbs = k →
      IsOfFinAddOrder (∑ j, a j • P j) → a i = 0 := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro a hak ha
      by_cases hai : a i = 0
      · exact hai
      let b : ι → ℤ := fun j => a j / (p : ℤ)
      have hb : ∀ j, (p : ℤ) * b j = a j := fun j => Int.mul_ediv_cancel' (hdiv a ha j)
      have heq : p • (∑ j, b j • P j) = ∑ j, a j • P j := by
        rw [Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro j _
        rw [← Nat.cast_smul_eq_nsmul ℤ, smul_smul, hb]
      have hbt : IsOfFinAddOrder (∑ j, b j • P j) :=
        (heq ▸ ha).of_nsmul (by omega : p ≠ 0)
      have hlt : (b i).natAbs < k := by
        rw [← hak]
        change (a i / (p : ℤ)).natAbs < (a i).natAbs
        rw [Int.natAbs_ediv_of_dvd (hdiv a ha i), Int.natAbs_natCast]
        exact Nat.div_lt_self (Int.natAbs_pos.mpr hai) hp
      have hbi : b i = 0 := ih (b i).natAbs hlt b rfl hbt
      simpa only [hbi, mul_zero] using (hb i).symm
  exact aux (n i).natAbs n rfl ht

end Z2Z4Rank6
