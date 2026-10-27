import Mathlib.Data.Nat.Squarefree
import Mathlib.Tactic

/-!
# Exact parametrization of split two-descent supports

The support reduction used for the full two-descent certificate at m=14/3 in
Proposition 2.3 of Manvir Jaswal, "Infinitely many elliptic curves with torsion
Z/2Z × Z/4Z and rank at least six", DOI: 10.5281/zenodo.23437117.

For pairwise coprime blocks A,B,C, three squarefree signed representatives
supported on AB, AC, BC, with positive second coordinate and square product,
are exactly (εab,ac,εbc). This is a general divisor argument; it does not enumerate any
representatives.
-/

namespace Z2Z4Rank6.SplitSupport

private theorem common_block_factor_eq
    (A B C x y z a b a' c : ℕ) (hAB : A.Coprime B) (hAC : A.Coprime C)
    (ha : a ∣ A) (hb : b ∣ B) (ha' : a' ∣ A) (hc : c ∣ C)
    (hz : z ∣ B * C) (hx : x = a * b) (hy : y = a' * c)
    (hsx : Squarefree x) (hsy : Squarefree y) (hsq : IsSquare (x * y * z)) :
    a = a' := by
  have hAx : A.Coprime z := (hAB.mul_right hAC).coprime_dvd_right hz
  have haz : a.Coprime z := hAx.coprime_dvd_left ha
  have ha'z : a'.Coprime z := hAx.coprime_dvd_left ha'
  have hac : a.Coprime c := (hAC.coprime_dvd_left ha).coprime_dvd_right hc
  have ha'b : a'.Coprime b := (hAB.coprime_dvd_left ha').coprime_dvd_right hb
  have hxy : x ∣ y * z := hsx.dvd_of_isSquare_mul (by simpa only [mul_assoc] using hsq)
  have hyx : y ∣ x * z := hsy.dvd_of_isSquare_mul (by
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hsq)
  have hax : a ∣ x := by rw [hx]; exact dvd_mul_right a b
  have ha'y : a' ∣ y := by rw [hy]; exact dvd_mul_right a' c
  have hay : a ∣ y := haz.dvd_of_dvd_mul_right (hax.trans hxy)
  have ha'x : a' ∣ x := ha'z.dvd_of_dvd_mul_right (ha'y.trans hyx)
  rw [hy] at hay
  rw [hx] at ha'x
  exact Nat.dvd_antisymm (hac.dvd_of_dvd_mul_right hay) (ha'b.dvd_of_dvd_mul_right ha'x)

/-- Exact positive factorization of a squarefree support triple. The blocks
need only be pairwise coprime; their own squarefreeness is unnecessary. -/
theorem exists_nat_block_parametrization
    (A B C : ℕ) (hAB : A.Coprime B) (hAC : A.Coprime C) (hBC : B.Coprime C)
    (x y z : ℕ) (hsx : Squarefree x) (hsy : Squarefree y) (hsz : Squarefree z)
    (hdx : x ∣ A * B) (hdy : y ∣ A * C) (hdz : z ∣ B * C)
    (hsq : IsSquare (x * y * z)) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ a ∣ A ∧ b ∣ B ∧ c ∣ C ∧
      x = a * b ∧ y = a * c ∧ z = b * c := by
  obtain ⟨a, b, ha, hb, hx⟩ := exists_dvd_and_dvd_of_dvd_mul hdx
  obtain ⟨a', c, ha', hc, hy⟩ := exists_dvd_and_dvd_of_dvd_mul hdy
  obtain ⟨b', c', hb', hc', hz⟩ := exists_dvd_and_dvd_of_dvd_mul hdz
  have haa' := common_block_factor_eq A B C x y z a b a' c hAB hAC
    ha hb ha' hc hdz hx hy hsx hsy hsq
  have hbb' := common_block_factor_eq B A C x z y b a b' c' hAB.symm hBC
    hb ha hb' hc' hdy (by simpa only [mul_comm] using hx) hz hsx hsz
    (by simpa only [mul_assoc, mul_left_comm, mul_comm] using hsq)
  have hcc' := common_block_factor_eq C A B y z x c a' c' b' hAC.symm hBC.symm
    hc ha' hc' hb' hdx (by simpa only [mul_comm] using hy)
    (by simpa only [mul_comm] using hz) hsy hsz
    (by simpa only [mul_assoc, mul_left_comm, mul_comm] using hsq)
  subst a'
  subst b'
  subst c'
  have hab0 : a * b ≠ 0 := hx ▸ hsx.ne_zero
  have hac0 : a * c ≠ 0 := hy ▸ hsy.ne_zero
  exact ⟨a, b, c, Nat.pos_of_ne_zero (mul_ne_zero_iff.mp hab0).1,
    Nat.pos_of_ne_zero (mul_ne_zero_iff.mp hab0).2,
    Nat.pos_of_ne_zero (mul_ne_zero_iff.mp hac0).2, ha, hb, hc, hx, hy, hz⟩

/-- The factors supplied by the support theorem are canonical: the common
factor is the gcd, and the other two are the corresponding quotients. -/
theorem nat_block_parameters_canonical
    (B C x y a b c : ℕ) (hBC : B.Coprime C) (hb : b ∣ B) (hc : c ∣ C)
    (ha0 : 0 < a) (hx : x = a * b) (hy : y = a * c) :
    a = Nat.gcd x y ∧ b = x / a ∧ c = y / a := by
  have hbc : b.Coprime c := (hBC.coprime_dvd_left hb).coprime_dvd_right hc
  rw [hx, hy]
  constructor
  · rw [Nat.gcd_mul_left, hbc.gcd_eq_one, mul_one]
  · exact ⟨(Nat.mul_div_cancel_left b ha0).symm, (Nat.mul_div_cancel_left c ha0).symm⟩

/-- Exact signed parametrization of the canonical integer representatives.
The same sign occurs in the first and third coordinates because the second
coordinate is positive and the product is a square. -/
theorem exists_signed_block_parametrization
    (A B C : ℕ) (hAB : A.Coprime B) (hAC : A.Coprime C) (hBC : B.Coprime C)
    (d1 d2 d3 : ℤ) (hs1 : Squarefree d1) (hs2 : Squarefree d2) (hs3 : Squarefree d3)
    (hd1 : d1.natAbs ∣ A * B) (hd2 : d2.natAbs ∣ A * C) (hd3 : d3.natAbs ∣ B * C)
    (hd2pos : 0 < d2) (hsq : IsSquare (d1 * d2 * d3)) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ a ∣ A ∧ b ∣ B ∧ c ∣ C ∧
      ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
        d1 = ε * (a : ℤ) * b ∧ d2 = (a : ℤ) * c ∧ d3 = ε * (b : ℤ) * c := by
  have hsn : IsSquare (d1.natAbs * d2.natAbs * d3.natAbs) := by
    obtain ⟨t, ht⟩ := hsq
    exact ⟨t.natAbs, by simpa only [Int.natAbs_mul] using congrArg Int.natAbs ht⟩
  obtain ⟨a, b, c, ha0, hb0, hc0, ha, hb, hc, hx, hy, hz⟩ :=
    exists_nat_block_parametrization A B C hAB hAC hBC d1.natAbs d2.natAbs d3.natAbs
      (Int.squarefree_natAbs.mpr hs1) (Int.squarefree_natAbs.mpr hs2)
      (Int.squarefree_natAbs.mpr hs3) hd1 hd2 hd3 hsn
  have hprod : 0 ≤ d1 * d2 * d3 := by
    obtain ⟨t, ht⟩ := hsq
    rw [ht]
    exact mul_self_nonneg t
  have hx' : |d1| = (a : ℤ) * b := by
    simpa only [Int.natCast_natAbs, Nat.cast_mul] using congrArg (fun n : ℕ => (n : ℤ)) hx
  have hy' : |d2| = (a : ℤ) * c := by
    simpa only [Int.natCast_natAbs, Nat.cast_mul] using congrArg (fun n : ℕ => (n : ℤ)) hy
  have hz' : |d3| = (b : ℤ) * c := by
    simpa only [Int.natCast_natAbs, Nat.cast_mul] using congrArg (fun n : ℕ => (n : ℤ)) hz
  rw [abs_of_pos hd2pos] at hy'
  refine ⟨a, b, c, ha0, hb0, hc0, ha, hb, hc, ?_⟩
  by_cases h1 : 0 ≤ d1
  · have h1pos : 0 < d1 := lt_of_le_of_ne h1 (Ne.symm hs1.ne_zero)
    have h3 : 0 ≤ d3 := (mul_nonneg_iff_of_pos_left (mul_pos h1pos hd2pos)).mp hprod
    refine ⟨1, Or.inl rfl, ?_, hy', ?_⟩
    · simpa only [one_mul, abs_of_nonneg h1] using hx'
    · simpa only [one_mul, abs_of_nonneg h3] using hz'
  · have h1neg : d1 < 0 := lt_of_not_ge h1
    have h12 : d1 * d2 < 0 := mul_neg_of_neg_of_pos h1neg hd2pos
    have h3 : d3 ≤ 0 := by
      rcases mul_nonneg_iff.mp hprod with h | h
      · exact False.elim ((not_le_of_gt h12) h.1)
      · exact h.2
    rw [abs_of_neg h1neg] at hx'
    rw [abs_of_nonpos h3] at hz'
    refine ⟨-1, Or.inr rfl, ?_, hy', ?_⟩ <;> simp only [neg_one_mul] <;> linarith

end Z2Z4Rank6.SplitSupport
