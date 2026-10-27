module

public import Z2Z4Rank6.Torsion
public import Mathlib.Data.Rat.Lemmas
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.Tactic

@[expose] public section

/-!
# The 13-adic torsion condition

The valuation calculation in Proposition 6.2 of Manvir Jaswal,
"Infinitely many elliptic curves with torsion Z/2Z × Z/4Z and rank at least six",
DOI: 10.5281/zenodo.23437117. The point and factor values are printed
in Proposition 5.1 and the proof of Proposition 6.2 and deposited in
`paper-data/pd_sec6c.gp`.

Mathlib's `padicValRat` assigns zero valuation to zero; the congruence
condition below therefore includes the zero difference explicitly.
-/

namespace Z2Z4Rank6

local instance : Fact (Nat.Prime 13) := ⟨by decide⟩

/-- The paper's condition `ord₁₃(m−m₀) ≥ 2`, including `m=m₀`. -/
def Congruent13Sq (m : ℚ) : Prop :=
  m = (7401 : ℚ) / 2399 ∨ 2 ≤ padicValRat 13 (m - (7401 : ℚ) / 2399)

private theorem val_nat_230100 : padicValNat 13 230100 = 1 := by
  rw [show (230100 : ℕ) = 13 * 17700 by decide,
    padicValNat.mul (by decide) (by decide), padicValNat.self (by decide),
    padicValNat.eq_zero_of_not_dvd (by decide)]

private theorem val_nat_zero (n : ℕ) (h : ¬13 ∣ n) : padicValNat 13 n = 0 :=
  padicValNat.eq_zero_of_not_dvd h

private theorem val_base_99 : padicValRat 13 ((7401 : ℚ) / 2399 - 99) = 1 := by
  norm_num [padicValRat_def, padicValInt]
  rw [val_nat_230100, val_nat_zero 2399 (by decide)]
  norm_num

private theorem val_base_other (k : ℚ)
    (hk : k ∈ ({0, 1, -1, 9, -9, 11, -11, -99} : Finset ℚ)) :
    padicValRat 13 ((7401 : ℚ) / 2399 - k) = 0 := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    norm_num [padicValRat_def, padicValInt] <;>
    simp (disch := norm_num) only [val_nat_zero, Nat.cast_zero, sub_zero]

/-- A perturbation of strictly higher valuation preserves both nonvanishing
and the valuation of a rational number. -/
theorem rational_valuation_stable {p : ℕ} [Fact p.Prime] {c d : ℚ}
    (hc : c ≠ 0) (hd : d ≠ 0) (hval : padicValRat p c < padicValRat p d) :
    c + d ≠ 0 ∧ padicValRat p (c + d) = padicValRat p c := by
  have hsum : c + d ≠ 0 := by
    intro hsum
    have heq : d = -c := by linarith
    rw [heq, padicValRat.neg] at hval
    exact lt_irrefl _ hval
  exact ⟨hsum, padicValRat.add_eq_of_lt hsum hc hd hval⟩

theorem rational_valuation_mul {p : ℕ} [Fact p.Prime] {c d : ℚ} {r s : ℤ}
    (hc : c ≠ 0 ∧ padicValRat p c = r) (hd : d ≠ 0 ∧ padicValRat p d = s) :
    c * d ≠ 0 ∧ padicValRat p (c * d) = r + s :=
  ⟨mul_ne_zero hc.1 hd.1, by rw [padicValRat.mul hc.1 hd.1, hc.2, hd.2]⟩

private theorem linear_factor_stable (m k : ℚ) (n : ℤ)
    (hm : Congruent13Sq m) (hc : (7401 : ℚ) / 2399 - k ≠ 0)
    (hbase : padicValRat 13 ((7401 : ℚ) / 2399 - k) = n) (hn : n < 2) :
    m - k ≠ 0 ∧ padicValRat 13 (m - k) = n := by
  rcases hm with rfl | hm
  · exact ⟨hc, hbase⟩
  · have hd : m - (7401 : ℚ) / 2399 ≠ 0 := by
      intro hd
      rw [hd, padicValRat.zero] at hm
      omega
    have hs := rational_valuation_stable hc hd (p := 13) (by omega)
    have heq : (7401 : ℚ) / 2399 - k + (m - (7401 : ℚ) / 2399) = m - k := by ring
    rw [heq, hbase] at hs
    exact hs

theorem linear_factor_13_other (m k : ℚ) (hm : Congruent13Sq m)
    (hk : k ∈ ({0, 1, -1, 9, -9, 11, -11, -99} : Finset ℚ)) :
    m - k ≠ 0 ∧ padicValRat 13 (m - k) = 0 := by
  apply linear_factor_stable m k 0 hm _ (val_base_other k hk) (by norm_num)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

theorem linear_factor_13_99 (m : ℚ) (hm : Congruent13Sq m) :
    m - 99 ≠ 0 ∧ padicValRat 13 (m - 99) = 1 :=
  linear_factor_stable m 99 1 hm (by norm_num) val_base_99 (by norm_num)

/-- Throughout the printed 13-adic congruence class, `ab` has
valuation exactly one and is nonzero. -/
theorem ab_valuation_13 (m : ℚ) (hm : Congruent13Sq m) :
    a m * b m ≠ 0 ∧ padicValRat 13 (a m * b m) = 1 := by
  have h99 := linear_factor_13_99 m hm
  have h1 := linear_factor_13_other m 1 hm (by simp)
  have hn1 := linear_factor_13_other m (-1) hm (by simp)
  have h9 := linear_factor_13_other m 9 hm (by simp)
  have hn9 := linear_factor_13_other m (-9) hm (by simp)
  have h11 := linear_factor_13_other m 11 hm (by simp)
  have hn11 := linear_factor_13_other m (-11) hm (by simp)
  have hn99 := linear_factor_13_other m (-99) hm (by simp)
  have hid : a m * b m = -49 * (m - 99) * (m - -1) * (m - 11) * (m - -9) *
      (m - -99) * (m - 1) * (m - -11) * (m - 9) := by simp only [a, b]; ring
  have hc : (-49 : ℚ) ≠ 0 ∧ padicValRat 13 (-49) = 0 := by
    constructor
    · norm_num
    · norm_num [padicValRat_def, padicValInt]
  have hv := rational_valuation_mul (rational_valuation_mul (rational_valuation_mul
    (rational_valuation_mul (rational_valuation_mul (rational_valuation_mul
    (rational_valuation_mul (rational_valuation_mul hc h99) hn1) h11) hn9) hn99) h1) hn11) h9
  simpa only [hid, zero_add, add_zero] using hv

/-- An odd valuation prevents a rational number from being a square. -/
theorem not_isSquare_of_valuation_one {p : ℕ} [Fact p.Prime] {z : ℚ}
    (hz : padicValRat p z = 1) : ¬IsSquare z := by
  rintro ⟨r, hr⟩
  have heq : z = r ^ 2 := by simpa only [pow_two] using hr
  rw [heq, padicValRat.pow] at hz
  omega

/-- Neither sign of `ab` is a rational square on the prescribed class. -/
theorem ab_not_squares_13 (m : ℚ) (hm : Congruent13Sq m) :
    ¬IsSquare (a m * b m) ∧ ¬IsSquare (-(a m * b m)) := by
  have hv := (ab_valuation_13 m hm).2
  exact ⟨not_isSquare_of_valuation_one hv,
    not_isSquare_of_valuation_one (by simpa only [padicValRat.neg] using hv)⟩

/-- The 13-adic condition alone avoids every singular rational fiber. -/
theorem X_good_of_congruent13 (m : ℚ) (hm : Congruent13Sq m) : GoodCurve (X m) := by
  have hprod := (ab_valuation_13 m hm).1
  have hm0 : m ≠ 0 := by simpa only [sub_zero] using (linear_factor_13_other m 0 hm (by simp)).1
  have hn99 : ¬IsSquare (99 : ℚ) := by norm_num [Rat.isSquare_natCast_iff]
  have hm99 : m ^ 2 - 99 ≠ 0 := by
    intro hh
    apply hn99
    exact ⟨m, by nlinarith⟩
  have hminus : a m - b m ≠ 0 := by
    have heq : a m - b m = 14 * ((m ^ 2 - 1) ^ 2 + 9800) := by simp only [a, b]; ring
    rw [heq]
    positivity
  have hplus : a m + b m ≠ 0 := by
    have heq : a m + b m = -1400 * m * (m ^ 2 - 99) := by simp only [a, b]; ring
    rw [heq]
    exact mul_ne_zero (mul_ne_zero (by norm_num) hm0) hm99
  apply E_good
  apply mul_ne_zero hprod
  have heq : a m ^ 2 - b m ^ 2 = (a m - b m) * (a m + b m) := by ring
  rw [heq]
  exact mul_ne_zero hminus hplus

/-- Proposition 6.2, torsion part: every parameter in the prescribed
13-adic class gives an elliptic curve with torsion exactly `Z/2 × Z/4`. -/
theorem X_torsion_of_congruent13 (hMazur : MazurTorsionTheorem)
    (m : ℚ) (hm : Congruent13Sq m) : TorsionExact (X m) := by
  have hprod := (ab_valuation_13 m hm).1
  have hgood := X_good_of_congruent13 m hm
  have hdiff : a m ^ 2 - b m ^ 2 ≠ 0 := by
    intro hd
    have hΔ : (X m).Δ = 0 := by rw [X, E_discriminant, hd]; ring
    exact hgood.isUnit.ne_zero hΔ
  exact E_torsion_exact hMazur (a m) (b m) (mul_ne_zero hprod hdiff)
    (ab_not_squares_13 m hm).1 (ab_not_squares_13 m hm).2

end Z2Z4Rank6
