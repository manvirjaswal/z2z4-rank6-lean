import Z2Z4Rank6.SplitLegendreConditions

/-!
# Necessary conditions at shared quadratic-twist primes

These elementary primitive p² arguments treat the four squarefree valuation
patterns at a prime dividing both root differences exactly once. They supply
the shared-prime conditions used in the twist Selmer certificates of
Proposition 5.2 of Manvir Jaswal, DOI: 10.5281/zenodo.23437117.
-/

namespace Z2Z4Rank6.SplitTwistPrime

def unitPart (p : ℕ) (n : ℤ) : ℤ := if (p : ℤ) ∣ n then n / p else n

private theorem cancel_prime_square {p w : ℤ} (hp : p ≠ 0)
    (h : p ^ 2 ∣ p * w) : p ∣ w := by
  apply (mul_dvd_mul_iff_left hp).mp
  simpa only [pow_two] using h

private theorem coordinate_dvd_of_prime_square {p : ℕ} [Fact p.Prime]
    (d z : ℤ) (hs : Squarefree d) (h : (p : ℤ) ^ 2 ∣ d * z ^ 2) : (p : ℤ) ∣ z := by
  have hp : Prime (p : ℤ) := Int.prime_iff_natAbs_prime.mpr
    (by simpa using (Fact.out : p.Prime))
  have hz : (p : ℤ) ∣ z ^ 2 := hs.dvd_of_squarefree_of_mul_dvd_mul_right
    (by simpa only [pow_two] using h)
  exact hp.dvd_of_dvd_pow hz

private theorem coordinate_dvd_of_prime {p : ℕ} [Fact p.Prime]
    (d z : ℤ) (hd : ¬ (p : ℤ) ∣ d) (h : (p : ℤ) ∣ d * z ^ 2) : (p : ℤ) ∣ z := by
  have hp : Prime (p : ℤ) := Int.prime_iff_natAbs_prime.mpr
    (by simpa using (Fact.out : p.Prime))
  exact hp.dvd_of_dvd_pow ((hp.dvd_or_dvd h).resolve_left hd)

private theorem primitive_t_unit {p : ℕ} [Fact p.Prime]
    (d : ECFullTriple) (r2 r3 : ℤ) (z : Fin 4 → ℤ)
    (hs1 : Squarefree d.1) (hs2 : Squarefree d.2.1) (hs3 : Squarefree d.2.2)
    (hi : ∃ i, ¬ (p : ℤ) ∣ z i)
    (he1 : (p : ℤ)^2 ∣ d.2.1*(z 1)^2-d.1*(z 0)^2-r2*(z 3)^2)
    (he2 : (p : ℤ)^2 ∣ d.2.2*(z 2)^2-d.1*(z 0)^2-r3*(z 3)^2)
    (j : Fin 3) (hzj : (p : ℤ) ∣ z j.castSucc) : ¬ (p : ℤ) ∣ z 3 := by
  intro ht
  have ht2 : (p : ℤ)^2 ∣ r2*(z 3)^2 := dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd ht 2) _
  have ht3 : (p : ℤ)^2 ∣ r3*(z 3)^2 := dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd ht 2) _
  have hdiff1 : (p : ℤ)^2 ∣ d.2.1*(z 1)^2-d.1*(z 0)^2 := (dvd_sub_left ht2).mp he1
  have hdiff2 : (p : ℤ)^2 ∣ d.2.2*(z 2)^2-d.1*(z 0)^2 := (dvd_sub_left ht3).mp he2
  have h0 : (p : ℤ)^2 ∣ d.1*(z 0)^2 := by
    fin_cases j
    · exact dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd hzj 2) _
    · exact (dvd_sub_right (dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd hzj 2) _)).mp hdiff1
    · exact (dvd_sub_right (dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd hzj 2) _)).mp hdiff2
  have h1 : (p : ℤ)^2 ∣ d.2.1*(z 1)^2 := (dvd_sub_left h0).mp hdiff1
  have h2 : (p : ℤ)^2 ∣ d.2.2*(z 2)^2 := (dvd_sub_left h0).mp hdiff2
  have hz0 := coordinate_dvd_of_prime_square _ _ hs1 h0
  have hz1 := coordinate_dvd_of_prime_square _ _ hs2 h1
  have hz2 := coordinate_dvd_of_prime_square _ _ hs3 h2
  obtain ⟨i, hi⟩ := hi
  fin_cases i <;> exact hi (by assumption)

private theorem binary_product_square {F : Type*} [Field F]
    (a b x y : F) (hy : y ≠ 0) (h : a*x^2=b*y^2) : IsSquare (a*b) := by
  refine ⟨a*x/y, ?_⟩
  field_simp
  linear_combination -a*h

private theorem square_cancel {F : Type*} [Field F] {a b : F}
    (h : IsSquare (a*b)) (hb : IsSquare b) (hb0 : b ≠ 0) : IsSquare a := by
  convert h.div hb using 1
  field_simp

private theorem square_remove_int_factor (p a : ℤ) (hp : p ≠ 0)
    (h : IsSquare (p^2*a)) : IsSquare a := by
  apply Rat.isSquare_intCast_iff.mp
  have hpQ : (p : ℚ) ≠ 0 := by exact_mod_cast hp
  have hq : IsSquare ((p^2*a : ℤ) : ℚ) := h.map (Int.castRingHom ℚ)
  convert hq.div (IsSquare.mul_self (p : ℚ)) using 1; push_cast; field_simp

private theorem quotient_unit {p : ℕ} [Fact p.Prime]
    (d c : ℤ) (hs : Squarefree d) (hc : d=(p : ℤ)*c) : (c : ZMod p) ≠ 0 := by
  intro hz
  have hp : Prime (p : ℤ) := Int.prime_iff_natAbs_prime.mpr
    (by simpa using (Fact.out : p.Prime))
  obtain ⟨x, hx⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz
  apply hp.not_isUnit
  apply hs (p : ℤ)
  refine ⟨x, ?_⟩
  rw [hc, hx]
  ring

theorem unitPart_cast_ne_zero {p : ℕ} [Fact p.Prime]
    (d : ℤ) (hs : Squarefree d) : (unitPart p d : ZMod p) ≠ 0 := by
  by_cases hd : (p : ℤ) ∣ d
  · rw [unitPart, ite_eq_left hd]
    apply quotient_unit d (d / p) hs
    exact (Int.mul_ediv_cancel' hd).symm
  · rw [unitPart, ite_eq_right hd]
    exact fun hz => hd ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz)

private theorem covering_rotate {F : Type*} [CommRing F]
    (d1 d2 d3 r2 r3 : F) (h : SplitCoverSoluble d1 d2 d3 r2 r3) :
    SplitCoverSoluble d2 d3 d1 (r3-r2) (-r2) := by
  obtain ⟨z, ⟨i, hi⟩, h1, h2⟩ := h
  refine ⟨![z 1,z 2,z 0,z 3], ?_, ?_, ?_⟩
  · fin_cases i
    · exact ⟨2, by simpa using hi⟩
    · exact ⟨0, by simpa using hi⟩
    · exact ⟨1, by simpa using hi⟩
    · exact ⟨3, by simpa using hi⟩
  · change d3*(z 2)^2-d2*(z 1)^2=(r3-r2)*(z 3)^2
    linear_combination h2-h1
  · change d1*(z 0)^2-d2*(z 1)^2=(-r2)*(z 3)^2
    linear_combination -h1

private theorem everywhere_rotate (d : ECFullTriple) (r2 r3 : ℤ)
    (h : SplitCoverEverywhereLocallySoluble d r2 r3) :
    SplitCoverEverywhereLocallySoluble (d.2.1,d.2.2,d.1) (r3-r2) (-r2) := by
  constructor
  · simpa only [Int.cast_sub, Int.cast_neg] using covering_rotate _ _ _ _ _ h.1
  · intro p hp
    simpa only [Int.cast_sub, Int.cast_neg] using covering_rotate _ _ _ _ _ (h.2 p)

/-- Leading square conditions when the first two coefficients contain p
and the third is a unit. This is the elementary ramified p² calculation. -/
theorem leading_110 {p : ℕ} [Fact p.Prime]
    (d : ECFullTriple) (r2 r3 R2 R3 c1 c2 : ℤ)
    (hs1 : Squarefree d.1) (hs2 : Squarefree d.2.1) (hs3 : Squarefree d.2.2)
    (hr2 : r2=(p : ℤ)*R2) (hr3 : r3=(p : ℤ)*R3)
    (hd1 : d.1=(p : ℤ)*c1) (hd2 : d.2.1=(p : ℤ)*c2)
    (hd3 : ¬ (p : ℤ) ∣ d.2.2)
    (hlocal : SplitCoverEverywhereLocallySoluble d r2 r3) :
    IsSquare ((c1*(-R3) : ℤ) : ZMod p) ∧
      IsSquare ((c2*(R2-R3) : ℤ) : ZMod p) := by
  obtain ⟨z, hi, he1, he2⟩ := splitCover_primitive_int_residues d r2 r3 (hlocal.2 p)
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hpp : (p : ℤ) ∣ (p : ℤ)^2 := dvd_pow_self _ (by decide)
  have hd1p : (p : ℤ) ∣ d.1 := ⟨c1, hd1⟩
  have hr3p : (p : ℤ) ∣ r3 := ⟨R3, hr3⟩
  have hdiff : (p : ℤ) ∣ d.2.2*(z 2)^2-d.1*(z 0)^2 :=
    (dvd_sub_left (dvd_mul_of_dvd_left hr3p _)).mp (hpp.trans he2)
  have hz2 : (p : ℤ) ∣ z 2 := coordinate_dvd_of_prime _ _ hd3
    ((dvd_sub_left (dvd_mul_of_dvd_left hd1p _)).mp hdiff)
  have ht := primitive_t_unit d r2 r3 z hs1 hs2 hs3 hi he1 he2 2 hz2
  have htF : (z 3 : ZMod p) ≠ 0 :=
    fun hh => ht ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hh)
  have h2 : (p : ℤ) ∣ -c1*(z 0)^2-R3*(z 3)^2 := by
    have hcoef : (p : ℤ)^2 ∣ d.2.2*(z 2)^2 :=
      dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd hz2 2) _
    have hh : (p : ℤ)^2 ∣ -d.1*(z 0)^2-r3*(z 3)^2 := by
      convert dvd_sub he2 hcoef using 1; ring
    apply cancel_prime_square hp0
    convert hh using 1; rw [hd1, hr3]; ring
  have h1 : (p : ℤ) ∣ c2*(z 1)^2-c1*(z 0)^2-R2*(z 3)^2 := by
    apply cancel_prime_square hp0
    convert he1 using 1; rw [hd1, hd2, hr2]; ring
  have h2F : (-c1 : ZMod p)*(z 0 : ZMod p)^2=(R3 : ZMod p)*(z 3 : ZMod p)^2 := by
    have hh := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h2
    push_cast at hh
    exact sub_eq_zero.mp hh
  have h1F : (c2 : ZMod p)*(z 1 : ZMod p)^2=
      ((R2-R3 : ℤ) : ZMod p)*(z 3 : ZMod p)^2 := by
    have hh := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h1
    push_cast at hh ⊢
    linear_combination hh-h2F
  constructor
  · simpa only [Int.cast_mul, Int.cast_neg, neg_mul, mul_neg] using
      binary_product_square (-c1 : ZMod p) (R3 : ZMod p) _ _ htF h2F
  · simpa only [Int.cast_mul] using
      binary_product_square (c2 : ZMod p) ((R2-R3 : ℤ) : ZMod p) _ _ htF h1F

/-- The other mixed valuation pattern, obtained by interchanging the later
root differences and their covering coordinates. -/
theorem leading_101 {p : ℕ} [Fact p.Prime]
    (d : ECFullTriple) (r2 r3 R2 R3 c1 c3 : ℤ)
    (hs1 : Squarefree d.1) (hs2 : Squarefree d.2.1) (hs3 : Squarefree d.2.2)
    (hr2 : r2=(p : ℤ)*R2) (hr3 : r3=(p : ℤ)*R3)
    (hd1 : d.1=(p : ℤ)*c1) (hd3 : d.2.2=(p : ℤ)*c3)
    (hd2 : ¬ (p : ℤ) ∣ d.2.1)
    (hlocal : SplitCoverEverywhereLocallySoluble d r2 r3) :
    IsSquare ((c1*(-R2) : ℤ) : ZMod p) ∧
      IsSquare ((c3*(R3-R2) : ℤ) : ZMod p) :=
  leading_110 (d.1,d.2.2,d.2.1) r3 r2 R3 R2 c1 c3
    hs1 hs3 hs2 hr3 hr2 hd1 hd3 hd2 (splitCover_everywhere_swap d r2 r3 hlocal)

/-- The pattern where both later coefficients ramify, obtained by moving
the origin to the second root of the split cubic. -/
theorem leading_011 {p : ℕ} [Fact p.Prime]
    (d : ECFullTriple) (r2 r3 R2 R3 c2 c3 : ℤ)
    (hs1 : Squarefree d.1) (hs2 : Squarefree d.2.1) (hs3 : Squarefree d.2.2)
    (hr2 : r2=(p : ℤ)*R2) (hr3 : r3=(p : ℤ)*R3)
    (hd2 : d.2.1=(p : ℤ)*c2) (hd3 : d.2.2=(p : ℤ)*c3)
    (hd1 : ¬ (p : ℤ) ∣ d.1)
    (hlocal : SplitCoverEverywhereLocallySoluble d r2 r3) :
    IsSquare ((c2*R2 : ℤ) : ZMod p) ∧ IsSquare ((c3*R3 : ℤ) : ZMod p) := by
  have hr2' : r3-r2=(p : ℤ)*(R3-R2) := by rw [hr2,hr3]; ring
  have hr3' : -r2=(p : ℤ)*(-R2) := by rw [hr2]; ring
  have hh := leading_110 (d.2.1,d.2.2,d.1) (r3-r2) (-r2) (R3-R2) (-R2) c2 c3
    hs2 hs3 hs1 hr2' hr3' hd2 hd3 hd1 (everywhere_rotate d r2 r3 hlocal)
  simpa only [neg_neg,sub_neg_eq_add,sub_add_cancel] using hh

/-- In the unramified pattern all three coefficient units are squares.
A vanishing first coordinate would force all coordinates to vanish modulo p,
using the simple p-factor in the first root difference. -/
theorem leading_000 {p : ℕ} [Fact p.Prime]
    (d : ECFullTriple) (r2 r3 R2 R3 : ℤ)
    (hs1 : Squarefree d.1) (hs2 : Squarefree d.2.1) (hs3 : Squarefree d.2.2)
    (hr2 : r2=(p : ℤ)*R2) (hr3 : r3=(p : ℤ)*R3)
    (hR2 : (R2 : ZMod p)≠0)
    (hd1 : ¬ (p : ℤ) ∣ d.1) (hd2 : ¬ (p : ℤ) ∣ d.2.1) (hd3 : ¬ (p : ℤ) ∣ d.2.2)
    (hsq : IsSquare (d.1*d.2.1*d.2.2))
    (hlocal : SplitCoverEverywhereLocallySoluble d r2 r3) :
    IsSquare (d.1 : ZMod p) ∧ IsSquare (d.2.1 : ZMod p) := by
  obtain ⟨z, hi, he1, he2⟩ := splitCover_primitive_int_residues d r2 r3 (hlocal.2 p)
  have hp : Prime (p : ℤ) := Int.prime_iff_natAbs_prime.mpr
    (by simpa using (Fact.out : p.Prime))
  have hpp : (p : ℤ) ∣ (p : ℤ)^2 := dvd_pow_self _ (by decide)
  have hr2p : (p : ℤ) ∣ r2 := ⟨R2,hr2⟩
  have hr3p : (p : ℤ) ∣ r3 := ⟨R3,hr3⟩
  have hdiff1 : (p : ℤ) ∣ d.2.1*(z 1)^2-d.1*(z 0)^2 :=
    (dvd_sub_left (dvd_mul_of_dvd_left hr2p _)).mp (hpp.trans he1)
  have hdiff2 : (p : ℤ) ∣ d.2.2*(z 2)^2-d.1*(z 0)^2 :=
    (dvd_sub_left (dvd_mul_of_dvd_left hr3p _)).mp (hpp.trans he2)
  have hz0 : ¬ (p : ℤ) ∣ z 0 := by
    intro hz0
    have h0 : (p : ℤ) ∣ d.1*(z 0)^2 := dvd_mul_of_dvd_right (dvd_pow hz0 (by decide)) _
    have hz1 := coordinate_dvd_of_prime _ _ hd2 ((dvd_sub_left h0).mp hdiff1)
    have ht := primitive_t_unit d r2 r3 z hs1 hs2 hs3 hi he1 he2 0 hz0
    have hcoef : (p : ℤ)^2 ∣ d.2.1*(z 1)^2-d.1*(z 0)^2 := dvd_sub
      (dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd hz1 2) _)
      (dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd hz0 2) _)
    have hroot : (p : ℤ)^2 ∣ r2*(z 3)^2 := (dvd_sub_right hcoef).mp he1
    have hRt : (p : ℤ) ∣ R2*(z 3)^2 := by
      apply cancel_prime_square hp.ne_zero
      simpa only [hr2,mul_assoc] using hroot
    have hR2p : ¬ (p : ℤ) ∣ R2 :=
      fun hh => hR2 ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hh)
    exact ht (hp.dvd_of_dvd_pow ((hp.dvd_or_dvd hRt).resolve_left hR2p))
  have hz0F : (z 0 : ZMod p) ≠ 0 :=
    fun hh => hz0 ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hh)
  have h12 : IsSquare ((d.1 : ZMod p)*(d.2.1 : ZMod p)) := by
    have hh := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hdiff1
    push_cast at hh
    simpa only [mul_comm] using binary_product_square (d.2.1 : ZMod p)
      (d.1 : ZMod p) _ _ hz0F (sub_eq_zero.mp hh)
  have h13 : IsSquare ((d.1 : ZMod p)*(d.2.2 : ZMod p)) := by
    have hh := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hdiff2
    push_cast at hh
    simpa only [mul_comm] using binary_product_square (d.2.2 : ZMod p)
      (d.1 : ZMod p) _ _ hz0F (sub_eq_zero.mp hh)
  have hd1F : (d.1 : ZMod p) ≠ 0 :=
    fun hh => hd1 ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hh)
  have hd2F : (d.2.1 : ZMod p) ≠ 0 :=
    fun hh => hd2 ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hh)
  have hd3F : (d.2.2 : ZMod p) ≠ 0 :=
    fun hh => hd3 ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hh)
  have h23 : IsSquare ((d.2.1 : ZMod p)*(d.2.2 : ZMod p)) := by
    convert (h12.mul h13).div (IsSquare.mul_self (d.1 : ZMod p)) using 1
    field_simp
  have hpF : IsSquare ((d.1 : ZMod p)*((d.2.1 : ZMod p)*(d.2.2 : ZMod p))) := by
    have hm : IsSquare ((d.1*d.2.1*d.2.2 : ℤ) : ZMod p) := hsq.map (Int.castRingHom (ZMod p))
    simpa only [Int.cast_mul,mul_assoc] using hm
  have h1 := square_cancel hpF h23 (mul_ne_zero hd2F hd3F)
  exact ⟨h1,square_cancel (by simpa only [mul_comm] using h12) h1 hd1F⟩

/-- The two square conditions at a shared twist prime. The product R2*R3
must itself be a square modulo p, as it is for R2=(D/p)A², R3=(D/p)B².
The conditions are precisely the two unit-character equations used by the
finite Legendre-symbol sieve. -/
theorem shared_prime_square_conditions {p : ℕ} [Fact p.Prime]
    (d : ECFullTriple) (r2 r3 R2 R3 : ℤ)
    (hs1 : Squarefree d.1) (hs2 : Squarefree d.2.1) (hs3 : Squarefree d.2.2)
    (hr2 : r2=(p : ℤ)*R2) (hr3 : r3=(p : ℤ)*R3)
    (hR2 : (R2 : ZMod p)≠0) (hR3 : (R3 : ZMod p)≠0)
    (hRR : IsSquare ((R2*R3 : ℤ) : ZMod p))
    (hsq : IsSquare (d.1*d.2.1*d.2.2))
    (hlocal : SplitCoverEverywhereLocallySoluble d r2 r3) :
    IsSquare ((unitPart p d.1 * (if (p : ℤ)∣d.1 then -R3 else 1) : ℤ) : ZMod p) ∧
    IsSquare ((unitPart p d.2.1 * (if (p : ℤ)∣d.1 then R2*(R2-R3) else 1) *
      (if (p : ℤ)∣d.2.1 then R2 else 1) : ℤ) : ZMod p) := by
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hRR' : IsSquare ((R2 : ZMod p)*(R3 : ZMod p)) := by
    simpa only [Int.cast_mul] using hRR
  by_cases hd1 : (p : ℤ) ∣ d.1
  · let c1 := d.1 / p
    have he1 : d.1=(p : ℤ)*c1 := (Int.mul_ediv_cancel' hd1).symm
    by_cases hd2 : (p : ℤ) ∣ d.2.1
    · let c2 := d.2.1 / p
      have he2 : d.2.1=(p : ℤ)*c2 := (Int.mul_ediv_cancel' hd2).symm
      have hd3 : ¬(p : ℤ)∣d.2.2 := by
        rcases squarefree_product_prime_parity d.1 d.2.1 d.2.2 hs1 hs2 hs3 hsq hd1 with h | h
        · exact h.2
        · exact False.elim (h.1 hd2)
      have hh := leading_110 d r2 r3 R2 R3 c1 c2 hs1 hs2 hs3 hr2 hr3 he1 he2 hd3 hlocal
      simp only [unitPart,ite_eq_left hd1,ite_eq_left hd2]
      constructor
      · exact hh.1
      · convert hh.2.mul (IsSquare.mul_self (R2 : ZMod p)) using 1
        push_cast
        ring
    · let c3 := d.2.2 / p
      have hd3 : (p : ℤ)∣d.2.2 := by
        rcases squarefree_product_prime_parity d.1 d.2.1 d.2.2 hs1 hs2 hs3 hsq hd1 with h | h
        · exact False.elim (hd2 h.1)
        · exact h.2
      have he3 : d.2.2=(p : ℤ)*c3 := (Int.mul_ediv_cancel' hd3).symm
      have hh := leading_101 d r2 r3 R2 R3 c1 c3 hs1 hs2 hs3 hr2 hr3 he1 he3 hd2 hlocal
      have hc1 := quotient_unit d.1 c1 hs1 he1
      have hc3 := quotient_unit d.2.2 c3 hs3 he3
      have hred : IsSquare (c1*d.2.1*c3) := by
        apply square_remove_int_factor (p : ℤ) _ hp0
        convert hsq using 1; rw [he1,he3]; ring
      have hredF : IsSquare ((c1*d.2.1*c3 : ℤ) : ZMod p) :=
        hred.map (Int.castRingHom (ZMod p))
      simp only [unitPart,ite_eq_left hd1,ite_eq_right hd2,mul_one]
      constructor
      · change IsSquare ((c1*(-R3) : ℤ) : ZMod p)
        convert (hh.1.mul hRR').div (IsSquare.mul_self (R2 : ZMod p)) using 1
        push_cast
        field_simp
      · convert (hredF.mul (hh.1.mul hh.2)).div
          (IsSquare.mul_self ((c1 : ZMod p)*(c3 : ZMod p))) using 1
        push_cast
        field_simp
        ring
  · by_cases hd2 : (p : ℤ) ∣ d.2.1
    · let c2 := d.2.1 / p
      let c3 := d.2.2 / p
      have hd3 : (p : ℤ)∣d.2.2 := by
        have hsq' : IsSquare (d.2.1*d.1*d.2.2) := by
          simpa only [mul_comm d.1 d.2.1] using hsq
        rcases squarefree_product_prime_parity d.2.1 d.1 d.2.2 hs2 hs1 hs3 hsq' hd2 with h | h
        · exact False.elim (hd1 h.1)
        · exact h.2
      have he2 : d.2.1=(p : ℤ)*c2 := (Int.mul_ediv_cancel' hd2).symm
      have he3 : d.2.2=(p : ℤ)*c3 := (Int.mul_ediv_cancel' hd3).symm
      have hh := leading_011 d r2 r3 R2 R3 c2 c3 hs1 hs2 hs3 hr2 hr3 he2 he3 hd1 hlocal
      have hc2 := quotient_unit d.2.1 c2 hs2 he2
      have hc3 := quotient_unit d.2.2 c3 hs3 he3
      have hred : IsSquare (d.1*c2*c3) := by
        apply square_remove_int_factor (p : ℤ) _ hp0
        convert hsq using 1; rw [he2,he3]; ring
      have hredF : IsSquare ((d.1 : ZMod p)*((c2 : ZMod p)*(c3 : ZMod p))) := by
        have hm : IsSquare ((d.1*c2*c3 : ℤ) : ZMod p) := hred.map (Int.castRingHom (ZMod p))
        simpa only [Int.cast_mul,mul_assoc] using hm
      have h23 : IsSquare ((c2 : ZMod p)*(c3 : ZMod p)) := by
        convert (hh.1.mul hh.2).div hRR' using 1
        push_cast
        field_simp
      simp only [unitPart,ite_eq_right hd1,ite_eq_left hd2,mul_one]
      exact ⟨square_cancel hredF h23 (mul_ne_zero hc2 hc3),hh.1⟩
    · have hd3 : ¬(p : ℤ)∣d.2.2 := by
        intro h3
        have hsq' : IsSquare (d.2.2*d.1*d.2.1) := by convert hsq using 1; ring
        rcases squarefree_product_prime_parity d.2.2 d.1 d.2.1 hs3 hs1 hs2 hsq' h3 with h | h
        · exact hd1 h.1
        · exact hd2 h.2
      simp only [unitPart,ite_eq_right hd1,ite_eq_right hd2,mul_one]
      exact leading_000 d r2 r3 R2 R3 hs1 hs2 hs3 hr2 hr3 hR2 hd1 hd2 hd3 hsq hlocal

end Z2Z4Rank6.SplitTwistPrime
