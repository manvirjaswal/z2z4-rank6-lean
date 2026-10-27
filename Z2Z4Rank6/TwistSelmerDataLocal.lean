module

public import Z2Z4Rank6.SplitLegendreConditions

@[expose] public section

/-!
# Odd-prime local conditions for the twist certificates

Elementary primitive congruence consequences of the two-covering
quadrics used in Proposition 5.2 of M. Jaswal,
DOI 10.5281/zenodo.23437117.
-/

namespace Z2Z4Rank6.TwistSelmer

/-- A p-adic covering point gives primitive integer residues to any
positive precision, by normalizing one integral coordinate to one. -/
theorem primitive_int_residues_pow {p : ℕ} [Fact p.Prime]
    (k : ℕ) (hk : k ≠ 0) (d : ECFullTriple) (r2 r3 : ℤ)
    (h : SplitCoverSoluble (d.1 : ℚ_[p]) (d.2.1 : ℚ_[p]) (d.2.2 : ℚ_[p])
      (r2 : ℚ_[p]) (r3 : ℚ_[p])) :
    ∃ z : Fin 4 → ℤ, (∃ i, ¬(p : ℤ) ∣ z i) ∧
      (p : ℤ)^k ∣ d.2.1*(z 1)^2-d.1*(z 0)^2-r2*(z 3)^2 ∧
      (p : ℤ)^k ∣ d.2.2*(z 2)^2-d.1*(z 0)^2-r3*(z 3)^2 := by
  have hpK : 1 < p^k := one_lt_pow₀ (Fact.out : p.Prime).one_lt hk
  let : Fact (1 < p^k) := ⟨hpK⟩
  obtain ⟨w,⟨i,hi⟩,h1,h2⟩ := splitCover_integral_normalization_general d r2 r3 h
  let q : Fin 4 → ZMod (p^k) := fun j => PadicInt.toZModPow k (w j)
  let z : Fin 4 → ℤ := fun j => ((q j).val : ℤ)
  have hz (j : Fin 4) : (z j : ZMod (p^k))=q j := by
    simp only [z,Int.cast_natCast,ZMod.natCast_zmod_val]
  have hqi : q i=1 := by simp only [q,hi,map_one]
  refine ⟨z,⟨i,?_⟩,?_,?_⟩
  · have hzi : z i=1 := by simp only [z,hqi,ZMod.val_one (p^k),Int.natCast_one]
    rw [hzi]
    exact (Int.prime_iff_natAbs_prime.mpr (by simpa using (Fact.out : p.Prime))).not_dvd_one
  · have he : ((d.2.1*(z 1)^2-d.1*(z 0)^2-r2*(z 3)^2 : ℤ) : ZMod (p^k))=0 := by
      push_cast
      simp only [hz]
      have hm := congrArg (PadicInt.toZModPow k) h1
      simp only [map_sub,map_mul,map_pow,map_intCast] at hm
      exact sub_eq_zero.mpr hm
    simpa only [Nat.cast_pow] using (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp he
  · have he : ((d.2.2*(z 2)^2-d.1*(z 0)^2-r3*(z 3)^2 : ℤ) : ZMod (p^k))=0 := by
      push_cast
      simp only [hz]
      have hm := congrArg (PadicInt.toZModPow k) h2
      simp only [map_sub,map_mul,map_pow,map_intCast] at hm
      exact sub_eq_zero.mpr hm
    simpa only [Nat.cast_pow] using (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp he

private theorem cancel_prime_pow {p w : ℤ} (hp : p≠0) (k : ℕ)
    (h : p^(k+1) ∣ p^k*w) : p∣w := by
  rw [pow_succ] at h
  exact (mul_dvd_mul_iff_left (pow_ne_zero k hp)).mp h

private theorem quotient_nondivisible {p d c : ℤ} (hp : Prime p)
    (hd : Squarefree d) (he : d=p*c) : ¬p∣c := by
  rintro ⟨x,hx⟩
  apply hp.not_isUnit
  apply hd p
  refine ⟨x,?_⟩
  rw [he,hx]
  ring

private theorem square_without_square_factor (p a : ℤ) (hp : p≠0)
    (h : IsSquare (p^2*a)) : IsSquare a := by
  apply Rat.isSquare_intCast_iff.mp
  have hpQ : (p : ℚ)≠0 := by exact_mod_cast hp
  have hq : IsSquare ((p^2*a : ℤ) : ℚ) := h.map (Int.castRingHom ℚ)
  have hs := hq.div (IsSquare.mul_self (p : ℚ))
  convert hs using 1; push_cast; field_simp

private theorem square_of_mul_square {F : Type*} [Field F] {a b : F}
    (h : IsSquare (a*b)) (hb : IsSquare b) (hb0 : b≠0) : IsSquare a := by
  convert h.div hb using 1
  field_simp

/-- With a root difference of valuation exactly two, ramification of both
first covering coefficients forces their unit parts to have square product.
The proof needs precision p³, rather than the p² support test. -/
theorem first_pair_unit_product_square {p : ℕ} [Fact p.Prime]
    (d : ECFullTriple) (r2 r3 c1 c2 R : ℤ)
    (hd1 : d.1=(p : ℤ)*c1) (hd2 : d.2.1=(p : ℤ)*c2)
    (hr2 : r2=(p : ℤ)^2*R) (hR : ¬(p : ℤ)∣R) (hd3 : ¬(p : ℤ)∣d.2.2)
    (hlocal : SplitCoverEverywhereLocallySoluble d r2 r3) :
    IsSquare ((c1*c2 : ℤ) : ZMod p) := by
  by_contra hn
  obtain ⟨z,⟨i,hi⟩,he1,he2⟩ := primitive_int_residues_pow 3 (by decide) d r2 r3 (hlocal.2 p)
  have hp : Prime (p : ℤ) := Int.prime_iff_natAbs_prime.mpr (by simpa using (Fact.out : p.Prime))
  have hp32 : (p : ℤ)^2 ∣ (p : ℤ)^3 := pow_dvd_pow _ (by decide : 2≤3)
  have hp31 : (p : ℤ) ∣ (p : ℤ)^3 := dvd_pow_self _ (by decide)
  have h1 : (p : ℤ)∣c2*(z 1)^2-c1*(z 0)^2 := by
    apply cancel_prime_pow hp.ne_zero 1
    have hh : (p : ℤ)^2∣d.2.1*(z 1)^2-d.1*(z 0)^2 := by
      apply (dvd_sub_left (dvd_mul_of_dvd_left (show (p : ℤ)^2∣r2 by rw [hr2]; exact dvd_mul_right _ _) _)).mp
      exact hp32.trans he1
    convert hh using 1; rw [hd1,hd2]; ring
  have hn' : ¬IsSquare ((c2*c1 : ℤ) : ZMod p) := by simpa only [mul_comm] using hn
  obtain ⟨hb,ha⟩ := prime_dvd_binary_of_not_isSquare c2 c1 (z 1) (z 0) hn' h1
  have hd1a : (p : ℤ)^3∣d.1*(z 0)^2 := by
    obtain ⟨a,hea⟩ := ha
    refine ⟨c1*a^2,?_⟩
    rw [hd1,hea]
    ring
  have hd2b : (p : ℤ)^3∣d.2.1*(z 1)^2 := by
    obtain ⟨b,heb⟩ := hb
    refine ⟨c2*b^2,?_⟩
    rw [hd2,heb]
    ring
  have ht : (p : ℤ)∣z 3 := by
    have hrt : (p : ℤ)^3∣r2*(z 3)^2 :=
      (dvd_sub_right (dvd_sub hd2b hd1a)).mp he1
    have hRt : (p : ℤ)∣R*(z 3)^2 := by
      apply cancel_prime_pow hp.ne_zero 2
      convert hrt using 1; rw [hr2]; ring
    exact hp.dvd_of_dvd_pow ((hp.dvd_or_dvd hRt).resolve_left hR)
  have hc : (p : ℤ)∣z 2 := by
    have hh : (p : ℤ)∣d.2.2*(z 2)^2 := by
      have hrest : (p : ℤ)∣d.1*(z 0)^2+r3*(z 3)^2 :=
        dvd_add (hp31.trans hd1a) (dvd_mul_of_dvd_right (dvd_pow ht (by decide)) _)
      have he : (p : ℤ)∣d.2.2*(z 2)^2-(d.1*(z 0)^2+r3*(z 3)^2) := by
        convert hp31.trans he2 using 1; ring
      exact (dvd_sub_left hrest).mp he
    exact hp.dvd_of_dvd_pow ((hp.dvd_or_dvd hh).resolve_left hd3)
  fin_cases i <;> exact hi (by assumption)

/-- A nonsquare unit second root excludes first-coefficient ramification
when the first root has valuation exactly two. -/
theorem first_coefficient_unramified {p : ℕ} [Fact p.Prime]
    (d : ECFullTriple) (r2 r3 R : ℤ)
    (hs1 : Squarefree d.1) (hs2 : Squarefree d.2.1) (hs3 : Squarefree d.2.2)
    (hsq : IsSquare (d.1*d.2.1*d.2.2))
    (hr2 : r2=(p : ℤ)^2*R) (hR : ¬(p : ℤ)∣R) (hd3 : ¬(p : ℤ)∣d.2.2)
    (hr3 : ¬IsSquare (r3 : ZMod p))
    (hlocal : SplitCoverEverywhereLocallySoluble d r2 r3) : ¬(p : ℤ)∣d.1 := by
  intro hd1
  have hp : Prime (p : ℤ) := Int.prime_iff_natAbs_prime.mpr (by simpa using (Fact.out : p.Prime))
  have hd2 : (p : ℤ)∣d.2.1 := by
    rcases squarefree_product_prime_parity d.1 d.2.1 d.2.2 hs1 hs2 hs3 hsq hd1 with h | h
    · exact h.1
    · exact False.elim (hd3 h.2)
  obtain ⟨c1,hc1⟩ := hd1
  obtain ⟨c2,hc2⟩ := hd2
  have h12 := first_pair_unit_product_square d r2 r3 c1 c2 R hc1 hc2 hr2 hR hd3 hlocal
  have hc10 : (c1 : ZMod p)≠0 := by
    intro hz
    exact quotient_nondivisible hp hs1 hc1 ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz)
  have hc20 : (c2 : ZMod p)≠0 := by
    intro hz
    exact quotient_nondivisible hp hs2 hc2 ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz)
  have hsred : IsSquare (c1*c2*d.2.2) := by
    apply square_without_square_factor (p : ℤ) _ hp.ne_zero
    convert hsq using 1; rw [hc1,hc2]; ring
  have hd3sq : IsSquare (d.2.2 : ZMod p) := by
    apply square_of_mul_square (b:=((c1 : ZMod p)*(c2 : ZMod p))) _
      (by simpa only [Int.cast_mul] using h12) (mul_ne_zero hc10 hc20)
    have hm : IsSquare ((c1*c2*d.2.2 : ℤ) : ZMod p) := hsred.map (Int.castRingHom (ZMod p))
    convert hm using 1; push_cast; ring
  have hprod : IsSquare ((d.2.2*r3 : ℤ) : ZMod p) := by
    by_contra hn
    apply splitCover_binary_obstruction_later_ramified (d.2.2,d.1,d.2.1) (-r3) (r2-r3)
      hs1 hs2 (by exact hc1 ▸ dvd_mul_right (p : ℤ) c1) _ (hlocal.rotate_first_third d r2 r3)
    simpa using hn
  apply hr3
  apply square_of_mul_square (b:=(d.2.2 : ZMod p)) _ hd3sq
    (fun hz => hd3 ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz))
  simpa only [Int.cast_mul,mul_comm] using hprod

/-- The symmetric nonramification condition for the other square root. -/
theorem first_coefficient_unramified_of_third_root {p : ℕ} [Fact p.Prime]
    (d : ECFullTriple) (r2 r3 R : ℤ)
    (hs1 : Squarefree d.1) (hs2 : Squarefree d.2.1) (hs3 : Squarefree d.2.2)
    (hsq : IsSquare (d.1*d.2.1*d.2.2))
    (hr3 : r3=(p : ℤ)^2*R) (hR : ¬(p : ℤ)∣R) (hd2 : ¬(p : ℤ)∣d.2.1)
    (hr2 : ¬IsSquare (r2 : ZMod p))
    (hlocal : SplitCoverEverywhereLocallySoluble d r2 r3) : ¬(p : ℤ)∣d.1 := by
  apply first_coefficient_unramified (d.1,d.2.2,d.2.1) r3 r2 R hs1 hs3 hs2 _
    hr3 hR hd2 hr2 (splitCover_everywhere_swap d r2 r3 hlocal)
  convert hsq using 1; ring

/-- At a simple difference prime the necessary character has the factor
-r₂ in the ramified case. This also covers nonsquare twists. -/
theorem first_mixed_isSquare_of_simple_difference {p : ℕ} [Fact p.Prime]
    (d : ECFullTriple) (r2 r3 : ℤ)
    (hs1 : Squarefree d.1) (hs2 : Squarefree d.2.1) (hs3 : Squarefree d.2.2)
    (hsq : IsSquare (d.1*d.2.1*d.2.2))
    (hr : (p : ℤ)∣r2-r3) (hrsq : ¬(p : ℤ)^2∣r2-r3)
    (hd10 : ¬(p : ℤ)∣d.1)
    (hlocal : SplitCoverEverywhereLocallySoluble d r2 r3) :
    IsSquare ((if (p : ℤ)∣d.2.1 then -d.1*r2 else d.1 : ℤ) : ZMod p) := by
  split_ifs with hd2
  · by_contra hn
    exact splitCover_binary_obstruction_later_ramified d r2 r3 hs2 hs3 hd2 hn hlocal
  · have hd3 : ¬(p : ℤ)∣d.2.2 := by
      intro h3
      have hsq' : IsSquare (d.2.2*d.1*d.2.1) := by convert hsq using 1; ring
      rcases squarefree_product_prime_parity d.2.2 d.1 d.2.1 hs3 hs1 hs2 hsq' h3 with h | h
      · exact hd10 h.1
      · exact hd2 h.2
    by_contra hn1
    have hn23 : ¬IsSquare ((d.2.1*d.2.2 : ℤ) : ZMod p) := by
      intro h23
      apply hn1
      have hprod : IsSquare ((d.1 : ZMod p)*((d.2.1 : ZMod p)*(d.2.2 : ZMod p))) := by
        have hh : IsSquare ((d.1*d.2.1*d.2.2 : ℤ) : ZMod p) := hsq.map (Int.castRingHom (ZMod p))
        convert hh using 1; push_cast; ring
      have h23p : IsSquare ((d.2.1 : ZMod p)*(d.2.2 : ZMod p)) := by
        simpa only [Int.cast_mul] using h23
      apply square_of_mul_square hprod h23p
      exact mul_ne_zero (fun hz => hd2 ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz))
        (fun hz => hd3 ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz))
    exact splitCover_binary_obstruction_later_unramified d r2 r3 hr hrsq hd10 hn23 hlocal


end Z2Z4Rank6.TwistSelmer
