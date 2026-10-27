import Z2Z4Rank6.SplitQuadraticObstructions

/-! # Necessary odd-prime square conditions for split two-coverings -/

namespace Z2Z4Rank6

private theorem isSquare_of_mul_square_right {F : Type*} [Field F]
    {a b : F} (h : IsSquare (a*b)) (hb : IsSquare b) (hb0 : b≠0) : IsSquare a := by
  convert h.div hb using 1
  field_simp

private theorem isSquare_of_int_square_factor (p a : ℤ) (hp : p≠0)
    (h : IsSquare (p^2*a)) : IsSquare a := by
  apply Rat.isSquare_intCast_iff.mp
  have hpQ : (p : ℚ)≠0 := by exact_mod_cast hp
  have hq : IsSquare ((p^2*a : ℤ) : ℚ) := h.map (Int.castRingHom ℚ)
  have hs := hq.div (IsSquare.mul_self (p : ℚ))
  convert hs using 1; push_cast; field_simp

private theorem not_dvd_quotient_of_squarefree {p d c : ℤ} (hp : Prime p)
    (hd : Squarefree d) (he : d=p*c) : ¬p∣c := by
  rintro ⟨x,hx⟩
  apply hp.not_isUnit
  apply hd p
  refine ⟨x,?_⟩
  rw [he,hx]
  ring

/-- At a prime dividing a square first root difference, the third covering
coefficient must be a square modulo p. This includes both coefficient
ramification patterns allowed by the square-product condition. -/
theorem splitCover_third_isSquare_of_first_square {p : ℕ} [Fact p.Prime]
    (d : ECFullTriple) (r2 r3 : ℤ)
    (hs1 : Squarefree d.1) (hs2 : Squarefree d.2.1) (hs3 : Squarefree d.2.2)
    (hsq : IsSquare (d.1*d.2.1*d.2.2))
    (hr2 : (p : ℤ)^2∣r2) (hr3 : IsSquare (r3 : ZMod p))
    (hr30 : (r3 : ZMod p)≠0) (hd30 : ¬(p : ℤ)∣d.2.2)
    (hlocal : SplitCoverEverywhereLocallySoluble d r2 r3) :
    IsSquare (d.2.2 : ZMod p) := by
  by_contra hn3
  have hp : Prime (p : ℤ) := Int.prime_iff_natAbs_prime.mpr (by simpa using (Fact.out : p.Prime))
  have hn3r : ¬IsSquare ((d.2.2*r3 : ℤ) : ZMod p) := by
    intro hh
    apply hn3
    apply isSquare_of_mul_square_right (b:=(r3 : ZMod p)) _ hr3 hr30
    simpa only [Int.cast_mul] using hh
  by_cases hd1 : (p : ℤ)∣d.1
  · have hd2 : (p : ℤ)∣d.2.1 := by
      rcases squarefree_product_prime_parity d.1 d.2.1 d.2.2 hs1 hs2 hs3 hsq hd1 with h | h
      · exact h.1
      · exact False.elim (hd30 h.2)
    obtain ⟨c1,hc1⟩ := hd1
    obtain ⟨c2,hc2⟩ := hd2
    have hc10 : (c1 : ZMod p)≠0 := by
      intro hz
      exact not_dvd_quotient_of_squarefree hp hs1 hc1 ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz)
    have hc20 : (c2 : ZMod p)≠0 := by
      intro hz
      exact not_dvd_quotient_of_squarefree hp hs2 hc2 ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz)
    have hred : IsSquare (c1*c2*d.2.2) := by
      apply isSquare_of_int_square_factor (p : ℤ) _ hp.ne_zero
      convert hsq using 1; rw [hc1,hc2]; ring
    have hn12 : ¬IsSquare ((c1*c2 : ℤ) : ZMod p) := by
      intro h12
      apply hn3
      have hredp : IsSquare ((c1*c2*d.2.2 : ℤ) : ZMod p) := hred.map (Int.castRingHom (ZMod p))
      have h12p : IsSquare ((c1 : ZMod p)*(c2 : ZMod p)) := by simpa only [Int.cast_mul] using h12
      have hprod : IsSquare ((d.2.2 : ZMod p)*((c1 : ZMod p)*(c2 : ZMod p))) := by
        convert hredp using 1; push_cast; ring
      exact isSquare_of_mul_square_right hprod h12p (mul_ne_zero hc10 hc20)
    exact splitCover_binary_obstruction_ramified d r2 r3 c1 c2 hc1 hc2 hr2 hn12 hn3r hlocal
  · have hd2 : ¬(p : ℤ)∣d.2.1 := by
      intro h2
      have hsq' : IsSquare (d.2.1*d.1*d.2.2) := by simpa only [mul_comm d.1 d.2.1] using hsq
      rcases squarefree_product_prime_parity d.2.1 d.1 d.2.2 hs2 hs1 hs3 hsq' h2 with h | h
      · exact hd1 h.1
      · exact hd30 h.2
    have hn12 : ¬IsSquare ((d.1*d.2.1 : ℤ) : ZMod p) := by
      intro h12
      apply hn3
      have hredp : IsSquare ((d.1*d.2.1*d.2.2 : ℤ) : ZMod p) := hsq.map (Int.castRingHom (ZMod p))
      have h12p : IsSquare ((d.1 : ZMod p)*(d.2.1 : ZMod p)) := by simpa only [Int.cast_mul] using h12
      have hprod : IsSquare ((d.2.2 : ZMod p)*((d.1 : ZMod p)*(d.2.1 : ZMod p))) := by
        convert hredp using 1; push_cast; ring
      apply isSquare_of_mul_square_right hprod h12p
      exact mul_ne_zero (fun hz => hd1 ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz))
        (fun hz => hd2 ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz))
    apply splitCover_binary_obstruction_unramified d r2 r3 _ hn12 hn3r hlocal
    exact (dvd_pow_self (p : ℤ) (by decide : 2≠0)).trans hr2


private theorem splitCover_swap {F : Type*} [CommRing F] (d1 d2 d3 r2 r3 : F)
    (h : SplitCoverSoluble d1 d2 d3 r2 r3) : SplitCoverSoluble d1 d3 d2 r3 r2 := by
  obtain ⟨z,⟨i,hi⟩,h1,h2⟩ := h
  refine ⟨![z 0,z 2,z 1,z 3],?_,?_,?_⟩
  · fin_cases i
    · exact ⟨0,by simpa using hi⟩
    · exact ⟨2,by simpa using hi⟩
    · exact ⟨1,by simpa using hi⟩
    · exact ⟨3,by simpa using hi⟩
  · simpa using h2
  · simpa using h1

/-- Interchanging the two later roots interchanges their covering coordinates. -/
theorem splitCover_everywhere_swap (d : ECFullTriple) (r2 r3 : ℤ)
    (h : SplitCoverEverywhereLocallySoluble d r2 r3) :
    SplitCoverEverywhereLocallySoluble (d.1,d.2.2,d.2.1) r3 r2 :=
  ⟨splitCover_swap _ _ _ _ _ h.1,fun p _ => splitCover_swap _ _ _ _ _ (h.2 p)⟩

/-- The symmetric necessary condition at primes dividing the second square
root difference. -/
theorem splitCover_second_isSquare_of_third_square {p : ℕ} [Fact p.Prime]
    (d : ECFullTriple) (r2 r3 : ℤ)
    (hs1 : Squarefree d.1) (hs2 : Squarefree d.2.1) (hs3 : Squarefree d.2.2)
    (hsq : IsSquare (d.1*d.2.1*d.2.2))
    (hr3 : (p : ℤ)^2∣r3) (hr2 : IsSquare (r2 : ZMod p))
    (hr20 : (r2 : ZMod p)≠0) (hd20 : ¬(p : ℤ)∣d.2.1)
    (hlocal : SplitCoverEverywhereLocallySoluble d r2 r3) :
    IsSquare (d.2.1 : ZMod p) := by
  apply splitCover_third_isSquare_of_first_square (d.1,d.2.2,d.2.1) r3 r2
    hs1 hs3 hs2 _ hr3 hr2 hr20 hd20 (splitCover_everywhere_swap d r2 r3 hlocal)
  convert hsq using 1; ring

/-- At a prime occurring exactly once in the difference of the root
differences, the first coefficient is square with the sign specified by
whether the two later coefficients ramify. -/
theorem splitCover_first_signed_isSquare_of_simple_difference {p : ℕ} [Fact p.Prime]
    (d : ECFullTriple) (r2 r3 : ℤ)
    (hs1 : Squarefree d.1) (hs2 : Squarefree d.2.1) (hs3 : Squarefree d.2.2)
    (hsq : IsSquare (d.1*d.2.1*d.2.2))
    (hr : (p : ℤ)∣r2-r3) (hrsq : ¬(p : ℤ)^2∣r2-r3)
    (hr2 : IsSquare (r2 : ZMod p)) (hr20 : (r2 : ZMod p)≠0)
    (hd10 : ¬(p : ℤ)∣d.1)
    (hlocal : SplitCoverEverywhereLocallySoluble d r2 r3) :
    IsSquare ((if (p : ℤ)∣d.2.1 then -d.1 else d.1 : ℤ) : ZMod p) := by
  split_ifs with hd2
  · have hprod : IsSquare ((-d.1*r2 : ℤ) : ZMod p) := by
      by_contra hn
      exact splitCover_binary_obstruction_later_ramified d r2 r3 hs2 hs3 hd2 hn hlocal
    apply isSquare_of_mul_square_right (b:=(r2 : ZMod p)) _ hr2 hr20
    simpa only [Int.cast_mul,Int.cast_neg] using hprod
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
      apply isSquare_of_mul_square_right hprod h23p
      exact mul_ne_zero (fun hz => hd2 ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz))
        (fun hz => hd3 ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz))
    exact splitCover_binary_obstruction_later_unramified d r2 r3 hr hrsq hd10 hn23 hlocal

end Z2Z4Rank6
