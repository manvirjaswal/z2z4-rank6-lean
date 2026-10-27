import Z2Z4Rank6.GenericSplitSelmerSieve
import Mathlib.NumberTheory.LegendreSymbol.Basic

/-!
# Binary quadratic obstructions for split two-coverings

These elementary p and p² arguments apply to arbitrary integral root
differences. Nonsquare binary forms force two coordinates to vanish modulo p;
the resulting four-coordinate vanishing contradicts projective primitivity.
-/

namespace Z2Z4Rank6

/-- A binary quadratic equality with nonsquare coefficient product is
anisotropic over any field. -/
theorem binary_zero_of_not_isSquare {F : Type*} [Field F]
    (a b x y : F) (hn : ¬ IsSquare (a*b)) (h : a*x^2=b*y^2) : x=0 ∧ y=0 := by
  have ha : a ≠ 0 := by intro hh; simp [hh] at hn
  by_cases hy : y=0
  · refine ⟨?_,hy⟩
    rw [hy,zero_pow (by decide),mul_zero] at h
    exact (sq_eq_zero_iff).mp (mul_eq_zero.mp h |>.resolve_left ha)
  · exfalso
    apply hn
    refine ⟨a*x/y,?_⟩
    field_simp
    linear_combination -h

/-- A nonsquare binary form modulo p forces both integral variables to be
multiples of p. -/
theorem prime_dvd_binary_of_not_isSquare {p : ℕ} [Fact p.Prime]
    (a b x y : ℤ) (hn : ¬ IsSquare ((a*b : ℤ) : ZMod p))
    (h : (p : ℤ) ∣ a*x^2-b*y^2) : (p : ℤ) ∣ x ∧ (p : ℤ) ∣ y := by
  have hm : (a : ZMod p)*(x : ZMod p)^2=(b : ZMod p)*(y : ZMod p)^2 := by
    have hz : ((a*x^2-b*y^2 : ℤ) : ZMod p)=0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h
    push_cast at hz
    exact sub_eq_zero.mp hz
  have hn' : ¬ IsSquare ((a : ZMod p)*(b : ZMod p)) := by simpa only [Int.cast_mul] using hn
  obtain ⟨hx,hy⟩ := binary_zero_of_not_isSquare _ _ _ _ hn' hm
  exact ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hx,
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hy⟩

private theorem cancel_prime_square {p w : ℤ} (hp : p ≠ 0)
    (h : p^2 ∣ p*w) : p ∣ w := by
  have h' : p*p ∣ p*w := by simpa only [pow_two] using h
  exact (mul_dvd_mul_iff_left hp).mp h'

private theorem prime_square_dvd_of_dvd {p x : ℤ} (h : p ∣ x) : p^2 ∣ x^2 :=
  pow_dvd_pow_of_dvd h 2

/-- When p divides the first root difference, two nonsquare binary forms
already obstruct a primitive covering solution modulo p. -/
theorem splitCover_binary_obstruction_unramified {p : ℕ} [Fact p.Prime]
    (d : ECFullTriple) (r2 r3 : ℤ)
    (hr2 : (p : ℤ) ∣ r2)
    (hn12 : ¬ IsSquare ((d.1*d.2.1 : ℤ) : ZMod p))
    (hn3 : ¬ IsSquare ((d.2.2*r3 : ℤ) : ZMod p)) :
    ¬ SplitCoverEverywhereLocallySoluble d r2 r3 := by
  intro hlocal
  obtain ⟨z,⟨i,hi⟩,he1,he2⟩ := splitCover_primitive_int_residues d r2 r3 (hlocal.2 p)
  have hpp : (p : ℤ) ∣ (p : ℤ)^2 := dvd_pow_self _ (by decide)
  have h1 : (p : ℤ) ∣ d.2.1*(z 1)^2-d.1*(z 0)^2 := by
    exact (dvd_sub_left (dvd_mul_of_dvd_left hr2 _)).mp (hpp.trans he1)
  have hn21 : ¬ IsSquare ((d.2.1*d.1 : ℤ) : ZMod p) := by
    simpa only [mul_comm] using hn12
  obtain ⟨hb,ha⟩ := prime_dvd_binary_of_not_isSquare d.2.1 d.1 (z 1) (z 0) hn21 h1
  have h2 : (p : ℤ) ∣ d.2.2*(z 2)^2-r3*(z 3)^2 := by
    have hda : (p : ℤ) ∣ d.1*(z 0)^2 := dvd_mul_of_dvd_right (dvd_pow ha (by decide)) _
    have hh : (p : ℤ) ∣ (d.2.2*(z 2)^2-r3*(z 3)^2)-d.1*(z 0)^2 := by
      convert hpp.trans he2 using 1; ring
    exact (dvd_sub_left hda).mp hh
  obtain ⟨hc,ht⟩ := prime_dvd_binary_of_not_isSquare d.2.2 r3 (z 2) (z 3) hn3 h2
  fin_cases i <;> exact hi (by assumption)

/-- If p divides both first coefficients and p² divides their root
difference, divide the first quadric by p before testing its binary form. -/
theorem splitCover_binary_obstruction_ramified {p : ℕ} [Fact p.Prime]
    (d : ECFullTriple) (r2 r3 c1 c2 : ℤ)
    (hd1 : d.1=(p : ℤ)*c1) (hd2 : d.2.1=(p : ℤ)*c2)
    (hr2 : (p : ℤ)^2 ∣ r2)
    (hn12 : ¬ IsSquare ((c1*c2 : ℤ) : ZMod p))
    (hn3 : ¬ IsSquare ((d.2.2*r3 : ℤ) : ZMod p)) :
    ¬ SplitCoverEverywhereLocallySoluble d r2 r3 := by
  intro hlocal
  obtain ⟨z,⟨i,hi⟩,he1,he2⟩ := splitCover_primitive_int_residues d r2 r3 (hlocal.2 p)
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hpp : (p : ℤ) ∣ (p : ℤ)^2 := dvd_pow_self _ (by decide)
  have h1 : (p : ℤ) ∣ c2*(z 1)^2-c1*(z 0)^2 := by
    have hh : (p : ℤ)^2 ∣ d.2.1*(z 1)^2-d.1*(z 0)^2 :=
      (dvd_sub_left (dvd_mul_of_dvd_left hr2 _)).mp he1
    apply cancel_prime_square hp0
    convert hh using 1; rw [hd1,hd2]; ring
  have hn21 : ¬ IsSquare ((c2*c1 : ℤ) : ZMod p) := by simpa only [mul_comm] using hn12
  obtain ⟨hb,ha⟩ := prime_dvd_binary_of_not_isSquare c2 c1 (z 1) (z 0) hn21 h1
  have h2 : (p : ℤ) ∣ d.2.2*(z 2)^2-r3*(z 3)^2 := by
    have hda : (p : ℤ) ∣ d.1*(z 0)^2 := by rw [hd1]; exact dvd_mul_right _ _ |>.mul_right _
    have hh : (p : ℤ) ∣ (d.2.2*(z 2)^2-r3*(z 3)^2)-d.1*(z 0)^2 := by
      convert hpp.trans he2 using 1; ring
    exact (dvd_sub_left hda).mp hh
  obtain ⟨hc,ht⟩ := prime_dvd_binary_of_not_isSquare d.2.2 r3 (z 2) (z 3) hn3 h2
  fin_cases i <;> exact hi (by assumption)


/-- If both later coefficients contain p, an anisotropic first reduction
forces the remaining variables to vanish modulo p by squarefreeness. -/
theorem splitCover_binary_obstruction_later_ramified {p : ℕ} [Fact p.Prime]
    (d : ECFullTriple) (r2 r3 : ℤ)
    (hs2 : Squarefree d.2.1) (hs3 : Squarefree d.2.2)
    (hd2 : (p : ℤ) ∣ d.2.1)
    (hn : ¬ IsSquare ((-d.1*r2 : ℤ) : ZMod p)) :
    ¬ SplitCoverEverywhereLocallySoluble d r2 r3 := by
  intro hlocal
  obtain ⟨z,⟨i,hi⟩,he1,he2⟩ := splitCover_primitive_int_residues d r2 r3 (hlocal.2 p)
  have hp : Prime (p : ℤ) := Int.prime_iff_natAbs_prime.mpr (by simpa using (Fact.out : p.Prime))
  have hpp : (p : ℤ) ∣ (p : ℤ)^2 := dvd_pow_self _ (by decide)
  have h1 : (p : ℤ) ∣ -d.1*(z 0)^2-r2*(z 3)^2 := by
    have hbase := hpp.trans he1
    have hd : (p : ℤ) ∣ d.2.1*(z 1)^2 := dvd_mul_of_dvd_left hd2 _
    convert dvd_sub hbase hd using 1; ring
  obtain ⟨ha,ht⟩ := prime_dvd_binary_of_not_isSquare (-d.1) r2 (z 0) (z 3) hn h1
  have hb : (p : ℤ) ∣ z 1 := by
    have hd : (p : ℤ)^2 ∣ d.1*(z 0)^2+r2*(z 3)^2 := dvd_add
      (dvd_mul_of_dvd_right (prime_square_dvd_of_dvd ha) _)
      (dvd_mul_of_dvd_right (prime_square_dvd_of_dvd ht) _)
    have hh : (p : ℤ)^2 ∣ d.2.1*(z 1)^2 := by
      apply (dvd_sub_left hd).mp
      convert he1 using 1; ring
    have hz : (p : ℤ) ∣ (z 1)^2 :=
      Squarefree.dvd_of_squarefree_of_mul_dvd_mul_right hs2 (by simpa only [pow_two] using hh)
    exact hp.dvd_of_dvd_pow hz
  have hc : (p : ℤ) ∣ z 2 := by
    have hd : (p : ℤ)^2 ∣ d.1*(z 0)^2+r3*(z 3)^2 := dvd_add
      (dvd_mul_of_dvd_right (prime_square_dvd_of_dvd ha) _)
      (dvd_mul_of_dvd_right (prime_square_dvd_of_dvd ht) _)
    have hh : (p : ℤ)^2 ∣ d.2.2*(z 2)^2 := by
      apply (dvd_sub_left hd).mp
      convert he2 using 1; ring
    have hz : (p : ℤ) ∣ (z 2)^2 :=
      Squarefree.dvd_of_squarefree_of_mul_dvd_mul_right hs3 (by simpa only [pow_two] using hh)
    exact hp.dvd_of_dvd_pow hz
  fin_cases i <;> exact hi (by assumption)

/-- At a prime occurring exactly once in the difference of the root
differences, an anisotropic later binary form gives a p² obstruction. -/
theorem splitCover_binary_obstruction_later_unramified {p : ℕ} [Fact p.Prime]
    (d : ECFullTriple) (r2 r3 : ℤ)
    (hr : (p : ℤ) ∣ r2-r3) (hrsq : ¬ (p : ℤ)^2 ∣ r2-r3)
    (hd1 : ¬ (p : ℤ) ∣ d.1)
    (hn : ¬ IsSquare ((d.2.1*d.2.2 : ℤ) : ZMod p)) :
    ¬ SplitCoverEverywhereLocallySoluble d r2 r3 := by
  intro hlocal
  obtain ⟨z,⟨i,hi⟩,he1,he2⟩ := splitCover_primitive_int_residues d r2 r3 (hlocal.2 p)
  have hp : Prime (p : ℤ) := Int.prime_iff_natAbs_prime.mpr (by simpa using (Fact.out : p.Prime))
  have hp0 : (p : ℤ) ≠ 0 := hp.ne_zero
  have hpp : (p : ℤ) ∣ (p : ℤ)^2 := dvd_pow_self _ (by decide)
  have hdiff : (p : ℤ)^2 ∣ d.2.1*(z 1)^2-d.2.2*(z 2)^2-(r2-r3)*(z 3)^2 := by
    convert dvd_sub he1 he2 using 1; ring
  have h1 : (p : ℤ) ∣ d.2.1*(z 1)^2-d.2.2*(z 2)^2 :=
    (dvd_sub_left (dvd_mul_of_dvd_left hr _)).mp (hpp.trans hdiff)
  obtain ⟨hb,hc⟩ := prime_dvd_binary_of_not_isSquare d.2.1 d.2.2 (z 1) (z 2) hn h1
  have ht : (p : ℤ) ∣ z 3 := by
    have hcoef : (p : ℤ)^2 ∣ d.2.1*(z 1)^2-d.2.2*(z 2)^2 := dvd_sub
      (dvd_mul_of_dvd_right (prime_square_dvd_of_dvd hb) _)
      (dvd_mul_of_dvd_right (prime_square_dvd_of_dvd hc) _)
    have hprod : (p : ℤ)^2 ∣ (r2-r3)*(z 3)^2 := (dvd_sub_right hcoef).mp hdiff
    obtain ⟨D,hD⟩ := hr
    have hD0 : ¬ (p : ℤ) ∣ D := by
      rintro ⟨c,hc⟩
      apply hrsq
      rw [hD,hc]
      exact ⟨c,by ring⟩
    have hz : (p : ℤ) ∣ D*(z 3)^2 := by
      apply cancel_prime_square hp0
      simpa only [hD,mul_assoc] using hprod
    exact hp.dvd_of_dvd_pow ((hp.dvd_or_dvd hz).resolve_left hD0)
  have ha : (p : ℤ) ∣ z 0 := by
    have hcoef : (p : ℤ)^2 ∣ d.2.1*(z 1)^2-r2*(z 3)^2 := dvd_sub
      (dvd_mul_of_dvd_right (prime_square_dvd_of_dvd hb) _)
      (dvd_mul_of_dvd_right (prime_square_dvd_of_dvd ht) _)
    have hh : (p : ℤ) ∣ d.1*(z 0)^2 := by
      have he : (p : ℤ)^2 ∣ (d.2.1*(z 1)^2-r2*(z 3)^2)-d.1*(z 0)^2 := by
        convert he1 using 1; ring
      exact hpp.trans ((dvd_sub_right hcoef).mp he)
    exact hp.dvd_of_dvd_pow ((hp.dvd_or_dvd hh).resolve_left hd1)
  fin_cases i <;> exact hi (by assumption)

end Z2Z4Rank6
