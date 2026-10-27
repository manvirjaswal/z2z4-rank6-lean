import Z2Z4Rank6.TwistSelmerDataLocal

/-!
# A high-precision split-covering obstruction

The p⁵ primitive-congruence argument below handles a root-difference gap
p⁴S without enumerating projective points modulo p⁵. It is used in the q₁
twist certificate of Proposition 5.2, M. Jaswal,
DOI 10.5281/zenodo.23437117. The theorem concerns arbitrary split coverings.
-/

namespace Z2Z4Rank6

private theorem high_difference_ramified_step (p d2 d3 b c R : ℤ) (hp : Prime p)
    (hs3 : Squarefree d3) (hd3 : p∣d3) (hd2 : ¬p∣d2)
    (hR : p^2∣R) (he : p^2∣d3*c^2-d2*b^2-R) : p∣b ∧ p∣c := by
  have hsum : p^2∣d3*c^2-d2*b^2 := (dvd_sub_left hR).mp he
  have hpp : p∣p^2 := dvd_pow_self _ (by decide)
  have hb : p∣b := by
    have hprod : p∣d2*b^2 :=
      (dvd_sub_right (dvd_mul_of_dvd_left hd3 _)).mp (hpp.trans hsum)
    exact hp.dvd_of_dvd_pow ((hp.dvd_or_dvd hprod).resolve_left hd2)
  have hc : p∣c := by
    have hdb : p^2∣d2*b^2 := dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd hb 2) _
    have hdc : p^2∣d3*c^2 := (dvd_sub_left hdb).mp hsum
    have hh : p∣c^2 := Squarefree.dvd_of_squarefree_of_mul_dvd_mul_right hs3
      (by simpa only [pow_two] using hdc)
    exact hp.dvd_of_dvd_pow hh
  exact ⟨hb,hc⟩

/-- If the root differences differ by p⁴S and the third covering
coefficient is ramified while the second is a unit, local solubility
forces −d₂S to be a square modulo p. The squarefreeness assumptions concern
only the two coefficients used to force primitivity. -/
theorem splitCover_high_difference_isSquare {p : ℕ} [Fact p.Prime]
    (d : ECFullTriple) (r2 r3 S : ℤ)
    (hs1 : Squarefree d.1) (hs3 : Squarefree d.2.2)
    (hd3 : (p : ℤ)∣d.2.2) (hd2 : ¬(p : ℤ)∣d.2.1)
    (hr : r3-r2=(p : ℤ)^4*S)
    (hlocal : SplitCoverEverywhereLocallySoluble d r2 r3) :
    IsSquare ((-d.2.1*S : ℤ) : ZMod p) := by
  by_contra hn
  obtain ⟨z,⟨i,hi⟩,he1,he2⟩ :=
    TwistSelmer.primitive_int_residues_pow 5 (by decide) d r2 r3 (hlocal.2 p)
  have hp : Prime (p : ℤ) := Int.prime_iff_natAbs_prime.mpr (by simpa using (Fact.out : p.Prime))
  have hp0 : (p : ℤ)≠0 := hp.ne_zero
  have hdiff : (p : ℤ)^5∣d.2.2*(z 2)^2-d.2.1*(z 1)^2-(p : ℤ)^4*S*(z 3)^2 := by
    convert dvd_sub he2 he1 using 1
    rw [←hr]
    ring
  have h25 : (p : ℤ)^2∣(p : ℤ)^5 := pow_dvd_pow _ (by decide)
  obtain ⟨hb,hc⟩ := high_difference_ramified_step (p : ℤ) d.2.1 d.2.2
    (z 1) (z 2) ((p : ℤ)^4*S*(z 3)^2) hp hs3 hd3 hd2
    ⟨(p : ℤ)^2*S*(z 3)^2,by ring⟩ (h25.trans hdiff)
  obtain ⟨b1,hb1⟩ := hb
  obtain ⟨c1,hc1⟩ := hc
  have hdiff3 : (p : ℤ)^3∣d.2.2*c1^2-d.2.1*b1^2-(p : ℤ)^2*S*(z 3)^2 := by
    apply (mul_dvd_mul_iff_left (pow_ne_zero 2 hp0)).mp
    convert hdiff using 1
    · ring
    · simp only [hb1,hc1]
      ring
  have h23 : (p : ℤ)^2∣(p : ℤ)^3 := pow_dvd_pow _ (by decide)
  obtain ⟨hbb,hcc⟩ := high_difference_ramified_step (p : ℤ) d.2.1 d.2.2
    b1 c1 ((p : ℤ)^2*S*(z 3)^2) hp hs3 hd3 hd2
    ⟨S*(z 3)^2,by ring⟩ (h23.trans hdiff3)
  obtain ⟨b2,hb2⟩ := hbb
  obtain ⟨c2,hc2⟩ := hcc
  have hzb : z 1=(p : ℤ)^2*b2 := by rw [hb1,hb2]; ring
  have hzc : z 2=(p : ℤ)^2*c2 := by rw [hc1,hc2]; ring
  have hlast : (p : ℤ)∣d.2.2*c2^2-d.2.1*b2^2-S*(z 3)^2 := by
    apply (mul_dvd_mul_iff_left (pow_ne_zero 4 hp0)).mp
    convert hdiff using 1
    · ring
    · simp only [hzb,hzc]
      ring
  have hbinary : (p : ℤ)∣-d.2.1*b2^2-S*(z 3)^2 := by
    convert dvd_sub hlast (dvd_mul_of_dvd_left hd3 (c2^2)) using 1; ring
  obtain ⟨_,ht⟩ := prime_dvd_binary_of_not_isSquare (-d.2.1) S b2 (z 3) hn hbinary
  have ha : (p : ℤ)∣z 0 := by
    have hcoef : (p : ℤ)^2∣d.2.1*(z 1)^2-r2*(z 3)^2 := dvd_sub
      (dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd ⟨b1,hb1⟩ 2) _)
      (dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd ht 2) _)
    have he : (p : ℤ)^2∣(d.2.1*(z 1)^2-r2*(z 3)^2)-d.1*(z 0)^2 := by
      convert h25.trans he1 using 1; ring
    have hh : (p : ℤ)^2∣d.1*(z 0)^2 := (dvd_sub_right hcoef).mp he
    have hz : (p : ℤ)∣(z 0)^2 := Squarefree.dvd_of_squarefree_of_mul_dvd_mul_right hs1
      (by simpa only [pow_two] using hh)
    exact hp.dvd_of_dvd_pow hz
  have hb : (p : ℤ)∣z 1 := ⟨b1,hb1⟩
  have hc : (p : ℤ)∣z 2 := ⟨c1,hc1⟩
  fin_cases i <;> exact hi (by assumption)

/-- The same necessary condition with the two later roots interchanged. -/
theorem splitCover_high_difference_swap_isSquare {p : ℕ} [Fact p.Prime]
    (d : ECFullTriple) (r2 r3 S : ℤ)
    (hs1 : Squarefree d.1) (hs2 : Squarefree d.2.1)
    (hd2 : (p : ℤ)∣d.2.1) (hd3 : ¬(p : ℤ)∣d.2.2)
    (hr : r3-r2=(p : ℤ)^4*S)
    (hlocal : SplitCoverEverywhereLocallySoluble d r2 r3) :
    IsSquare ((d.2.2*S : ℤ) : ZMod p) := by
  have hr' : r2-r3=(p : ℤ)^4*(-S) := by linear_combination -hr
  have h := splitCover_high_difference_isSquare (d.1,d.2.2,d.2.1) r3 r2 (-S)
    hs1 hs2 hd2 hd3 hr' (splitCover_everywhere_swap d r2 r3 hlocal)
  simpa only [neg_mul_neg] using h

end Z2Z4Rank6
