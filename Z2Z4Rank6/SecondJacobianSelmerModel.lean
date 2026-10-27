module

public import Z2Z4Rank6.SecondJacobianBasic
public import Z2Z4Rank6.SplitLegendreConditions

@[expose] public section

/-!
# Elementary necessary conditions for the second Jacobian descent

The split equation is E_{393129,25921}. We bound its complete
descent classes by signed divisor pairs and proved local square conditions.
-/

namespace Z2Z4Rank6.SecondJacobianSelmer

def A : ℤ := 154550410641
def B : ℤ := 671898241
def radical1 : ℤ := 100947
def radical2 : ℤ := 141885040110
def radical3 : ℤ := 36433000730

/-- Remove the possible common ramified prime before taking a residue class. -/
def normalizedProduct (p : ℕ) (a b : ℤ) : ℤ :=
  if (p:ℤ) ∣ a then (a/(p:ℤ))*(b/(p:ℤ)) else a*b

theorem support_radicals (d : ECFullTriple) (hd : d ∈ fullTwoSelmerTriples A B) :
    d.1 ∣ radical1 ∧ d.2.1 ∣ radical2 ∧ d.2.2 ∣ radical3 := by
  obtain ⟨hs1,hs2,hs3,hd1,hd2,hd3,_,_⟩ := hd
  refine ⟨?_,?_,?_⟩
  · apply (hs1.dvd_pow_iff_dvd (by decide : (4:ℕ) ≠ 0)).mp
    exact hd1.trans (by norm_num [A,B,radical1])
  · apply (hs2.dvd_pow_iff_dvd (by decide : (4:ℕ) ≠ 0)).mp
    exact hd2.trans (by norm_num [A,B,radical2])
  · apply (hs3.dvd_pow_iff_dvd (by decide : (4:ℕ) ≠ 0)).mp
    exact hd3.trans (by norm_num [A,B,radical3])

theorem not_dvd_of_support {p d N : ℤ} (hd : d ∣ N) (hp : ¬p ∣ N) : ¬p ∣ d :=
  fun h => hp (h.trans hd)

theorem pair_parity {p : ℕ} [Fact p.Prime] (d : ECFullTriple)
    (hd : d ∈ fullTwoSelmerTriples A B) (hp : ¬(p:ℤ) ∣ radical3) :
    ((p:ℤ) ∣ d.1 ↔ (p:ℤ) ∣ d.2.1) := by
  have hn3 := not_dvd_of_support (support_radicals d hd).2.2 hp
  obtain ⟨hs1,hs2,hs3,_,_,_,hsq,_⟩ := hd
  constructor
  · intro h1
    rcases squarefree_product_prime_parity d.1 d.2.1 d.2.2 hs1 hs2 hs3 hsq h1 with h | h
    · exact h.1
    · exact False.elim (hn3 h.2)
  · intro h2
    have hsq' : IsSquare (d.2.1*d.1*d.2.2) := by simpa only [mul_comm d.1 d.2.1] using hsq
    rcases squarefree_product_prime_parity d.2.1 d.1 d.2.2 hs2 hs1 hs3 hsq' h2 with h | h
    · exact h.1
    · exact False.elim (hn3 h.2)

private theorem isSquare_of_int_square_factor (p a : ℤ) (hp : p ≠ 0)
    (hs : IsSquare (p^2*a)) : IsSquare a := by
  apply Rat.isSquare_intCast_iff.mp
  have hpQ : (p:ℚ) ≠ 0 := by exact_mod_cast hp
  have hq : IsSquare ((p^2*a:ℤ):ℚ) := hs.map (Int.castRingHom ℚ)
  have hz := hq.div (IsSquare.mul_self (p:ℚ))
  convert hz using 1; push_cast; field_simp

/-- The third coefficient's local square condition gives a square test on
the first two coefficients alone. This avoids choosing a gcd-normalized third
representative in the finite certificate. -/
theorem normalizedProduct_square {p : ℕ} [Fact p.Prime] (d : ECFullTriple)
    (hd : d ∈ fullTwoSelmerTriples A B) (hp : ¬(p:ℤ) ∣ radical3)
    (h3 : IsSquare (d.2.2 : ZMod p)) :
    IsSquare ((normalizedProduct p d.1 d.2.1 : ℤ):ZMod p) := by
  have hpar := pair_parity d hd hp
  have hn3 := not_dvd_of_support (support_radicals d hd).2.2 hp
  have hsq := hd.2.2.2.2.2.2.1
  have hs : IsSquare (normalizedProduct p d.1 d.2.1*d.2.2) := by
    unfold normalizedProduct
    split_ifs with ha
    · have hb := hpar.mp ha
      have hea : d.1=(p:ℤ)*(d.1/(p:ℤ)) := by
        symm; rw [mul_comm,Int.ediv_mul_cancel ha]
      have heb : d.2.1=(p:ℤ)*(d.2.1/(p:ℤ)) := by
        symm; rw [mul_comm,Int.ediv_mul_cancel hb]
      apply isSquare_of_int_square_factor (p:ℤ) _
        (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
      convert hsq using 1
      conv_rhs => rw [hea,heb]
      ring
    · exact hsq
  have hmod := hs.map (Int.castRingHom (ZMod p))
  have h30 : (d.2.2 : ZMod p) ≠ 0 := by
    intro hz
    exact hn3 ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz)
  have hm : IsSquare ((normalizedProduct p d.1 d.2.1 : ZMod p)*(d.2.2:ZMod p)) := by
    change IsSquare (((normalizedProduct p d.1 d.2.1*d.2.2:ℤ):ZMod p)) at hmod
    simpa only [Int.cast_mul] using hmod
  have hquot := hm.div h3
  convert hquot using 1
  field_simp

theorem cycle_local (d : ECFullTriple) (r2 r3 : ℤ)
    (h : SplitCoverEverywhereLocallySoluble d r2 r3) :
    SplitCoverEverywhereLocallySoluble (d.2.1,d.2.2,d.1) (r3-r2) (-r2) :=
  splitCover_everywhere_swap _ _ _
    (SplitCoverEverywhereLocallySoluble.swap_first_second d r2 r3 h)

private theorem zero_of_neg_square_difference (a b c u v t : ℝ)
    (ha : a < 0) (hb : 0 < b) (hc : 0 < c)
    (h : a*u^2-b*v^2=c*t^2) : u=0 ∧ v=0 ∧ t=0 := by
  have h1 : a*u^2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg ha.le (sq_nonneg u)
  have h2 : 0 ≤ b*v^2 := mul_nonneg hb.le (sq_nonneg v)
  have h3 : 0 ≤ c*t^2 := mul_nonneg hc.le (sq_nonneg t)
  have hu : a*u^2=0 := by linarith
  have hv : b*v^2=0 := by linarith
  have ht : c*t^2=0 := by linarith
  exact ⟨sq_eq_zero_iff.mp ((mul_eq_zero.mp hu).resolve_left ha.ne),
    sq_eq_zero_iff.mp ((mul_eq_zero.mp hv).resolve_left hb.ne'),
    sq_eq_zero_iff.mp ((mul_eq_zero.mp ht).resolve_left hc.ne')⟩

theorem real_negative_obstruction (d1 d2 d3 r2 r3 : ℝ)
    (hd2 : d2 < 0) (h13 : d1*d3 < 0) (hr3 : 0 < r3) (hr23 : r3 < r2) :
    ¬SplitCoverSoluble d1 d2 d3 r2 r3 := by
  rintro ⟨z,⟨i,hi⟩,h1,h2⟩
  rcases (mul_neg_iff.mp h13).symm with ⟨hd1,hd3⟩ | ⟨hd1,hd3⟩
  · have hdiff : d2*(z 1)^2-d3*(z 2)^2=(r2-r3)*(z 3)^2 := by linarith
    obtain ⟨hz1,hz2,hz3⟩ := zero_of_neg_square_difference _ _ _ _ _ _ hd2 hd3
      (sub_pos.mpr hr23) hdiff
    have hz0 : z 0=0 := by
      rw [hz1,hz3] at h1
      have hz : d1*(z 0)^2=0 := by simpa using h1.symm
      exact sq_eq_zero_iff.mp ((mul_eq_zero.mp hz).resolve_left hd1.ne)
    fin_cases i <;> simp_all
  · obtain ⟨hz1,hz0,hz3⟩ := zero_of_neg_square_difference _ _ _ _ _ _ hd2 hd1
      (hr3.trans hr23) h1
    have hz2 : z 2=0 := by
      rw [hz0,hz3] at h2
      have hz : d3*(z 2)^2=0 := by simpa using h2
      exact sq_eq_zero_iff.mp ((mul_eq_zero.mp hz).resolve_left hd3.ne)
    fin_cases i <;> simp_all

theorem second_positive (d : ECFullTriple) (hd : d ∈ fullTwoSelmerTriples A B) : 0<d.2.1 := by
  obtain ⟨hs1,hs2,hs3,_,_,_,hsq,hloc⟩ := hd
  by_contra hn
  have hb : d.2.1<0 := lt_of_le_of_ne (le_of_not_gt hn) hs2.ne_zero
  have hp : 0<d.1*d.2.1*d.2.2 :=
    lt_of_le_of_ne hsq.nonneg (mul_ne_zero (mul_ne_zero hs1.ne_zero hs2.ne_zero) hs3.ne_zero).symm
  have hac : d.1*d.2.2<0 := by
    have hp' : 0<(d.1*d.2.2)*d.2.1 := by nlinarith only [hp]
    rcases mul_pos_iff.mp hp' with h | h
    · exact False.elim (not_lt_of_ge hb.le h.2)
    · exact h.1
  exact real_negative_obstruction (d.1:ℝ) (d.2.1:ℝ) (d.2.2:ℝ) A B
    (by exact_mod_cast hb) (by exact_mod_cast hac) (by norm_num [B])
    (by norm_num [A,B]) hloc.1

end Z2Z4Rank6.SecondJacobianSelmer
