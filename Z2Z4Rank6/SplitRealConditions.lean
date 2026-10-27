module

public import Z2Z4Rank6.ECFullSelmerModel

@[expose] public section

/-! # The real sign condition for ordered split root differences -/
namespace Z2Z4Rank6

private theorem zero_of_negative_square_difference (a b c u v t : ℝ)
    (ha : a < 0) (hb : 0 < b) (hc : 0 < c)
    (h : a*u^2-b*v^2=c*t^2) : u=0 ∧ v=0 ∧ t=0 := by
  have h1 : a*u^2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg ha.le (sq_nonneg u)
  have h2 : 0 ≤ b*v^2 := mul_nonneg hb.le (sq_nonneg v)
  have h3 : 0 ≤ c*t^2 := mul_nonneg hc.le (sq_nonneg t)
  have hu : a*u^2 = 0 := by linarith
  have hv : b*v^2 = 0 := by linarith
  have ht : c*t^2 = 0 := by linarith
  exact ⟨sq_eq_zero_iff.mp ((mul_eq_zero.mp hu).resolve_left ha.ne),
    sq_eq_zero_iff.mp ((mul_eq_zero.mp hv).resolve_left hb.ne'),
    sq_eq_zero_iff.mp ((mul_eq_zero.mp ht).resolve_left hc.ne')⟩

theorem splitCover_real_negative_obstruction_for (d1 d2 d3 r2 r3 : ℝ)
    (hr3 : 0<r3) (hr23 : r3<r2) (hd2 : d2<0) (h13 : d1*d3<0) :
    ¬SplitCoverSoluble d1 d2 d3 r2 r3 := by
  rintro ⟨z,⟨i,hi⟩,h1,h2⟩
  rcases (mul_neg_iff.mp h13).symm with ⟨hd1,hd3⟩ | ⟨hd1,hd3⟩
  · have hdiff : d2*(z 1)^2-d3*(z 2)^2=(r2-r3)*(z 3)^2 := by linarith
    obtain ⟨hz1,hz2,hz3⟩ := zero_of_negative_square_difference _ _ _ _ _ _ hd2 hd3
      (sub_pos.mpr hr23) hdiff
    have hz0 : z 0=0 := by
      rw [hz1,hz3] at h1
      have hz : d1*(z 0)^2=0 := by simpa using h1.symm
      exact sq_eq_zero_iff.mp ((mul_eq_zero.mp hz).resolve_left hd1.ne)
    fin_cases i <;> simp_all
  · obtain ⟨hz1,hz0,hz3⟩ := zero_of_negative_square_difference _ _ _ _ _ _ hd2 hd1
      (lt_trans hr3 hr23) h1
    have hz2 : z 2=0 := by
      rw [hz0,hz3] at h2
      have hz : d3*(z 2)^2=0 := by simpa using h2
      exact sq_eq_zero_iff.mp ((mul_eq_zero.mp hz).resolve_left hd3.ne)
    fin_cases i <;> simp_all

/-- In the canonical nonzero square-product model, ordered positive root
differences force the second covering coefficient to be positive. -/
theorem splitCover_second_pos_of_ordered_differences (d : ECFullTriple) (r2 r3 : ℤ)
    (hr3 : 0<r3) (hr23 : r3<r2)
    (hd1 : d.1≠0) (hd2 : d.2.1≠0) (hd3 : d.2.2≠0)
    (hsq : IsSquare (d.1*d.2.1*d.2.2))
    (hlocal : SplitCoverEverywhereLocallySoluble d r2 r3) : 0<d.2.1 := by
  by_contra hn
  have hd2neg : d.2.1<0 := lt_of_le_of_ne (by omega) hd2
  have hprod : 0<d.1*d.2.1*d.2.2 := by
    obtain ⟨t,ht⟩ := hsq
    have hnonneg : 0≤d.1*d.2.1*d.2.2 := by rw [ht]; exact mul_self_nonneg _
    exact lt_of_le_of_ne hnonneg (mul_ne_zero (mul_ne_zero hd1 hd2) hd3).symm
  have h13 : d.1*d.2.2<0 := by
    have hh : 0<(d.1*d.2.2)*d.2.1 := by convert hprod using 1; ring
    exact (mul_pos_iff.mp hh).resolve_left (by intro h; exact hd2neg.not_gt h.2) |>.1
  exact splitCover_real_negative_obstruction_for _ _ _ _ _
    (by exact_mod_cast hr3) (by exact_mod_cast hr23)
    (by exact_mod_cast hd2neg) (by exact_mod_cast h13) hlocal.1

end Z2Z4Rank6
