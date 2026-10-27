module

public import Z2Z4Rank6.ECFullSelmerModel

@[expose] public section

/-! # The real obstruction in the full two-descent certificate -/

namespace Z2Z4Rank6

private theorem zero_of_neg_square_difference (a b c u v t : ℝ)
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

theorem splitCover_real_negative_obstruction (d1 d2 d3 : ℝ)
    (hd2 : d2 < 0) (h13 : d1*d3 < 0) :
    ¬ SplitCoverSoluble d1 d2 d3 729 484 := by
  rintro ⟨z,⟨i,hi⟩,h1,h2⟩
  rcases (mul_neg_iff.mp h13).symm with ⟨hd1,hd3⟩ | ⟨hd1,hd3⟩
  · have hdiff : d2*(z 1)^2-d3*(z 2)^2=245*(z 3)^2 := by linarith
    obtain ⟨hz1,hz2,hz3⟩ := zero_of_neg_square_difference _ _ _ _ _ _ hd2 hd3
      (by norm_num) hdiff
    have hz0 : z 0 = 0 := by
      rw [hz1,hz3] at h1
      have hz : d1*(z 0)^2=0 := by simpa using h1.symm
      exact sq_eq_zero_iff.mp ((mul_eq_zero.mp hz).resolve_left hd1.ne)
    fin_cases i <;> simp_all
  · obtain ⟨hz1,hz0,hz3⟩ := zero_of_neg_square_difference _ _ _ _ _ _ hd2 hd1
      (by norm_num) h1
    have hz2 : z 2 = 0 := by
      rw [hz0,hz3] at h2
      have hz : d3*(z 2)^2=0 := by simpa using h2
      exact sq_eq_zero_iff.mp ((mul_eq_zero.mp hz).resolve_left hd3.ne)
    fin_cases i <;> simp_all

end Z2Z4Rank6
