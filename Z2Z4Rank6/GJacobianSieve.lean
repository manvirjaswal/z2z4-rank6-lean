import Z2Z4Rank6.GJacobianData
import Z2Z4Rank6.SplitQuadraticObstructions

/-!
# Sparse finite obstructions for the Jacobian of G

The tests at 3,5,7 are exact anisotropic binary-form tests with primitive p²
lifts, avoiding enumeration of four coordinates modulo large prime powers.
They apply to the homogeneous coverings.
-/
namespace Z2Z4Rank6

local instance gJacobianSievePrimeThree : Fact (Nat.Prime 3) := ⟨by decide⟩
local instance gJacobianSievePrimeFive : Fact (Nat.Prime 5) := ⟨by decide⟩
local instance gJacobianSievePrimeSeven : Fact (Nat.Prime 7) := ⟨by decide⟩

def gJacobianBinaryBad (p:ℕ)[Fact p.Prime](d:ECFullTriple)(r2 r3:ℤ):Bool := decide
  (((p:ℤ)∣r2 ∧ ¬IsSquare ((d.1*d.2.1:ℤ):ZMod p) ∧ ¬IsSquare ((d.2.2*r3:ℤ):ZMod p)) ∨
   ((p:ℤ)^2∣r2 ∧ d.1=(p:ℤ)*(d.1/(p:ℤ)) ∧ d.2.1=(p:ℤ)*(d.2.1/(p:ℤ)) ∧
     ¬IsSquare (((d.1/(p:ℤ))*(d.2.1/(p:ℤ)):ℤ):ZMod p) ∧
     ¬IsSquare ((d.2.2*r3:ℤ):ZMod p)))

theorem gJacobian_binary_bad_not_local (p:ℕ)[Fact p.Prime]
    (d:ECFullTriple)(r2 r3:ℤ)(h:gJacobianBinaryBad p d r2 r3=true):
    ¬SplitCoverEverywhereLocallySoluble d r2 r3 := by
  rw [gJacobianBinaryBad,decide_eq_true_eq] at h
  rcases h with ⟨hr,h12,h3⟩ | ⟨hr,hd1,hd2,h12,h3⟩
  · exact splitCover_binary_obstruction_unramified d r2 r3 hr h12 h3
  · exact splitCover_binary_obstruction_ramified d r2 r3 (d.1/(p:ℤ)) (d.2.1/(p:ℤ))
      hd1 hd2 hr h12 h3

theorem gJacobian_binary_good_of_local (p:ℕ)[Fact p.Prime]
    (d:ECFullTriple)(r2 r3:ℤ)(h:SplitCoverEverywhereLocallySoluble d r2 r3):
    gJacobianBinaryBad p d r2 r3=false := by
  by_contra hn
  exact gJacobian_binary_bad_not_local p d r2 r3 (Bool.eq_true_of_not_eq_false hn) h

private theorem swap_later_cover {K:Type*}[Field K]
    (d1 d2 d3 r2 r3:K)(h:SplitCoverSoluble d1 d2 d3 r2 r3):
    SplitCoverSoluble d1 d3 d2 r3 r2 := by
  obtain ⟨z,⟨i,hi⟩,h1,h2⟩ := h
  refine ⟨![z 0,z 2,z 1,z 3],?_,h2,h1⟩
  fin_cases i
  · exact ⟨0,hi⟩
  · exact ⟨2,hi⟩
  · exact ⟨1,hi⟩
  · exact ⟨3,hi⟩

theorem gJacobian_swap_later_local (d:ECFullTriple)(r2 r3:ℤ)
    (h:SplitCoverEverywhereLocallySoluble d r2 r3):
    SplitCoverEverywhereLocallySoluble (d.1,d.2.2,d.2.1) r3 r2 := by
  constructor
  · exact swap_later_cover _ _ _ _ _ h.1
  · intro p hp
    exact swap_later_cover _ _ _ _ _ (h.2 p)

theorem gJacobian_cycle_local (d:ECFullTriple)(r2 r3:ℤ)
    (h:SplitCoverEverywhereLocallySoluble d r2 r3):
    SplitCoverEverywhereLocallySoluble (d.2.1,d.2.2,d.1) (r3-r2) (-r2) := by
  exact gJacobian_swap_later_local (d.2.1,d.1,d.2.2) (-r2) (r3-r2)
    (SplitCoverEverywhereLocallySoluble.swap_first_second d r2 r3 h)

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

theorem gJacobian_real_negative_obstruction (d1 d2 d3 : ℝ)
    (hd2 : d2 < 0) (h13 : d1*d3 < 0) :
    ¬ SplitCoverSoluble d1 d2 d3 9801 2401 := by
  rintro ⟨z,⟨i,hi⟩,h1,h2⟩
  rcases (mul_neg_iff.mp h13).symm with ⟨hd1,hd3⟩ | ⟨hd1,hd3⟩
  · have hdiff : d2*(z 1)^2-d3*(z 2)^2=7400*(z 3)^2 := by linarith
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
