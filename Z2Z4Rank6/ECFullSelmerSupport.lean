import Z2Z4Rank6.ECFullSelmerData
import Mathlib.NumberTheory.Divisors

/-! # The canonical divisor supports in the full two-descent certificate -/

namespace Z2Z4Rank6

private theorem signed_divisor_mem (N : ℕ) (hn : N ≠ 0) (pos : List ℕ) (signed : List ℤ)
    (hdivs : N.divisors = pos.toFinset)
    (hsigns : ∀ n ∈ pos, (n : ℤ) ∈ signed ∧ -(n : ℤ) ∈ signed)
    (d : ℤ) (hd : d ∣ (N : ℤ)) : d ∈ signed := by
  have hmem : d.natAbs ∈ N.divisors := Nat.mem_divisors.mpr ⟨Int.dvd_natCast.mp hd,hn⟩
  rw [hdivs, List.mem_toFinset] at hmem
  have hp := hsigns d.natAbs hmem
  rcases Int.natAbs_eq d with hd | hd
  · exact hd ▸ hp.1
  · exact hd ▸ hp.2

theorem ecFull_second_squarefree_divisor_mem (d : ℤ) (hd : Squarefree d)
    (hdiv : d ∣ 178605) : d ∈ ecFullSecondDivisors := by
  have hdpow : d ∣ (105 : ℤ)^6 := hdiv.trans (by norm_num)
  have hd105 : d ∣ 105 := (hd.dvd_pow_iff_dvd (by norm_num : (6 : ℕ) ≠ 0)).mp hdpow
  apply signed_divisor_mem 105 (by norm_num) [1,3,5,7,15,21,35,105]
    ecFullSecondDivisors (by decide +kernel) (by decide +kernel) d hd105

theorem ecFull_third_squarefree_divisor_mem (d : ℤ) (hd : Squarefree d)
    (hdiv : d ∣ 118580) : d ∈ ecFullThirdDivisors := by
  have hdpow : d ∣ (770 : ℤ)^2 := hdiv.trans (by norm_num)
  have hd770 : d ∣ 770 := (hd.dvd_pow_iff_dvd (by norm_num : (2 : ℕ) ≠ 0)).mp hdpow
  apply signed_divisor_mem 770 (by norm_num) [1,2,5,7,10,11,14,22,35,55,70,77,110,154,385,770]
    ecFullThirdDivisors (by decide +kernel) (by decide +kernel) d hd770

end Z2Z4Rank6
