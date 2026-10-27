module

public import Z2Z4Rank6.GJacobianData
public import Mathlib.NumberTheory.Divisors

@[expose] public section
/-! Canonical signed squarefree divisor supports for J_G, Proposition 7.2(a). -/
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

theorem gJacobian_squarefree_divisor_1 (d : ℤ) (hd : Squarefree d)
    (hdiv : d ∣ 23532201) : d ∈ gJacobianD1 := by
  have hdpow : d ∣ (231 : ℤ)^4 := hdiv.trans (by norm_num)
  have hdR : d ∣ 231 := (hd.dvd_pow_iff_dvd (by norm_num : (4 : ℕ) ≠ 0)).mp hdpow
  apply signed_divisor_mem 231 (by norm_num) [1,3,7,11,21,33,77,231]
    gJacobianD1 (by decide +kernel) (by decide +kernel) d hdR

theorem gJacobian_squarefree_divisor_2 (d : ℤ) (hd : Squarefree d)
    (hdiv : d ∣ 72527400) : d ∈ gJacobianD2 := by
  have hdpow : d ∣ (12210 : ℤ)^4 := hdiv.trans (by norm_num)
  have hdR : d ∣ 12210 := (hd.dvd_pow_iff_dvd (by norm_num : (4 : ℕ) ≠ 0)).mp hdpow
  apply signed_divisor_mem 12210 (by norm_num) [1,2,3,5,6,10,11,15,22,30,33,37,55,66,74,110,111,165,185,222,330,370,407,555,814,1110,1221,2035,2442,4070,6105,12210]
    gJacobianD2 (by decide +kernel) (by decide +kernel) d hdR

theorem gJacobian_squarefree_divisor_3 (d : ℤ) (hd : Squarefree d)
    (hdiv : d ∣ 17767400) : d ∈ gJacobianD3 := by
  have hdpow : d ∣ (2590 : ℤ)^4 := hdiv.trans (by norm_num)
  have hdR : d ∣ 2590 := (hd.dvd_pow_iff_dvd (by norm_num : (4 : ℕ) ≠ 0)).mp hdpow
  apply signed_divisor_mem 2590 (by norm_num) [1,2,5,7,10,14,35,37,70,74,185,259,370,518,1295,2590]
    gJacobianD3 (by decide +kernel) (by decide +kernel) d hdR

end Z2Z4Rank6
