import Z2Z4Rank6.ECDescentCertificates
import Mathlib.Algebra.Squarefree.Basic

/-!
# Squarefree divisor lists for the E_C descent

The integer representatives required by the two-isogeny algorithm of
Cremona, *Algorithms for Modular Elliptic Curves*, Section 3.6, Method 1,
for the rank-one curve in Jaswal, Lemma 4.1(b), DOI 10.5281/zenodo.23437117.
-/

namespace Z2Z4Rank6

def ecDescentDivisors : List ℤ :=
  [-66,-33,-22,-11,-6,-3,-2,-1,1,2,3,6,11,22,33,66]

def ecIsogenousDescentDivisors : List ℤ := [-35,-7,-5,-1,1,5,7,35]

def ecDescentSurvivors : List ℤ := [-66,-11,-6,-1,1,6,11,66]

theorem ec_squarefree_divisor_mem (d : ℤ) (hd : Squarefree d) (hdiv : d ∣ 352836) :
    d ∈ ecDescentDivisors := by
  have hdpow : d ∣ (66 : ℤ)^6 := hdiv.trans (by norm_num)
  have hd66 : d ∣ 66 := (hd.dvd_pow_iff_dvd (by norm_num : (6 : ℕ) ≠ 0)).mp hdpow
  have hbound : d.natAbs ≤ 66 := Int.natAbs_le_of_dvd_ne_zero hd66 (by norm_num)
  have hlo : -66 ≤ d := by omega
  have hhi : d ≤ 66 := by omega
  unfold ecDescentDivisors
  interval_cases d <;> norm_num at hd66 <;> norm_num

theorem ecIsogenous_squarefree_divisor_mem (d : ℤ) (hd : Squarefree d)
    (hdiv : d ∣ 60025) : d ∈ ecIsogenousDescentDivisors := by
  have hdpow : d ∣ (35 : ℤ)^4 := hdiv.trans (by norm_num)
  have hd35 : d ∣ 35 := (hd.dvd_pow_iff_dvd (by norm_num : (4 : ℕ) ≠ 0)).mp hdpow
  have hbound : d.natAbs ≤ 35 := Int.natAbs_le_of_dvd_ne_zero hd35 (by norm_num)
  have hlo : -35 ≤ d := by omega
  have hhi : d ≤ 35 := by omega
  unfold ecIsogenousDescentDivisors
  interval_cases d <;> norm_num at hd35 <;> norm_num

theorem ec_divisor_survivor_or_mod5_obstruction (d : ℤ)
    (hd : d ∈ ecDescentDivisors) :
    d ∈ ecDescentSurvivors ∨ ¬PrimitiveQuarticSolubleMod 5 d 1213 (352836/d) := by
  by_cases hs : d ∈ ecDescentSurvivors
  · exact Or.inl hs
  · right
    apply ec_mod5_obstruction
    simp only [ecDescentDivisors, List.mem_cons, List.not_mem_nil, or_false] at hd
    simp only [ecDescentSurvivors, List.mem_cons, List.not_mem_nil, or_false, not_or] at hs
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all

end Z2Z4Rank6
