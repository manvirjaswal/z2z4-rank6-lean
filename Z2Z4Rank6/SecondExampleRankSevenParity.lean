import Z2Z4Rank6.SecondExampleRankSevenData

/-! Nine independent complete-descent vectors for the second example.
Source: Jaswal, unnumbered rank-seven assertion after Theorem 8.1,
DOI 10.5281/zenodo.23437117; exact representatives match pd_sec8d.out. -/
namespace Z2Z4Rank6.SecondExampleRankSeven
noncomputable section

local instance secondExampleRankSevenPrime2 : Fact (Nat.Prime 2) := ⟨by norm_num⟩
local instance secondExampleRankSevenPrime3 : Fact (Nat.Prime 3) := ⟨by norm_num⟩
local instance secondExampleRankSevenPrime5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩
local instance secondExampleRankSevenPrime11 : Fact (Nat.Prime 11) := ⟨by norm_num⟩
local instance secondExampleRankSevenPrime17 : Fact (Nat.Prime 17) := ⟨by norm_num⟩
local instance secondExampleRankSevenPrime13 : Fact (Nat.Prime 13) := ⟨by norm_num⟩
local instance secondExampleRankSevenPrime89 : Fact (Nat.Prime 89) := ⟨by norm_num⟩
local instance secondExampleRankSevenPrime137 : Fact (Nat.Prime 137) := ⟨by norm_num⟩

private theorem valuation_nat_zero_or_one {p n : ℕ} [Fact p.Prime]
    (hn : n≠0) (hp2 : ¬p^2∣n) : padicValNat p n=if p∣n then 1 else 0 := by
  split_ifs with hdiv
  · have hlo : 1≤padicValNat p n := by
      apply (padicValNat_dvd_iff_le hn).mp
      simpa only [pow_one] using hdiv
    have hhi : ¬2≤padicValNat p n := fun h => hp2 ((padicValNat_dvd_iff_le hn).mpr h)
    omega
  · exact padicValNat.eq_zero_of_not_dvd hdiv

noncomputable def parity : (RatSquareClassAdd×RatSquareClassAdd) →+ (Fin 9 → ZMod 2) where
  toFun q := ![squareClassSign q.1,squareClassValuation 2 q.1,
    squareClassValuation 3 q.1,squareClassValuation 5 q.1,
    squareClassValuation 11 q.1,squareClassValuation 17 q.1,
    squareClassValuation 13 q.2,squareClassValuation 89 q.2,squareClassValuation 137 q.2]
  map_zero' := by ext i; fin_cases i <;> simp
  map_add' q r := by ext i; fin_cases i <;> simp

theorem parity_values (i : Fin 9) : parity (squareclasses i)=parityVectors i := by
  ext j
  fin_cases i <;> fin_cases j <;>
    simp only [parity,squareclasses,representatives,parityVectors,
      AddMonoidHom.coe_mk,ZeroHom.coe_mk]
  all_goals simp (disch := norm_num) only [squareClassValuation_apply,squareClassSign_apply]
  all_goals norm_num [padicValRat_def,padicValInt]
  all_goals try rw [valuation_nat_zero_or_one (by decide) (by decide)]
  all_goals norm_num

/-- The seven point images and two torsion images are F₂-independent. -/
theorem squareclasses_independent : LinearIndependent (ZMod 2) squareclasses := by
  apply Fintype.linearIndependent_iff.mpr
  intro n hn
  have hm : ∑ i,n i • parityVectors i=0 := by
    have hh := congrArg parity hn
    simpa only [map_sum,ZMod.map_smul,parity_values,map_zero] using hh
  have h0 := congrFun hm 0
  have h1 := congrFun hm 1
  have h2 := congrFun hm 2
  have h3 := congrFun hm 3
  have h4 := congrFun hm 4
  have h5 := congrFun hm 5
  have h6 := congrFun hm 6
  have h7 := congrFun hm 7
  have h8 := congrFun hm 8
  norm_num [Fin.sum_univ_succ,parityVectors] at h0 h1 h2 h3 h4 h5 h6 h7 h8
  have hTwo : (2 : ZMod 2)=0 := by decide
  have hFour : (4 : ZMod 2)=0 := by decide
  have hSix : (6 : ZMod 2)=0 := by decide
  intro i
  fin_cases i
  · change n 0=0
    linear_combination (norm := skip) h0+h1+h3+h4+h5+h8
    ring_nf
    repeat' first
      | rw [hTwo]
      | rw [hFour]
      | rw [hSix]
      | rw [mul_zero]
      | rw [sub_zero]
      | rw [zero_sub]
      | rw [neg_zero]
  · change n 1=0
    linear_combination (norm := skip) h0+h1+h2+h3+h4+h5+h6+h7+h8
    ring_nf
    repeat' first
      | rw [hTwo]
      | rw [hFour]
      | rw [hSix]
      | rw [mul_zero]
      | rw [sub_zero]
      | rw [zero_sub]
      | rw [neg_zero]
  · change n 2=0
    linear_combination (norm := skip) h0+h6
    ring_nf
    repeat' first
      | rw [hTwo]
      | rw [hFour]
      | rw [hSix]
      | rw [mul_zero]
      | rw [sub_zero]
      | rw [zero_sub]
      | rw [neg_zero]
  · change n 3=0
    linear_combination (norm := skip) h2+h5
    ring_nf
    repeat' first
      | rw [hTwo]
      | rw [hFour]
      | rw [hSix]
      | rw [mul_zero]
      | rw [sub_zero]
      | rw [zero_sub]
      | rw [neg_zero]
  · change n 4=0
    linear_combination (norm := skip) h1+h5
    ring_nf
    repeat' first
      | rw [hTwo]
      | rw [hFour]
      | rw [hSix]
      | rw [mul_zero]
      | rw [sub_zero]
      | rw [zero_sub]
      | rw [neg_zero]
  · change n 5=0
    linear_combination (norm := skip) h1+h3+h5+h7+h8
    ring_nf
    repeat' first
      | rw [hTwo]
      | rw [hFour]
      | rw [hSix]
      | rw [mul_zero]
      | rw [sub_zero]
      | rw [zero_sub]
      | rw [neg_zero]
  · change n 6=0
    linear_combination (norm := skip) h1+h5+h7+h8
    ring_nf
    repeat' first
      | rw [hTwo]
      | rw [hFour]
      | rw [hSix]
      | rw [mul_zero]
      | rw [sub_zero]
      | rw [zero_sub]
      | rw [neg_zero]
  · change n 7=0
    linear_combination (norm := skip) h2+h3+h5+h6+h7+h8
    ring_nf
    repeat' first
      | rw [hTwo]
      | rw [hFour]
      | rw [hSix]
      | rw [mul_zero]
      | rw [sub_zero]
      | rw [zero_sub]
      | rw [neg_zero]
  · change n 8=0
    linear_combination (norm := skip) h0+h1+h2+h4+h6
    ring_nf
    repeat' first
      | rw [hTwo]
      | rw [hFour]
      | rw [hSix]
      | rw [mul_zero]
      | rw [sub_zero]
      | rw [zero_sub]
      | rw [neg_zero]

/-- The first coordinate of the four-torsion image has odd two-adic parity. -/
theorem ab_not_square : ¬IsSquare (A*B) := by
  intro hs
  have hzero := squareClass_eq_zero_of_isSquare hs
  have hraw := congrArg Prod.fst (raw_squareclasses (8 : Fin 9))
  change squareClass (A*B)=squareClass (representatives (8 : Fin 9)).1 at hraw
  have hval := congrFun (parity_values (8 : Fin 9)) (1 : Fin 9)
  change squareClassValuation 2 (squareClass (representatives (8 : Fin 9)).1)=1 at hval
  rw [←hraw,hzero,map_zero] at hval
  norm_num at hval

end
end Z2Z4Rank6.SecondExampleRankSeven
