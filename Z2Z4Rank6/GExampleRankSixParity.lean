import Z2Z4Rank6.GExampleRankSixData

/-! Eight independent complete-descent classes from the six printed points and torsion. -/
namespace Z2Z4Rank6.GExampleRankSix
noncomputable section
set_option maxHeartbeats 3000000

local instance gExamplePrime2 : Fact (Nat.Prime 2) := ⟨by norm_num⟩
local instance gExamplePrime17 : Fact (Nat.Prime 17) := ⟨by norm_num⟩
local instance gExamplePrime19 : Fact (Nat.Prime 19) := ⟨by norm_num⟩
local instance gExamplePrime23 : Fact (Nat.Prime 23) := ⟨by norm_num⟩
local instance gExamplePrime31 : Fact (Nat.Prime 31) := ⟨by norm_num⟩
local instance gExamplePrime43 : Fact (Nat.Prime 43) := ⟨by norm_num⟩
local instance gExamplePrime4001 : Fact (Nat.Prime 4001) := ⟨by norm_num⟩

private theorem valuation_nat_zero_or_one {p n : ℕ} [Fact p.Prime]
    (hn : n≠0) (hp2 : ¬p^2∣n) : padicValNat p n=if p∣n then 1 else 0 := by
  split_ifs with hdiv
  · have hlo : 1≤padicValNat p n := by
      apply (padicValNat_dvd_iff_le hn).mp
      simpa only [pow_one] using hdiv
    have hhi : ¬2≤padicValNat p n := fun h => hp2 ((padicValNat_dvd_iff_le hn).mpr h)
    omega
  · exact padicValNat.eq_zero_of_not_dvd hdiv

noncomputable def parity : (RatSquareClassAdd×RatSquareClassAdd) →+ (Fin 8 → ZMod 2) where
  toFun q := ![squareClassSign q.1,squareClassValuation 2 q.1,squareClassValuation 17 q.1,squareClassValuation 19 q.1,squareClassValuation 23 q.1,squareClassValuation 31 q.1,squareClassValuation 43 q.1,squareClassValuation 4001 q.2]
  map_zero' := by ext i; fin_cases i <;> simp
  map_add' q r := by ext i; fin_cases i <;> simp

theorem parity_values (i : Fin 8) : parity (squareclasses i)=parityVectors i := by
  ext j
  fin_cases i <;> fin_cases j <;>
    simp only [parity,squareclasses,representatives,parityVectors,
      AddMonoidHom.coe_mk,ZeroHom.coe_mk]
  all_goals simp (disch := norm_num) only [squareClassValuation_apply,squareClassSign_apply]
  all_goals norm_num [padicValRat_def,padicValInt]
  all_goals try rw [valuation_nat_zero_or_one (by decide) (by decide)]
  all_goals norm_num

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
  norm_num [Fin.sum_univ_succ,parityVectors] at h0 h1 h2 h3 h4 h5 h6 h7
  have hEven2 : (2 : ZMod 2)=0 := by decide
  have hEven4 : (4 : ZMod 2)=0 := by decide
  have hEven6 : (6 : ZMod 2)=0 := by decide
  have hEven8 : (8 : ZMod 2)=0 := by decide
  intro i
  fin_cases i
  · change n 0=0
    linear_combination (norm := skip) h0+h1+h2+h5+h6+h7
    ring_nf
    repeat' first
      | rw [hEven2]
      | rw [hEven4]
      | rw [hEven6]
      | rw [hEven8]
      | rw [mul_zero]
      | rw [sub_zero]
      | rw [zero_sub]
      | rw [neg_zero]
  · change n 1=0
    linear_combination (norm := skip) h1+h5
    ring_nf
    repeat' first
      | rw [hEven2]
      | rw [hEven4]
      | rw [hEven6]
      | rw [hEven8]
      | rw [mul_zero]
      | rw [sub_zero]
      | rw [zero_sub]
      | rw [neg_zero]
  · change n 2=0
    linear_combination (norm := skip) h3+h5
    ring_nf
    repeat' first
      | rw [hEven2]
      | rw [hEven4]
      | rw [hEven6]
      | rw [hEven8]
      | rw [mul_zero]
      | rw [sub_zero]
      | rw [zero_sub]
      | rw [neg_zero]
  · change n 3=0
    linear_combination (norm := skip) h1+h2+h4+h5
    ring_nf
    repeat' first
      | rw [hEven2]
      | rw [hEven4]
      | rw [hEven6]
      | rw [hEven8]
      | rw [mul_zero]
      | rw [sub_zero]
      | rw [zero_sub]
      | rw [neg_zero]
  · change n 4=0
    linear_combination (norm := skip) h1+h2+h3+h5
    ring_nf
    repeat' first
      | rw [hEven2]
      | rw [hEven4]
      | rw [hEven6]
      | rw [hEven8]
      | rw [mul_zero]
      | rw [sub_zero]
      | rw [zero_sub]
      | rw [neg_zero]
  · change n 5=0
    linear_combination (norm := skip) h1+h3+h4+h6
    ring_nf
    repeat' first
      | rw [hEven2]
      | rw [hEven4]
      | rw [hEven6]
      | rw [hEven8]
      | rw [mul_zero]
      | rw [sub_zero]
      | rw [zero_sub]
      | rw [neg_zero]
  · change n 6=0
    linear_combination (norm := skip) h1+h3+h4+h6+h7
    ring_nf
    repeat' first
      | rw [hEven2]
      | rw [hEven4]
      | rw [hEven6]
      | rw [hEven8]
      | rw [mul_zero]
      | rw [sub_zero]
      | rw [zero_sub]
      | rw [neg_zero]
  · change n 7=0
    exact h3

/-- The first coordinate of the four-torsion image has odd two-adic parity. -/
theorem ab_not_square : ¬IsSquare (A*B) := by
  intro hs
  have hzero := squareClass_eq_zero_of_isSquare hs
  have hraw := congrArg Prod.fst (raw_squareclasses (7 : Fin 8))
  change squareClass (A*B)=squareClass (representatives (7 : Fin 8)).1 at hraw
  have hval := congrFun (parity_values (7 : Fin 8)) (1 : Fin 8)
  change squareClassValuation 2 (squareClass (representatives (7 : Fin 8)).1)=1 at hval
  rw [←hraw,hzero,map_zero] at hval
  norm_num at hval

end
end Z2Z4Rank6.GExampleRankSix
