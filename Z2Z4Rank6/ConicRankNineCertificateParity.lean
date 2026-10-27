import Z2Z4Rank6.ConicRankNineCertificateData

/-! Exact 11-dimensional descent image certificate; Dujella–Peral Section 7.2, p. 19. -/
namespace Z2Z4Rank6.ConicRankNineCertificate
noncomputable section
set_option maxHeartbeats 3000000
local instance conicPrime2 : Fact (Nat.Prime 2) := ⟨by norm_num⟩
local instance conicPrime3 : Fact (Nat.Prime 3) := ⟨by norm_num⟩
local instance conicPrime5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩
local instance conicPrime11 : Fact (Nat.Prime 11) := ⟨by norm_num⟩
local instance conicPrime13 : Fact (Nat.Prime 13) := ⟨by norm_num⟩
local instance conicPrime17 : Fact (Nat.Prime 17) := ⟨by norm_num⟩
local instance conicPrime23 : Fact (Nat.Prime 23) := ⟨by norm_num⟩
local instance conicPrime53 : Fact (Nat.Prime 53) := ⟨by norm_num⟩
local instance conicPrime61 : Fact (Nat.Prime 61) := ⟨by norm_num⟩
local instance conicPrime193 : Fact (Nat.Prime 193) := ⟨by norm_num⟩

private theorem valuation_nat_zero_or_one {p n : ℕ} [Fact p.Prime]
    (hn : n≠0) (hp2 : ¬p^2∣n) : padicValNat p n=if p∣n then 1 else 0 := by
  split_ifs with hdiv
  · have hlo : 1≤padicValNat p n := by
      apply (padicValNat_dvd_iff_le hn).mp
      simpa only [pow_one] using hdiv
    have hhi : ¬2≤padicValNat p n := fun h => hp2 ((padicValNat_dvd_iff_le hn).mpr h)
    omega
  · exact padicValNat.eq_zero_of_not_dvd hdiv

noncomputable def parity : (RatSquareClassAdd×RatSquareClassAdd) →+ (Fin 11 → ZMod 2) where
  toFun q := ![squareClassSign q.1,squareClassValuation 2 q.1,squareClassValuation 3 q.1,squareClassValuation 5 q.1,squareClassValuation 11 q.1,squareClassValuation 13 q.1,squareClassValuation 23 q.1,squareClassValuation 53 q.1,squareClassValuation 61 q.1,squareClassValuation 17 q.2,squareClassValuation 193 q.2]
  map_zero' := by ext i; fin_cases i <;> simp
  map_add' q r := by ext i; fin_cases i <;> simp

theorem parity_values (i : Fin 11) : parity (squareclasses i)=parityVectors i := by
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
  have h8 := congrFun hm 8
  have h9 := congrFun hm 9
  have h10 := congrFun hm 10
  norm_num [Fin.sum_univ_succ,parityVectors] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  have hEven2 : (2 : ZMod 2)=0 := by decide
  have hEven4 : (4 : ZMod 2)=0 := by decide
  have hEven6 : (6 : ZMod 2)=0 := by decide
  have hEven8 : (8 : ZMod 2)=0 := by decide
  have hEven10 : (10 : ZMod 2)=0 := by decide
  have hEven12 : (12 : ZMod 2)=0 := by decide
  intro i
  fin_cases i
  · change n 0=0
    linear_combination (norm := skip) h1+h4+h5+h9+h10
    ring_nf
    repeat' first
      | rw [hEven2]
      | rw [hEven4]
      | rw [hEven6]
      | rw [hEven8]
      | rw [hEven10]
      | rw [hEven12]
      | rw [mul_zero]
      | rw [sub_zero]
      | rw [zero_sub]
      | rw [neg_zero]
  · change n 1=0
    linear_combination (norm := skip) h4+h5+h6+h7+h8+h9+h10
    ring_nf
    repeat' first
      | rw [hEven2]
      | rw [hEven4]
      | rw [hEven6]
      | rw [hEven8]
      | rw [hEven10]
      | rw [hEven12]
      | rw [mul_zero]
      | rw [sub_zero]
      | rw [zero_sub]
      | rw [neg_zero]
  · change n 2=0
    linear_combination (norm := skip) h1+h2+h3+h5+h6+h8+h9+h10
    ring_nf
    repeat' first
      | rw [hEven2]
      | rw [hEven4]
      | rw [hEven6]
      | rw [hEven8]
      | rw [hEven10]
      | rw [hEven12]
      | rw [mul_zero]
      | rw [sub_zero]
      | rw [zero_sub]
      | rw [neg_zero]
  · change n 3=0
    linear_combination (norm := skip) h0+h4+h9
    ring_nf
    repeat' first
      | rw [hEven2]
      | rw [hEven4]
      | rw [hEven6]
      | rw [hEven8]
      | rw [hEven10]
      | rw [hEven12]
      | rw [mul_zero]
      | rw [sub_zero]
      | rw [zero_sub]
      | rw [neg_zero]
  · change n 4=0
    linear_combination (norm := skip) h1+h2+h8+h9+h10
    ring_nf
    repeat' first
      | rw [hEven2]
      | rw [hEven4]
      | rw [hEven6]
      | rw [hEven8]
      | rw [hEven10]
      | rw [hEven12]
      | rw [mul_zero]
      | rw [sub_zero]
      | rw [zero_sub]
      | rw [neg_zero]
  · change n 5=0
    linear_combination (norm := skip) h2+h4+h6+h7+h8+h9+h10
    ring_nf
    repeat' first
      | rw [hEven2]
      | rw [hEven4]
      | rw [hEven6]
      | rw [hEven8]
      | rw [hEven10]
      | rw [hEven12]
      | rw [mul_zero]
      | rw [sub_zero]
      | rw [zero_sub]
      | rw [neg_zero]
  · change n 6=0
    linear_combination (norm := skip) h0+h2+h9
    ring_nf
    repeat' first
      | rw [hEven2]
      | rw [hEven4]
      | rw [hEven6]
      | rw [hEven8]
      | rw [hEven10]
      | rw [hEven12]
      | rw [mul_zero]
      | rw [sub_zero]
      | rw [zero_sub]
      | rw [neg_zero]
  · change n 7=0
    linear_combination (norm := skip) h0+h3+h5+h8+h10
    ring_nf
    repeat' first
      | rw [hEven2]
      | rw [hEven4]
      | rw [hEven6]
      | rw [hEven8]
      | rw [hEven10]
      | rw [hEven12]
      | rw [mul_zero]
      | rw [sub_zero]
      | rw [zero_sub]
      | rw [neg_zero]
  · change n 8=0
    linear_combination (norm := skip) h0+h2+h3+h4+h5+h9
    ring_nf
    repeat' first
      | rw [hEven2]
      | rw [hEven4]
      | rw [hEven6]
      | rw [hEven8]
      | rw [hEven10]
      | rw [hEven12]
      | rw [mul_zero]
      | rw [sub_zero]
      | rw [zero_sub]
      | rw [neg_zero]
  · change n 9=0
    linear_combination (norm := skip) h0+h1+h4+h5+h6+h7+h9+h10
    ring_nf
    repeat' first
      | rw [hEven2]
      | rw [hEven4]
      | rw [hEven6]
      | rw [hEven8]
      | rw [hEven10]
      | rw [hEven12]
      | rw [mul_zero]
      | rw [sub_zero]
      | rw [zero_sub]
      | rw [neg_zero]
  · change n 10=0
    linear_combination (norm := skip) h0+h2+h4+h6+h7+h8+h10
    ring_nf
    repeat' first
      | rw [hEven2]
      | rw [hEven4]
      | rw [hEven6]
      | rw [hEven8]
      | rw [hEven10]
      | rw [hEven12]
      | rw [mul_zero]
      | rw [sub_zero]
      | rw [zero_sub]
      | rw [neg_zero]

theorem ab_not_square : ¬IsSquare (A*B) := by
  intro hs
  have hzero := squareClass_eq_zero_of_isSquare hs
  have hraw := congrArg Prod.fst (raw_squareclasses (10 : Fin 11))
  change squareClass (A*B)=squareClass (representatives (10 : Fin 11)).1 at hraw
  have hval := congrFun (parity_values (10 : Fin 11)) (1 : Fin 11)
  change squareClassValuation 2 (squareClass (representatives (10 : Fin 11)).1)=1 at hval
  rw [←hraw,hzero,map_zero] at hval
  norm_num at hval

end
end Z2Z4Rank6.ConicRankNineCertificate
