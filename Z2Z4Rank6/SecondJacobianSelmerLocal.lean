module

public import Z2Z4Rank6.SecondJacobianSelmerModel

@[expose] public section

/-! Necessary local square tests for the second-Jacobian coverings. -/
namespace Z2Z4Rank6.SecondJacobianSelmer

local instance prime3 : Fact (Nat.Prime 3) := ⟨by decide⟩
local instance prime5 : Fact (Nat.Prime 5) := ⟨by decide⟩
local instance prime7 : Fact (Nat.Prime 7) := ⟨by decide⟩
local instance prime11 : Fact (Nat.Prime 11) := ⟨by decide⟩
local instance prime17 : Fact (Nat.Prime 17) := ⟨by decide⟩
local instance prime19 : Fact (Nat.Prime 19) := ⟨by decide⟩
local instance prime23 : Fact (Nat.Prime 23) := ⟨by decide⟩
local instance prime29 : Fact (Nat.Prime 29) := ⟨by decide⟩

private theorem third_test {p : ℕ} [Fact p.Prime] (d : ECFullTriple)
    (hd : d ∈ fullTwoSelmerTriples A B)
    (hp : ¬(p:ℤ)∣radical3) (hA : (p:ℤ)^2∣A)
    (hB : IsSquare (B:ZMod p)) (hB0 : (B:ZMod p)≠0) :
    IsSquare (normalizedProduct p d.1 d.2.1 : ZMod p) := by
  have hn := not_dvd_of_support (support_radicals d hd).2.2 hp
  apply normalizedProduct_square d hd hp
  obtain ⟨hs1,hs2,hs3,_,_,_,hsq,hloc⟩ := hd
  exact splitCover_third_isSquare_of_first_square d A B hs1 hs2 hs3 hsq hA hB hB0
    hn hloc

private theorem second_test {p : ℕ} [Fact p.Prime] (d : ECFullTriple)
    (hd : d ∈ fullTwoSelmerTriples A B)
    (hp : ¬(p:ℤ)∣radical2) (hB : (p:ℤ)^2∣B)
    (hA : IsSquare (A:ZMod p)) (hA0 : (A:ZMod p)≠0) :
    IsSquare (d.2.1 : ZMod p) := by
  have hn := not_dvd_of_support (support_radicals d hd).2.1 hp
  obtain ⟨hs1,hs2,hs3,_,_,_,hsq,hloc⟩ := hd
  exact splitCover_second_isSquare_of_third_square d A B hs1 hs2 hs3 hsq hB hA hA0 hn hloc

private theorem first_cycle_test {p : ℕ} [Fact p.Prime] (d : ECFullTriple)
    (hd : d ∈ fullTwoSelmerTriples A B)
    (hp : ¬(p:ℤ)∣radical1) (hD : (p:ℤ)^2∣B-A)
    (hA : IsSquare (-A:ZMod p)) (hA0 : (-A:ZMod p)≠0) :
    IsSquare (d.1 : ZMod p) := by
  have hn := not_dvd_of_support (support_radicals d hd).1 hp
  obtain ⟨hs1,hs2,hs3,_,_,_,hsq,hloc⟩ := hd
  apply splitCover_third_isSquare_of_first_square (d.2.1,d.2.2,d.1) (B-A) (-A)
    hs2 hs3 hs1 _ hD (by simpa only [Int.cast_neg] using hA)
    (by simpa only [Int.cast_neg] using hA0) hn (cycle_local d A B hloc)
  convert hsq using 1; ring

/-- The eight tests bound everywhere locally soluble coverings. -/
def PairTests (a b : ℤ) : Prop :=
  0<b ∧ IsSquare (normalizedProduct 3 a b : ZMod 3) ∧
  IsSquare (b:ZMod 7) ∧ IsSquare (normalizedProduct 11 a b : ZMod 11) ∧
  IsSquare (normalizedProduct 19 a b : ZMod 19) ∧ IsSquare (b:ZMod 23) ∧
  IsSquare (a:ZMod 5) ∧ IsSquare (a:ZMod 17) ∧ IsSquare (a:ZMod 29)

instance pairTestsDecidable (a b : ℤ) : Decidable (PairTests a b) := by
  unfold PairTests; infer_instance

theorem necessary_pair_tests (d : ECFullTriple) (hd : d ∈ fullTwoSelmerTriples A B) :
    PairTests d.1 d.2.1 := by
  refine ⟨second_positive d hd,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · apply third_test d hd (by norm_num [radical3]) (by norm_num [A])
    · decide +kernel
    · decide +kernel
  · apply second_test d hd (by norm_num [radical2]) (by norm_num [B])
    · decide +kernel
    · decide +kernel
  · apply third_test d hd (by norm_num [radical3]) (by norm_num [A])
    · decide +kernel
    · decide +kernel
  · apply third_test d hd (by norm_num [radical3]) (by norm_num [A])
    · decide +kernel
    · decide +kernel
  · apply second_test d hd (by norm_num [radical2]) (by norm_num [B])
    · decide +kernel
    · decide +kernel
  · apply first_cycle_test d hd (by norm_num [radical1]) (by norm_num [A,B])
    · decide +kernel
    · decide +kernel
  · apply first_cycle_test d hd (by norm_num [radical1]) (by norm_num [A,B])
    · decide +kernel
    · decide +kernel
  · have hn := not_dvd_of_support (support_radicals d hd).1 (by norm_num [radical1] : ¬(29:ℤ)∣radical1)
    have hh := splitCover_first_signed_isSquare_of_simple_difference (p:=29) d A B
      hd.1 hd.2.1 hd.2.2.1 hd.2.2.2.2.2.2.1
      (by norm_num [A,B]) (by norm_num [A,B]) (by decide +kernel) (by decide +kernel)
      hn hd.2.2.2.2.2.2.2
    split_ifs at hh with hb
    · have hminus : IsSquare (-1:ZMod 29) := by decide +kernel
      have hm := hminus.mul hh
      simpa only [Int.cast_neg,neg_one_mul,neg_neg] using hm
    · exact hh

end Z2Z4Rank6.SecondJacobianSelmer
