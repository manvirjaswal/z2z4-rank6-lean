module

public import Z2Z4Rank6.RankThreeSelmerData
public import Z2Z4Rank6.SplitRealConditions
public import Z2Z4Rank6.SplitSupportParametrization
public import Mathlib.Data.Finset.NatDivisors

@[expose] public section

/-! # Necessary local and support conditions at the printed m=14/3 fiber -/
namespace Z2Z4Rank6.RankThreeSelmer

set_option maxRecDepth 10000

private theorem first_prime_facts (p : ℕ) (hp : p∈([17,19,41,283] : List ℕ)) :
    (p : ℤ)^2∣r2 ∧ ¬(p : ℤ)∣r3 ∧ ¬(p : ℤ)∣r3*(r2-r3) := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl <;> norm_num [r2,r3,A,B]

private theorem second_prime_facts (p : ℕ) (hp : p∈([11,13,47] : List ℕ)) :
    (p : ℤ)^2∣r3 ∧ ¬(p : ℤ)∣r2 ∧ ¬(p : ℤ)∣r2*(r2-r3) := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl <;> norm_num [r2,r3,A,B]

private theorem difference_prime_facts (p : ℕ) (hp : p∈([3,7,73,139] : List ℕ)) :
    (p : ℤ)∣r2-r3 ∧ ¬(p : ℤ)^2∣r2-r3 ∧ ¬(p : ℤ)∣r2 ∧ ¬(p : ℤ)∣r2*r3 := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl <;> norm_num [r2,r3,A,B]

private theorem r2_square_mod (p : ℕ) : IsSquare (r2 : ZMod p) := by
  refine ⟨(A : ZMod p),?_⟩
  change (((A:ℤ)^2 : ℤ) : ZMod p)=(A : ZMod p)*(A : ZMod p)
  push_cast
  ring

private theorem r3_square_mod (p : ℕ) : IsSquare (r3 : ZMod p) := by
  refine ⟨(B : ZMod p),?_⟩
  change (((B:ℤ)^2 : ℤ) : ZMod p)=(B : ZMod p)*(B : ZMod p)
  push_cast
  ring

/-- Every everywhere locally soluble canonical covering at the
printed m=14/3 fiber passes the 11 proved odd-prime square tests. -/
theorem localTest_of_mem {d : ECFullTriple} (hd : d∈fullTwoSelmerTriples r2 r3) :
    localTest d=true := by
  rcases hd with ⟨hs1,hs2,hs3,hd1,hd2,hd3,hsq,hlocal⟩
  have first (p : ℕ) (hp : p∈([17,19,41,283] : List ℕ)) : modSquareTest p d.2.2=true := by
    have hpprime : p.Prime := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl <;> decide
    let : Fact p.Prime := ⟨hpprime⟩
    obtain ⟨hr2,hr3,hrange⟩ := first_prime_facts p hp
    apply (modSquareTest_iff p _).mpr
    apply splitCover_third_isSquare_of_first_square d r2 r3 hs1 hs2 hs3 hsq hr2
      (r3_square_mod p) _ _ hlocal
    · exact fun hz => hr3 ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz)
    · exact fun hh => hrange (hh.trans hd3)
  have second (p : ℕ) (hp : p∈([11,13,47] : List ℕ)) : modSquareTest p d.2.1=true := by
    have hpprime : p.Prime := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
      rcases hp with rfl | rfl | rfl <;> decide
    let : Fact p.Prime := ⟨hpprime⟩
    obtain ⟨hr3,hr2,hrange⟩ := second_prime_facts p hp
    apply (modSquareTest_iff p _).mpr
    apply splitCover_second_isSquare_of_third_square d r2 r3 hs1 hs2 hs3 hsq hr3
      (r2_square_mod p) _ _ hlocal
    · exact fun hz => hr2 ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz)
    · exact fun hh => hrange (hh.trans hd2)
  have diff (p : ℕ) (hp : p∈([3,7,73,139] : List ℕ)) :
      modSquareTest p (if (p : ℤ)∣d.2.1 then -d.1 else d.1)=true := by
    have hpprime : p.Prime := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl <;> decide
    let : Fact p.Prime := ⟨hpprime⟩
    obtain ⟨hr,hrsq,hr2,hrange⟩ := difference_prime_facts p hp
    apply (modSquareTest_iff p _).mpr
    apply splitCover_first_signed_isSquare_of_simple_difference d r2 r3 hs1 hs2 hs3 hsq
      hr hrsq (r2_square_mod p) _ _ hlocal
    · exact fun hz => hr2 ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz)
    · exact fun hh => hrange (hh.trans hd1)
  simp only [localTest,Bool.and_eq_true,List.all_eq_true]
  exact ⟨⟨first,second⟩,diff⟩

/-- The canonical coverings lie in the disjoint-prime block model;
the positivity of the second coefficient follows from the real place. -/
theorem exists_block_parameters_of_mem {d : ECFullTriple}
    (hd : d∈fullTwoSelmerTriples r2 r3) :
    ∃ a b c : ℕ, 0<a ∧ 0<b ∧ 0<c ∧ a∣A ∧ b∣B ∧ c∣C ∧
      ∃ ε : ℤ, (ε=1 ∨ ε = -1) ∧
        d.1=ε*(a:ℤ)*b ∧ d.2.1=(a:ℤ)*c ∧ d.2.2=ε*(b:ℤ)*c := by
  rcases hd with ⟨hs1,hs2,hs3,hd1,hd2,hd3,hsq,hlocal⟩
  have hAB : d.1.natAbs∣A*B := by
    have hh : d.1∣(((A*B : ℕ) : ℤ))^2 := by
      convert hd1 using 1; simp only [r2,r3,Nat.cast_mul]; ring
    exact Int.dvd_natCast.mp ((hs1.dvd_pow_iff_dvd (by decide : 2≠0)).mp hh)
  have hAC : d.2.1.natAbs∣A*C := by
    have hh : d.2.1∣(((A*C : ℕ) : ℤ))^6 :=
      hd2.trans (by norm_num [r2,r3,A,B,C])
    exact Int.dvd_natCast.mp ((hs2.dvd_pow_iff_dvd (by decide : 6≠0)).mp hh)
  have hBC : d.2.2.natAbs∣B*C := by
    have hh : d.2.2∣(((B*C : ℕ) : ℤ))^6 :=
      hd3.trans (by norm_num [r2,r3,A,B,C])
    exact Int.dvd_natCast.mp ((hs3.dvd_pow_iff_dvd (by decide : 6≠0)).mp hh)
  have hpos : 0<d.2.1 := splitCover_second_pos_of_ordered_differences d r2 r3
    (by norm_num [r3,B]) (by norm_num [r2,r3,A,B]) hs1.ne_zero hs2.ne_zero hs3.ne_zero hsq hlocal
  exact SplitSupport.exists_signed_block_parametrization A B C
    (by norm_num [A,B]) (by norm_num [A,C]) (by norm_num [B,C])
    d.1 d.2.1 d.2.2 hs1 hs2 hs3 hAB hAC hBC hpos hsq

end Z2Z4Rank6.RankThreeSelmer
