import Z2Z4Rank6.RankThreeSelmerNecessary

/-! # The structured canonical covering candidates at m=14/3 -/
namespace Z2Z4Rank6.RankThreeSelmer

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

private theorem a_divisors : A.divisors=aDivisors.toFinset := by
  rw [show A=17*19*41*283 by decide]
  simp only [Nat.divisors_mul,(show Nat.Prime 17 by norm_num).divisors,
    (show Nat.Prime 19 by norm_num).divisors,(show Nat.Prime 41 by norm_num).divisors,
    (show Nat.Prime 283 by norm_num).divisors]
  decide +kernel

private theorem b_divisors : B.divisors=bDivisors.toFinset := by
  rw [show B=11*13*47*311 by decide]
  simp only [Nat.divisors_mul,(show Nat.Prime 11 by norm_num).divisors,
    (show Nat.Prime 13 by norm_num).divisors,(show Nat.Prime 47 by norm_num).divisors,
    (show Nat.Prime 311 by norm_num).divisors]
  decide +kernel

private theorem c_divisors : C.divisors=cDivisors.toFinset := by
  rw [C]
  simp only [Nat.divisors_mul,(show Nat.Prime 2 by norm_num).divisors,
    (show Nat.Prime 3 by norm_num).divisors,(show Nat.Prime 5 by norm_num).divisors,
    (show Nat.Prime 7 by norm_num).divisors,(show Nat.Prime 73 by norm_num).divisors,
    (show Nat.Prime 139 by norm_num).divisors,(show Nat.Prime 11353 by norm_num).divisors]
  decide +kernel

/-- The block-support theorem reduces all locally soluble coverings
to 65536 structured candidates, without a huge Cartesian divisor product. -/
theorem exists_rawChunk_of_mem {d : ECFullTriple} (hd : d∈fullTwoSelmerTriples r2 r3) :
    ∃ a ∈ aDivisors, d∈rawChunk a := by
  obtain ⟨a,b,c,ha0,hb0,hc0,ha,hb,hc,ε,hε,hd1,hd2,hd3⟩ :=
    exists_block_parameters_of_mem hd
  have halist : a∈aDivisors := by
    have hh : a∈A.divisors := Nat.mem_divisors.mpr ⟨ha,by decide⟩
    rwa [a_divisors,List.mem_toFinset] at hh
  have hblist : b∈bDivisors := by
    have hh : b∈B.divisors := Nat.mem_divisors.mpr ⟨hb,by decide⟩
    rwa [b_divisors,List.mem_toFinset] at hh
  have hclist : c∈cDivisors := by
    have hh : c∈C.divisors := Nat.mem_divisors.mpr ⟨hc,by decide⟩
    rwa [c_divisors,List.mem_toFinset] at hh
  have hbblocks : b∈bBlocks.flatten := by
    rw [show bBlocks.flatten=bDivisors by decide +kernel]
    exact hblist
  obtain ⟨bs,hbs,hbmem⟩ := List.mem_flatten.mp hbblocks
  refine ⟨a,halist,List.mem_flatMap.mpr ⟨bs,hbs,?_⟩⟩
  apply List.mem_flatMap.mpr
  refine ⟨(b:ℤ),List.mem_flatMap.mpr ⟨b,hbmem,by simp⟩,
    List.mem_flatMap.mpr ⟨(c:ℤ),List.mem_flatMap.mpr ⟨c,hclist,by simp⟩,?_⟩⟩
  have he : d=(ε*(a:ℤ)*b,(a:ℤ)*c,ε*(b:ℤ)*c) :=
    Prod.ext hd1 (Prod.ext hd2 hd3)
  rcases hε with rfl | rfl
  · simp only [one_mul] at he
    simp only [List.mem_cons,List.not_mem_nil,or_false]
    exact Or.inl he
  · simp only [neg_one_mul] at he
    simp only [List.mem_cons,List.not_mem_nil,or_false]
    exact Or.inr (he.trans (by ext <;> ring))

end Z2Z4Rank6.RankThreeSelmer
