import Z2Z4Rank6.RankThreeSelmerChunk00
import Z2Z4Rank6.RankThreeSelmerChunk01
import Z2Z4Rank6.RankThreeSelmerChunk02
import Z2Z4Rank6.RankThreeSelmerChunk03
import Z2Z4Rank6.RankThreeSelmerChunk04
import Z2Z4Rank6.RankThreeSelmerChunk05
import Z2Z4Rank6.RankThreeSelmerChunk06
import Z2Z4Rank6.RankThreeSelmerChunk07
import Z2Z4Rank6.RankThreeSelmerChunk08
import Z2Z4Rank6.RankThreeSelmerChunk09
import Z2Z4Rank6.RankThreeSelmerChunk10
import Z2Z4Rank6.RankThreeSelmerChunk11
import Z2Z4Rank6.RankThreeSelmerChunk12
import Z2Z4Rank6.RankThreeSelmerChunk13
import Z2Z4Rank6.RankThreeSelmerChunk14
import Z2Z4Rank6.RankThreeSelmerChunk15
import Z2Z4Rank6.RankThreeSelmerSupport
import Z2Z4Rank6.SplitDescentImage
import Z2Z4Rank6.ECExactRank

/-!
# The rank-three upper certificate at m=14/3

Source: Jaswal, DOI 10.5281/zenodo.23437117, Propositions 2.3 and 5.2.
All canonical everywhere locally soluble coverings lie among 32
explicit triples, by proved local conditions and 64 kernel checks.
The published complete-descent kernel theorem and Mordell--Weil
finite generation then bound the rational elliptic point-group rank.
-/
namespace Z2Z4Rank6.RankThreeSelmer

private theorem chunk_check (a : ℕ) (ha : a∈aDivisors) :
    (rawChunk a).filter localTest=survivorChunk a := by
  simp only [aDivisors,List.mem_cons,List.not_mem_nil,or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact chunk_00
  · exact chunk_01
  · exact chunk_02
  · exact chunk_03
  · exact chunk_04
  · exact chunk_05
  · exact chunk_06
  · exact chunk_07
  · exact chunk_08
  · exact chunk_09
  · exact chunk_10
  · exact chunk_11
  · exact chunk_12
  · exact chunk_13
  · exact chunk_14
  · exact chunk_15

/-- The canonical everywhere locally soluble covering set is contained
in the 32 explicit surviving triples. -/
theorem fullTwoSelmerTriples_subset_survivors :
    fullTwoSelmerTriples r2 r3 ⊆ (survivors.toFinset : Set ECFullTriple) := by
  intro d hd
  obtain ⟨a,ha,hm⟩ := exists_rawChunk_of_mem hd
  have hf : d∈(rawChunk a).filter localTest := List.mem_filter.mpr ⟨hm,localTest_of_mem hd⟩
  rw [chunk_check a ha] at hf
  exact List.mem_toFinset.mpr (List.mem_flatMap.mpr ⟨a,ha,hf⟩)

/-- The finite upper certificate has exactly 32 distinct canonical triples. -/
theorem survivors_card : survivors.toFinset.card=32 := by decide +kernel

/-- The printed integral split elliptic curve isomorphic to X at m=14/3. -/
def curve : WeierstrassCurve ℚ := E (A:ℚ) (B:ℚ)

instance curveElliptic : curve.IsElliptic :=
  E_good _ _ (by norm_num [A,B])

theorem curve_eq_split : curve=splitWeierstrass 0 (-(r2:ℚ)) (-(r3:ℚ)) := by
  convert E_eq_splitWeierstrass (A:ℚ) (B:ℚ) using 1 <;>
    simp [curve,r2,r3]

/-- Every complete-descent homomorphism on the printed integral fiber
has a finite image of cardinality at most 32. -/
theorem descent_image_card_le
    (κ : RationalPoints curve →+ (RatSquareClassAdd × RatSquareClassAdd))
    (hκ : ∀ P, κ P=completeDescentCoordinates curve 0 (-(r2:ℚ)) (-(r3:ℚ)) P) :
    Finite κ.range ∧ Nat.card κ.range≤32 := by
  have h := split_descent_image_card_le curve r2 r3
    (by norm_num [r2,A]) (by norm_num [r3,B]) (by norm_num [r2,r3,A,B])
    curve_eq_split survivors.toFinset fullTwoSelmerTriples_subset_survivors κ hκ
  simpa only [survivors_card] using h

/-- The rational point group of the printed 14/3 fiber has
integral rank at most 3. The hypotheses are the Mordell--Weil and complete two-descent theorems. -/
theorem curve_rank_at_most_three (hMW : MordellWeilTheorem)
    (hDescent : CompleteTwoDescentTheorem) : Module.rank ℤ (RationalPoints curve)≤3 := by
  let : AddGroup.FG (RationalPoints curve) := hMW curve inferInstance
  obtain ⟨κ,hκ,hker⟩ := hDescent curve 0 (-(r2:ℚ)) (-(r3:ℚ))
    curveElliptic curve_eq_split
  obtain ⟨_,hcard⟩ := descent_image_card_le κ hκ
  obtain ⟨f,hf⟩ := E_two_four_inclusion (A:ℚ) (B:ℚ) (by norm_num [A,B])
  let j : (ZMod 2 × ZMod 2) →+ RationalPoints curve := f.comp twoTwoToTwoFour
  apply RankModTwo.rank_le_of_descent_image_card κ hker j
    (hf.comp twoTwoToTwoFour_injective) 3
  simpa only [show (2:ℕ)^(3+2)=32 by decide] using hcard

end Z2Z4Rank6.RankThreeSelmer
