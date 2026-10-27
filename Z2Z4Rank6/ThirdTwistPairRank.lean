import Z2Z4Rank6.ThirdTwistPairRankModels
import Z2Z4Rank6.ThirdTwistRank
import Z2Z4Rank6.RankSixExact

/-! The printed two pair function fields both give rank 5=3+1+1+0. -/
namespace Z2Z4Rank6.ThirdTwistPairRank
noncomputable section
open scoped Classical

/-- The first or second old twist has its proved rank 1. -/
theorem old_rank (hMazur : MazurTorsionTheorem)
    (hReduction : GoodReductionHomomorphisms) (hFormal : FormalGoodReductionHomomorphisms)
    (hGT : GusicTadic.GusicTadicTheorem11) (hMW : MordellWeilTheorem)
    (hDescent : CompleteTwoDescentTheorem) (ε : Bool) :
    Module.rank ℤ (FunctionField.TwistCharacters.twistCurve (oldCharacter ε)).toAffine.Point=1 := by
  obtain ⟨h1,h2,_⟩ :=
    RankSixExact.three_twist_ranks_eq_one hMazur hReduction hFormal hGT hMW hDescent
  cases ε
  · exact h1
  · exact h2

/-- Exact rank on both quadratic radical towers. -/
theorem model_rank_eq_five (hMazur : MazurTorsionTheorem)
    (hReduction : GoodReductionHomomorphisms) (hFormal : FormalGoodReductionHomomorphisms)
    (hGT : GusicTadic.GusicTadicTheorem11) (hMW : MordellWeilTheorem)
    (hDescent : CompleteTwoDescentTheorem) (hOdd : OddPrimeTorsionIntegrality) (ε : Bool) :
    Module.rank ℤ (model ε).toAffine.Point=5 := by
  rw [rank_decomposition,RationalFunctionFamily.rank_eq_three hMazur hMW hDescent hFormal hGT,
    old_rank hMazur hReduction hFormal hGT hMW hDescent,
    ThirdTwist.generic_rank hMW hDescent hGT hOdd,
    ThirdTwist.generic_rank hMW hDescent hGT hOdd]
  cases ε <;> norm_num [thirdIndex]

theorem pairOne_rank_eq_five (hMazur : MazurTorsionTheorem)
    (hReduction : GoodReductionHomomorphisms) (hFormal : FormalGoodReductionHomomorphisms)
    (hGT : GusicTadic.GusicTadicTheorem11) (hMW : MordellWeilTheorem)
    (hDescent : CompleteTwoDescentTheorem) (hOdd : OddPrimeTorsionIntegrality) :
    Module.rank ℤ (X ThirdTwistField.PairOne.m).toAffine.Point=5 :=
  (PointScaling.pointCongr model_false).toIntLinearEquiv.rank_eq.symm.trans
    (model_rank_eq_five hMazur hReduction hFormal hGT hMW hDescent hOdd false)

theorem pairTwo_rank_eq_five (hMazur : MazurTorsionTheorem)
    (hReduction : GoodReductionHomomorphisms) (hFormal : FormalGoodReductionHomomorphisms)
    (hGT : GusicTadic.GusicTadicTheorem11) (hMW : MordellWeilTheorem)
    (hDescent : CompleteTwoDescentTheorem) (hOdd : OddPrimeTorsionIntegrality) :
    Module.rank ℤ (X ThirdTwistField.PairTwo.m).toAffine.Point=5 :=
  (PointScaling.pointCongr model_true).toIntLinearEquiv.rank_eq.symm.trans
    (model_rank_eq_five hMazur hReduction hFormal hGT hMW hDescent hOdd true)

end
end Z2Z4Rank6.ThirdTwistPairRank
