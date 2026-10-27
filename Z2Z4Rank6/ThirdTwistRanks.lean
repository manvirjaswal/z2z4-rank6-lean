import Z2Z4Rank6.ThirdTwistRanksModels
import Z2Z4Rank6.ThirdTwistRank
import Z2Z4Rank6.RankSixExact

/-! The unnumbered third-twist branch after Proposition 7.2: the
curve X over the degree-eight field Q(m,sqrt(q1),sqrt(q2),sqrt(q3))
has rank 7. -/
namespace Z2Z4Rank6.ThirdTwistField
noncomputable section
open TwistCharacters

/-- Exact ranks of the four new character classes. -/
theorem third_twist_rank (hMW : MordellWeilTheorem)
    (hDescent : CompleteTwoDescentTheorem) (hGT : GusicTadic.GusicTadicTheorem11)
    (hOdd : OddPrimeTorsionIntegrality) (χ : Bool × Bool) :
    Module.rank ℤ (twistPoints (χ.1,χ.2,true))=
      if χ=(false,false) then 1 else 0 := by
  rw [(PointScaling.pointCongr (twistCurve_last_true χ)).toIntLinearEquiv.rank_eq,
    ThirdTwist.generic_rank hMW hDescent hGT hOdd]
  rcases χ with ⟨a,b⟩
  cases a <;> cases b <;> rfl

/-- The old four character classes retain the rank 6 decomposition. -/
theorem old_four_rank_sum (hMazur : MazurTorsionTheorem)
    (hReduction : GoodReductionHomomorphisms) (hFormal : FormalGoodReductionHomomorphisms)
    (hGT : GusicTadic.GusicTadicTheorem11) (hMW : MordellWeilTheorem)
    (hDescent : CompleteTwoDescentTheorem) :
    Module.rank ℤ (twistPoints (false,false,false))+
      Module.rank ℤ (twistPoints (true,false,false))+
      Module.rank ℤ (twistPoints (false,true,false))+
      Module.rank ℤ (twistPoints (true,true,false))=6 := by
  have h := RankSixExact.pointGroup_rank_eq_six hMazur hReduction hFormal hGT hMW hDescent
  rw [RankSixAssembly.rank_four_twists] at h
  have he (χ : Bool × Bool) :=
    (PointScaling.pointCongr (twistCurve_last_false χ)).toIntLinearEquiv.rank_eq
  rw [he (false,false),he (true,false),he (false,true),he (true,true)]
  exact h

/-- The printed rank 7 over the genus 5 triple-square base field. -/
theorem pointGroup_rank_eq_seven (hMazur : MazurTorsionTheorem)
    (hReduction : GoodReductionHomomorphisms) (hFormal : FormalGoodReductionHomomorphisms)
    (hGT : GusicTadic.GusicTadicTheorem11) (hMW : MordellWeilTheorem)
    (hDescent : CompleteTwoDescentTheorem) (hOdd : OddPrimeTorsionIntegrality) :
    Module.rank ℤ (X m).toAffine.Point=7 := by
  rw [rank_eight_twists,old_four_rank_sum hMazur hReduction hFormal hGT hMW hDescent,
    third_twist_rank hMW hDescent hGT hOdd (false,false),
    third_twist_rank hMW hDescent hGT hOdd (true,false),
    third_twist_rank hMW hDescent hGT hOdd (false,true),
    third_twist_rank hMW hDescent hGT hOdd (true,true)]
  norm_num

end
end Z2Z4Rank6.ThirdTwistField
