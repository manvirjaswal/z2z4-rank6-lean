module

public import Z2Z4Rank6.ThirdTwistRanksSchemeModels
public import Z2Z4Rank6.ThirdTwistRanks

@[expose] public section

/-! Rank 7 on the function field of the smooth proper genus 5 base.
Its geometric integrality follows from the published geometric theorem. -/
namespace Z2Z4Rank6.ThirdTwistField
noncomputable section
open AlgebraicGeometry ThirdTwistCoverFunctionField
open scoped Classical

theorem scheme_pointGroup_rank_eq_seven
    (hGeo : SmoothProperGlobalConstantsGeometricIntegralityTheorem)
    (hMazur : MazurTorsionTheorem) (hReduction : GoodReductionHomomorphisms)
    (hFormal : FormalGoodReductionHomomorphisms) (hGT : GusicTadic.GusicTadicTheorem11)
    (hMW : MordellWeilTheorem) (hDescent : CompleteTwoDescentTheorem)
    (hOdd : OddPrimeTorsionIntegrality) :
    letI : IsIntegral ThirdTwistCoverProjective.scheme := schemeIntegral hGeo
    Module.rank ℤ (X coordinateM).toAffine.Point=7 := by
  let : IsIntegral ThirdTwistCoverProjective.scheme := schemeIntegral hGeo
  exact scheme_pointGroup_rank_eq_radical_rank.trans
    (pointGroup_rank_eq_seven hMazur hReduction hFormal hGT hMW hDescent hOdd)

end
end Z2Z4Rank6.ThirdTwistField
