module

public import Z2Z4Rank6.TwistSelmerDataBounds
public import Z2Z4Rank6.TwistRankTransport
public import Z2Z4Rank6.RankThreeExact
public import Z2Z4Rank6.RankSixAssembly

@[expose] public section

/-!
# Exact generic rank six and finite index of the six printed points

Theorem 1.2(b) and Proposition 5.2 of Jaswal,
DOI 10.5281/zenodo.23437117.
-/

namespace Z2Z4Rank6
noncomputable section

namespace TwistSelmer

theorem curve_rank_at_most_one (hMW : MordellWeilTheorem)
    (hDescent : CompleteTwoDescentTheorem) (k : Fin 3) :
    Module.rank ℤ (RationalPoints (curve k))≤1 := by
  let : AddGroup.FG (RationalPoints (curve k)) := hMW (curve k) inferInstance
  obtain ⟨κ,hκ,hker⟩ := hDescent (curve k) 0 (-(r2 k:ℚ)) (-(r3 k:ℚ)) inferInstance rfl
  obtain ⟨_,hcard⟩ := descent_image_card_le_eight k κ hκ
  obtain ⟨j,hj⟩ := fullTwoTorsion_inclusion k
  apply RankModTwo.rank_le_of_descent_image_card κ hker j hj 1
  simpa only [show (2:ℕ)^(1+2)=8 by decide] using hcard

theorem generic_rank_at_most_one (hGT : GusicTadic.GusicTadicTheorem11)
    (hMW : MordellWeilTheorem) (hDescent : CompleteTwoDescentTheorem) (k : Fin 3) :
    Module.rank ℤ (GusicTadic.genericModel (twistPolynomial k)).toAffine.Point≤1 :=
  generic_rank_le_of_normalized_rank hGT k 1 (curve_rank_at_most_one hMW hDescent k)

end TwistSelmer

namespace RankSixExact
open FunctionField FunctionField.TwistCharacters

theorem four_rank_bounds (hGT : GusicTadic.GusicTadicTheorem11)
    (hMW : MordellWeilTheorem) (hDescent : CompleteTwoDescentTheorem) :
    Module.rank ℤ (twistPoints (false,false))≤3 ∧
    Module.rank ℤ (twistPoints (true,false))≤1 ∧
    Module.rank ℤ (twistPoints (false,true))≤1 ∧
    Module.rank ℤ (twistPoints (true,true))≤1 := by
  refine ⟨?_,?_,?_,?_⟩
  · have he : twistCurve (false,false)=RationalFunctionFamily.curve := twistCurve_trivial
    exact (PointScaling.pointCongr he).toIntLinearEquiv.rank_eq.le.trans
      (RationalFunctionFamily.rank_at_most_three hGT hMW hDescent)
  · exact (PointScaling.pointCongr RankSixAssembly.twistCurve_q1_model).toIntLinearEquiv.rank_eq.le.trans
      (TwistSelmer.generic_rank_at_most_one hGT hMW hDescent 0)
  · exact (PointScaling.pointCongr RankSixAssembly.twistCurve_q2_model).toIntLinearEquiv.rank_eq.le.trans
      (TwistSelmer.generic_rank_at_most_one hGT hMW hDescent 1)
  · exact (PointScaling.pointCongr RankSixAssembly.twistCurve_q12_model).toIntLinearEquiv.rank_eq.le.trans
      (TwistSelmer.generic_rank_at_most_one hGT hMW hDescent 2)

theorem pointGroup_rank_eq_six (hMazur : MazurTorsionTheorem)
    (hReduction : GoodReductionHomomorphisms) (hFormal : FormalGoodReductionHomomorphisms)
    (hGT : GusicTadic.GusicTadicTheorem11) (hMW : MordellWeilTheorem)
    (hDescent : CompleteTwoDescentTheorem) : Module.rank ℤ PointGroup=6 := by
  obtain ⟨h0,h1,h2,h3⟩ := four_rank_bounds hGT hMW hDescent
  exact RankSixAssembly.rank_eq_six_of_bounds hMazur hReduction hFormal h0 h1 h2 h3

theorem three_twist_ranks_eq_one (hMazur : MazurTorsionTheorem)
    (hReduction : GoodReductionHomomorphisms) (hFormal : FormalGoodReductionHomomorphisms)
    (hGT : GusicTadic.GusicTadicTheorem11) (hMW : MordellWeilTheorem)
    (hDescent : CompleteTwoDescentTheorem) :
    Module.rank ℤ (twistPoints (true,false))=1 ∧
    Module.rank ℤ (twistPoints (false,true))=1 ∧
    Module.rank ℤ (twistPoints (true,true))=1 := by
  obtain ⟨h0,h1,h2,h3⟩ := four_rank_bounds hGT hMW hDescent
  exact RankSixAssembly.twists_rank_one_of_bounds hMazur hReduction hFormal h0 h1 h2 h3

end RankSixExact

/-- The complete printed Theorem 1.2(b): the six specified
points are independent, and the function-field point group has rank 6. -/
theorem theorem_1_2_b (hMazur : MazurTorsionTheorem)
    (hReduction : GoodReductionHomomorphisms) (hFormal : FormalGoodReductionHomomorphisms)
    (hGT : GusicTadic.GusicTadicTheorem11) (hMW : MordellWeilTheorem)
    (hDescent : CompleteTwoDescentTheorem) : Theorem12b :=
  ⟨FunctionField.points_independent hMazur hReduction hFormal,
    RankSixExact.pointGroup_rank_eq_six hMazur hReduction hFormal hGT hMW hDescent⟩

/-- Proposition 5.2: the three quadratic twists have rank 1;
the rank over Q(C) is 6 and the six printed points span finite index. -/
theorem proposition_5_2 (hMazur : MazurTorsionTheorem)
    (hReduction : GoodReductionHomomorphisms) (hFormal : FormalGoodReductionHomomorphisms)
    (hGT : GusicTadic.GusicTadicTheorem11) (hMW : MordellWeilTheorem)
    (hDescent : CompleteTwoDescentTheorem) (hMWLN : MordellWeilLangNeronTheorem.{0}) :
    (Module.rank ℤ (FunctionField.TwistCharacters.twistPoints (true,false))=1 ∧
      Module.rank ℤ (FunctionField.TwistCharacters.twistPoints (false,true))=1 ∧
      Module.rank ℤ (FunctionField.TwistCharacters.twistPoints (true,true))=1) ∧
    Module.rank ℤ GenericPoints=6 ∧ GenericSixFiniteIndex := by
  obtain ⟨h0,h1,h2,h3⟩ := RankSixExact.four_rank_bounds hGT hMW hDescent
  exact ⟨RankSixExact.three_twist_ranks_eq_one hMazur hReduction hFormal hGT hMW hDescent,
    RankSixExact.pointGroup_rank_eq_six hMazur hReduction hFormal hGT hMW hDescent,
    RankSixAssembly.finiteIndex_of_bounds hMazur hReduction hFormal hMWLN h0 h1 h2 h3⟩

end
end Z2Z4Rank6
