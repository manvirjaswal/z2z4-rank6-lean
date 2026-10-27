module

public import Z2Z4Rank6.RankSixExact

@[expose] public section

/-! Exact ranks of the four normalized fibers used in the upper bounds,
Jaswal Propositions 2.3/5.2, DOI 10.5281/zenodo.23437117. The lower bounds
transport along the proved injective specialization maps. -/
namespace Z2Z4Rank6
noncomputable section

namespace RankThreeSelmer

theorem curve_rank_eq_three (hMazur : MazurTorsionTheorem) (hMW : MordellWeilTheorem)
    (hDescent : CompleteTwoDescentTheorem) (hFormal : FormalGoodReductionHomomorphisms)
    (hGT : GusicTadic.GusicTadicTheorem11) : Module.rank ℤ (RationalPoints curve)=3 := by
  apply le_antisymm (curve_rank_at_most_three hMW hDescent)
  obtain ⟨σ,_,hσ⟩ := GusicTadic.X_injective_specialization_14 hGT
  let f := RankThreeExact.fiberEquiv.toAddMonoidHom.comp σ
  have hf : Function.Injective f := RankThreeExact.fiberEquiv.injective.comp hσ
  have hle := f.toIntLinearMap.rank_le_of_injective hf
  rwa [RationalFunctionFamily.rank_eq_three hMazur hMW hDescent hFormal hGT] at hle

end RankThreeSelmer

namespace TwistSelmer

theorem generic_rank_eq_one (hMazur : MazurTorsionTheorem)
    (hReduction : GoodReductionHomomorphisms) (hFormal : FormalGoodReductionHomomorphisms)
    (hGT : GusicTadic.GusicTadicTheorem11) (hMW : MordellWeilTheorem)
    (hDescent : CompleteTwoDescentTheorem) (k : Fin 3) :
    Module.rank ℤ (GusicTadic.genericModel (twistPolynomial k)).toAffine.Point=1 := by
  obtain ⟨h1,h2,h3⟩ := RankSixExact.three_twist_ranks_eq_one
    hMazur hReduction hFormal hGT hMW hDescent
  fin_cases k
  · exact (PointScaling.pointCongr RankSixAssembly.twistCurve_q1_model).toIntLinearEquiv.rank_eq.symm.trans h1
  · exact (PointScaling.pointCongr RankSixAssembly.twistCurve_q2_model).toIntLinearEquiv.rank_eq.symm.trans h2
  · exact (PointScaling.pointCongr RankSixAssembly.twistCurve_q12_model).toIntLinearEquiv.rank_eq.symm.trans h3

theorem curve_rank_eq_one (hMazur : MazurTorsionTheorem)
    (hReduction : GoodReductionHomomorphisms) (hFormal : FormalGoodReductionHomomorphisms)
    (hGT : GusicTadic.GusicTadicTheorem11) (hMW : MordellWeilTheorem)
    (hDescent : CompleteTwoDescentTheorem) (k : Fin 3) :
    Module.rank ℤ (RationalPoints (curve k))=1 := by
  apply le_antisymm (curve_rank_at_most_one hMW hDescent k)
  obtain ⟨σ,hσ⟩ := injective_to_normalized_fiber hGT k
  have hle := σ.toIntLinearMap.rank_le_of_injective hσ
  rwa [generic_rank_eq_one hMazur hReduction hFormal hGT hMW hDescent k] at hle

end TwistSelmer
end
end Z2Z4Rank6
