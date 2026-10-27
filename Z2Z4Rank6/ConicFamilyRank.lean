module

public import Z2Z4Rank6.ConicRankNineCertificateExact
public import Z2Z4Rank6.ConicSpecialization
public import Z2Z4Rank6.ConicMinimality

@[expose] public section
/-!
# The conic family and its exact rank-nine fiber

The four generic points are independent. The specified numerical fiber
has the displayed minimal equation and exact rank nine, proved by its
independent descent images and complete-descent upper certificate.
Source: Jaswal, Proposition 7.1, DOI 10.5281/zenodo.23437117.
-/

namespace Z2Z4Rank6.ConicFamilyRank

noncomputable section

/-- The four specified points are independent over Q(k), and the
printed k=25/11 fiber is the rank-nine curve with the displayed minimal model. -/
theorem proposition_7_1
    (hMazur : MazurTorsionTheorem) (hReduction : GoodReductionHomomorphisms)
    (hFormal : FormalGoodReductionHomomorphisms)
    (hMW : MordellWeilTheorem) (hDescent : CompleteTwoDescentTheorem) :
    LinearIndependent ℤ ConicBase.points ∧
    4 ≤ Module.rank ℤ (X ConicBase.m).toAffine.Point ∧
    conicM (25/11 : ℚ)=1681/119 ∧
    parameterM (900/781 : ℚ)=1681/119 ∧
    (∃ C : WeierstrassCurve.VariableChange ℚ,
      C • X (conicM (25/11 : ℚ))=ConicRankNine.publishedModel) ∧
    ConicRankNine.PublishedModelGlobalMinimal ∧
    Module.rank ℤ (RationalPoints (X (conicM (25/11 : ℚ))))=9 := by
  have hIndependent := ConicBase.points_independent hMazur hReduction hFormal
  refine ⟨hIndependent, ?_, ConicRankNine.conic_parameter, ConicRankNine.dp_parameter,
    ⟨_, ConicRankNine.conic_published_change⟩,
    ConicRankNine.publishedModel_global_minimal, ?_⟩
  · simpa using hIndependent.cardinal_le_rank
  · rw [ConicRankNine.conic_parameter]
    exact ConicRankNine.fiberPublishedEquiv.toIntLinearEquiv.rank_eq.trans
      (ConicRankNineCertificate.published_rank_nine hMazur hMW hDescent)

end
end Z2Z4Rank6.ConicFamilyRank
