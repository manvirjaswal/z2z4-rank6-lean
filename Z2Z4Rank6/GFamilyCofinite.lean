module

public import Z2Z4Rank6.GCofiniteRank
public import Z2Z4Rank6.GTorsionCoverCofinite

@[expose] public section

/-!
# Infinitely many rank-five curves from G

The unnumbered conclusion following Proposition 7.2 is assembled on the
rational G-point set. Outside a finite set, the rational
fibers are elliptic with torsion Z/2 × Z/4 and ordinary rank at least 5.
Their rational j-values form an infinite set.
-/
namespace Z2Z4Rank6.GFamilyCofinite
noncomputable section
open GCofiniteRank

/-- The ellipticity, exact torsion and ordinary rank-five conditions. -/
def DesiredFive (W : WeierstrassCurve ℚ) : Prop :=
  GoodCurve W ∧ TorsionExact W ∧ ordinaryRankAtLeastFive W

/-- Both the torsion and rank exceptions are finite subsets of G(Q). -/
theorem finite_not_desired
    (hSilverman : SilvermanRigidSpecializationTheorem.{0})
    (hMazur : MazurTorsionTheorem) (hReduction : GoodReductionHomomorphisms)
    (hFormal : FormalGoodReductionHomomorphisms)
    (hCohom : AffineCoverStructureSheafCohomologyTheorem)
    (hGeo : SmoothProperGlobalConstantsGeometricIntegralityTheorem)
    (hF : FaltingsProperCurveTheorem) :
    {c : GQuarticPoint | ¬DesiredFive (X c.m)}.Finite := by
  apply ((GTorsionCoverCofinite.finite_not_good_torsion_exact hMazur hCohom hGeo hF).union
    (GCofiniteRank.finite_ordinary_rank_failures hSilverman hMazur hReduction hFormal)).subset
  intro c hc
  change ¬(GoodCurve (X c.m) ∧ TorsionExact (X c.m)) ∨
    ¬ordinaryRankAtLeastFive (X c.m)
  change ¬(GoodCurve (X c.m) ∧ TorsionExact (X c.m) ∧
    ordinaryRankAtLeastFive (X c.m)) at hc
  tauto

theorem desired_cofinite
    (hSilverman : SilvermanRigidSpecializationTheorem.{0})
    (hMazur : MazurTorsionTheorem) (hReduction : GoodReductionHomomorphisms)
    (hFormal : FormalGoodReductionHomomorphisms)
    (hCohom : AffineCoverStructureSheafCohomologyTheorem)
    (hGeo : SmoothProperGlobalConstantsGeometricIntegralityTheorem)
    (hF : FaltingsProperCurveTheorem) :
    ∀ᶠ c : GQuarticPoint in Filter.cofinite, DesiredFive (X c.m) :=
  Filter.eventually_cofinite.mpr
    (finite_not_desired hSilverman hMazur hReduction hFormal hCohom hGeo hF)

theorem desired_parameters_infinite
    (hSilverman : SilvermanRigidSpecializationTheorem.{0})
    (hMazur : MazurTorsionTheorem) (hReduction : GoodReductionHomomorphisms)
    (hFormal : FormalGoodReductionHomomorphisms)
    (hCohom : AffineCoverStructureSheafCohomologyTheorem)
    (hGeo : SmoothProperGlobalConstantsGeometricIntegralityTheorem)
    (hF : FaltingsProperCurveTheorem) (hOdd : OddPrimeTorsionIntegrality) :
    {c : GQuarticPoint | DesiredFive (X c.m)}.Infinite := by
  let : Infinite GQuarticPoint := infinite_GQuarticPoint hOdd
  exact Set.infinite_of_finite_compl
    (finite_not_desired hSilverman hMazur hReduction hFormal hCohom hGeo hF)

/-- Infinitely many j-values occur among the desired fibers. -/
theorem desired_j_image_infinite
    (hSilverman : SilvermanRigidSpecializationTheorem.{0})
    (hMazur : MazurTorsionTheorem) (hReduction : GoodReductionHomomorphisms)
    (hFormal : FormalGoodReductionHomomorphisms)
    (hCohom : AffineCoverStructureSheafCohomologyTheorem)
    (hGeo : SmoothProperGlobalConstantsGeometricIntegralityTheorem)
    (hF : FaltingsProperCurveTheorem) (hOdd : OddPrimeTorsionIntegrality) :
    ((fun c : GQuarticPoint=>jValue (X c.m)) '' {c | DesiredFive (X c.m)}).Infinite := by
  have hInf := desired_parameters_infinite hSilverman hMazur hReduction hFormal hCohom hGeo hF hOdd
  intro hFinite
  apply hInf
  apply Set.Finite.of_finite_fibers (fun c : GQuarticPoint=>jValue (X c.m)) hFinite
  intro j _
  exact (finite_j_GQuarticPoint_fiber j).subset (fun c hc=>⟨hc.1.1,hc.2⟩)

/-- The complete printed unnumbered rank-five family conclusion following
Proposition 7.2: cofinite exact torsion/rank and infinitely many distinct j-values. -/
theorem rank_five_family
    (hSilverman : SilvermanRigidSpecializationTheorem.{0})
    (hMazur : MazurTorsionTheorem) (hReduction : GoodReductionHomomorphisms)
    (hFormal : FormalGoodReductionHomomorphisms)
    (hCohom : AffineCoverStructureSheafCohomologyTheorem)
    (hGeo : SmoothProperGlobalConstantsGeometricIntegralityTheorem)
    (hF : FaltingsProperCurveTheorem) (hOdd : OddPrimeTorsionIntegrality) :
    {c : GQuarticPoint | ¬DesiredFive (X c.m)}.Finite ∧
      ((fun c : GQuarticPoint=>jValue (X c.m)) '' {c | DesiredFive (X c.m)}).Infinite :=
  ⟨finite_not_desired hSilverman hMazur hReduction hFormal hCohom hGeo hF,
    desired_j_image_infinite hSilverman hMazur hReduction hFormal hCohom hGeo hF hOdd⟩

end
end Z2Z4Rank6.GFamilyCofinite
