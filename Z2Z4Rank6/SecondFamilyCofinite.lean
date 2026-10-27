import Z2Z4Rank6.SecondTorsionCofiniteViaProjective
import Z2Z4Rank6.SecondGenericRank
import Z2Z4Rank6.SecondCofiniteRank
import Z2Z4Rank6.SecondQuarticG2

/-! Theorem 8.1(c): cofinite torsion follows from the genus-nine
projective covers and Faltings' theorem. The specialization, singular-fiber
and j-fiber bounds are proved in the imported modules. -/
namespace Z2Z4Rank6.SecondFamilyCofinite
open SecondFamily
noncomputable section

theorem finite_not_desired
    (hSilverman : SilvermanRigidSpecializationTheorem.{0})
    (hMazur : MazurTorsionTheorem) (hReduction : GoodReductionHomomorphisms)
    (hFormal : FormalGoodReductionHomomorphisms)
    (hCohom : AffineCoverStructureSheafCohomologyTheorem)
    (hGeo : SmoothProperGlobalConstantsGeometricIntegralityTheorem)
    (hF : FaltingsProperCurveTheorem) :
    {P : G2Point ℚ | ¬DesiredCurve (F P.W)}.Finite :=
  finite_not_desired_of_finite_failures (fun P : G2Point ℚ => F P.W)
    (SecondTorsionCofiniteViaProjective.finite_not_good_torsion_exact hMazur hCohom hGeo hF)
    (SecondCofiniteSpecialization.finite_rank_failures hSilverman hMazur hReduction hFormal)

theorem desired_j_image_infinite
    (hSilverman : SilvermanRigidSpecializationTheorem.{0})
    (hMazur : MazurTorsionTheorem) (hReduction : GoodReductionHomomorphisms)
    (hFormal : FormalGoodReductionHomomorphisms)
    (hCohom : AffineCoverStructureSheafCohomologyTheorem)
    (hGeo : SmoothProperGlobalConstantsGeometricIntegralityTheorem)
    (hF : FaltingsProperCurveTheorem) (hOdd : OddPrimeTorsionIntegrality) :
    ((fun P : G2Point ℚ => jValue (F P.W)) '' {P | DesiredCurve (F P.W)}).Infinite := by
  let : Infinite (G2Point ℚ) := secondG2_infinite hOdd
  have hInf : {P : G2Point ℚ | DesiredCurve (F P.W)}.Infinite :=
    Set.infinite_of_finite_compl (finite_not_desired hSilverman hMazur hReduction hFormal hCohom hGeo hF)
  intro hFinite
  apply hInf
  apply Set.Finite.of_finite_fibers (fun P : G2Point ℚ => jValue (F P.W)) hFinite
  intro j _
  exact (finite_j_G2Point_fiber j).subset (fun P hP => ⟨hP.1.1,hP.2⟩)

theorem theorem_8_1_c
    (hSilverman : SilvermanRigidSpecializationTheorem.{0})
    (hMazur : MazurTorsionTheorem) (hReduction : GoodReductionHomomorphisms)
    (hFormal : FormalGoodReductionHomomorphisms)
    (hCohom : AffineCoverStructureSheafCohomologyTheorem)
    (hGeo : SmoothProperGlobalConstantsGeometricIntegralityTheorem)
    (hF : FaltingsProperCurveTheorem) (hOdd : OddPrimeTorsionIntegrality) :
    {P : G2Point ℚ | ¬GoodCurve (F P.W)}.ncard=16 ∧
    (∀ P : G2Point ℚ,P∉Set.range singularPoint → GoodCurve (F P.W) ∧ TorsionContains (F P.W)) ∧
    {P : G2Point ℚ | ¬DesiredCurve (F P.W)}.Finite ∧
    ((fun P : G2Point ℚ => jValue (F P.W)) '' {P | DesiredCurve (F P.W)}).Infinite := by
  refine ⟨singular_fiber_points_ncard,?_,
    finite_not_desired hSilverman hMazur hReduction hFormal hCohom hGeo hF,
    desired_j_image_infinite hSilverman hMazur hReduction hFormal hCohom hGeo hF hOdd⟩
  intro P hP
  have hg : GoodCurve (F P.W) := by
    apply P.rational_elliptic_iff.mpr
    have hn : ¬(P.W=1 ∨ P.W=(lambda:ℚ)^2) := fun hw =>
      hP ((mem_singularPoint_range_iff P).mpr hw)
    tauto
  exact ⟨hg,second_torsion_contains_of_good P hg⟩

end
end Z2Z4Rank6.SecondFamilyCofinite
