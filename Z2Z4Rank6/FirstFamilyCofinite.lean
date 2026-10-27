module

public import Z2Z4Rank6.TorsionCofiniteViaProjective
public import Z2Z4Rank6.FirstCofiniteRank

@[expose] public section

/-! Theorem 1.2(c): cofinite torsion follows from the genus-seventeen
projective covers and Faltings' theorem; cofinite rank follows from
specialization. -/
namespace Z2Z4Rank6.FirstFamilyCofinite

theorem finite_not_desired
    (hSilverman : SilvermanRigidSpecializationTheorem.{0})
    (hMazur : MazurTorsionTheorem) (hReduction : GoodReductionHomomorphisms)
    (hFormal : FormalGoodReductionHomomorphisms)
    (hCohom : AffineCoverStructureSheafCohomologyTheorem)
    (hGeo : SmoothProperGlobalConstantsGeometricIntegralityTheorem)
    (hF : FaltingsProperCurveTheorem) :
    {c : CPoint | ¬DesiredCurve (X c.m)}.Finite :=
  finite_not_desired_of_finite_failures (fun c : CPoint => X c.m)
    (TorsionCofiniteViaProjective.finite_not_good_torsion_exact hMazur hCohom hGeo hF)
    (CofiniteSpecialization.finite_rank_failures hSilverman hMazur hReduction hFormal)

theorem theorem12c
    (hSilverman : SilvermanRigidSpecializationTheorem.{0})
    (hMazur : MazurTorsionTheorem) (hReduction : GoodReductionHomomorphisms)
    (hFormal : FormalGoodReductionHomomorphisms)
    (hCohom : AffineCoverStructureSheafCohomologyTheorem)
    (hGeo : SmoothProperGlobalConstantsGeometricIntegralityTheorem)
    (hF : FaltingsProperCurveTheorem) : Theorem12c :=
  ⟨theorem12c_first_clause,
    finite_not_desired hSilverman hMazur hReduction hFormal hCohom hGeo hF⟩

end Z2Z4Rank6.FirstFamilyCofinite
