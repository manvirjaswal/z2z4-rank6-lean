module

public import Z2Z4Rank6.SecondTorsionCoverFaltings
public import Z2Z4Rank6.SecondTorsionCriterion

@[expose] public section

/-! Cofinite exact torsion from the signed genus 9 projective covers.
The only finiteness theorem applied here is the generic proper-curve theorem.
-/
namespace Z2Z4Rank6.SecondTorsionCofiniteViaProjective
open SecondFamily SecondTorsionHyperelliptic

theorem finite_square_obstructions
    (hCohom : AffineCoverStructureSheafCohomologyTheorem)
    (hGeo : SmoothProperGlobalConstantsGeometricIntegralityTheorem)
    (hF : FaltingsProperCurveTheorem) :
    {P : G2Point ℚ | IsSquare (V P.W) ∨ IsSquare (-V P.W)}.Finite := by
  have hp : {P : G2Point ℚ | IsSquare (V P.W)}.Finite := by
    simpa [sign,TorsionHyperelliptic.sign] using
      SecondTorsionCoverFaltings.finite_signed_square_obstruction false hCohom hGeo hF
  have hn : {P : G2Point ℚ | IsSquare (-V P.W)}.Finite := by
    simpa [sign,TorsionHyperelliptic.sign] using
      SecondTorsionCoverFaltings.finite_signed_square_obstruction true hCohom hGeo hF
  exact hp.union hn

theorem finite_not_good_torsion_exact (hMazur : MazurTorsionTheorem)
    (hCohom : AffineCoverStructureSheafCohomologyTheorem)
    (hGeo : SmoothProperGlobalConstantsGeometricIntegralityTheorem)
    (hF : FaltingsProperCurveTheorem) :
    {P : G2Point ℚ | ¬(GoodCurve (F P.W) ∧ TorsionExact (F P.W))}.Finite := by
  apply (finite_square_obstructions hCohom hGeo hF).subset
  intro P hP
  by_contra hout
  exact hP (SecondTorsionCofinite.good_torsion_exact_of_nonsquares hMazur P
    (not_or.mp hout).1 (not_or.mp hout).2)

theorem torsion_cofinite (hMazur : MazurTorsionTheorem)
    (hCohom : AffineCoverStructureSheafCohomologyTheorem)
    (hGeo : SmoothProperGlobalConstantsGeometricIntegralityTheorem)
    (hF : FaltingsProperCurveTheorem) :
    ∀ᶠ P : G2Point ℚ in Filter.cofinite, GoodCurve (F P.W) ∧ TorsionExact (F P.W) :=
  Filter.eventually_cofinite.mpr (finite_not_good_torsion_exact hMazur hCohom hGeo hF)

end Z2Z4Rank6.SecondTorsionCofiniteViaProjective
