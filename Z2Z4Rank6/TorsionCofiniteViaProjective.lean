module

public import Z2Z4Rank6.TorsionCoverFaltings
public import Mathlib.Order.Filter.Cofinite

@[expose] public section

/-!
# Cofinite exact torsion by the printed genus-seventeen cover route

Jaswal, Theorem 1.2(c), DOI 10.5281/zenodo.23437117. The proper
square-obstruction covers have proved genus 17. Their rational
points are finite by the Faltings theorem. The two signed
square loci and the sixteen singular exceptions therefore contain every
failure of ellipticity and exact torsion.
-/
namespace Z2Z4Rank6.TorsionCofiniteViaProjective
open TorsionHyperelliptic

theorem finite_square_ab
    (hCohom : AffineCoverStructureSheafCohomologyTheorem)
    (hGeo : SmoothProperGlobalConstantsGeometricIntegralityTheorem)
    (hF : FaltingsProperCurveTheorem) :
    {c : CPoint | IsSquare (a c.m*b c.m)}.Finite := by
  simpa only [sign,Bool.false_eq_true,ite_false,one_mul] using
    TorsionCoverFaltings.finite_signed_square_obstruction false hCohom hGeo hF

theorem finite_square_neg_ab
    (hCohom : AffineCoverStructureSheafCohomologyTheorem)
    (hGeo : SmoothProperGlobalConstantsGeometricIntegralityTheorem)
    (hF : FaltingsProperCurveTheorem) :
    {c : CPoint | IsSquare (-(a c.m*b c.m))}.Finite := by
  simpa only [sign,ite_true,neg_one_mul,neg_mul,one_mul] using
    TorsionCoverFaltings.finite_signed_square_obstruction true hCohom hGeo hF

theorem finite_not_good_torsion_exact (hMazur : MazurTorsionTheorem)
    (hCohom : AffineCoverStructureSheafCohomologyTheorem)
    (hGeo : SmoothProperGlobalConstantsGeometricIntegralityTheorem)
    (hF : FaltingsProperCurveTheorem) :
    {c : CPoint | ¬(GoodCurve (X c.m) ∧ TorsionExact (X c.m))}.Finite := by
  have hfinite := (exceptionalPoints_finite.union (finite_square_ab hCohom hGeo hF)).union
    (finite_square_neg_ab hCohom hGeo hF)
  apply hfinite.subset
  intro c hc
  by_contra hnot
  have he : c∉exceptionalPoints := fun h => hnot (Or.inl (Or.inl h))
  have hp : ¬IsSquare (a c.m*b c.m) := fun h => hnot (Or.inl (Or.inr h))
  have hn : ¬IsSquare (-(a c.m*b c.m)) := fun h => hnot (Or.inr h)
  have hg := (X_good_iff_not_exceptional c).mpr he
  exact hc ⟨hg,E_torsion_exact hMazur (a c.m) (b c.m)
    ((E_good_iff (a c.m) (b c.m)).mp hg) hp hn⟩

theorem torsion_cofinite (hMazur : MazurTorsionTheorem)
    (hCohom : AffineCoverStructureSheafCohomologyTheorem)
    (hGeo : SmoothProperGlobalConstantsGeometricIntegralityTheorem)
    (hF : FaltingsProperCurveTheorem) :
    ∀ᶠ c : CPoint in Filter.cofinite, GoodCurve (X c.m) ∧ TorsionExact (X c.m) :=
  Filter.eventually_cofinite.mpr (finite_not_good_torsion_exact hMazur hCohom hGeo hF)

theorem theorem12c_torsion_half (hMazur : MazurTorsionTheorem)
    (hCohom : AffineCoverStructureSheafCohomologyTheorem)
    (hGeo : SmoothProperGlobalConstantsGeometricIntegralityTheorem)
    (hF : FaltingsProperCurveTheorem) :
    (∀ c : CPoint,c∉exceptionalPoints → GoodCurve (X c.m) ∧ TorsionContains (X c.m)) ∧
      {c : CPoint | ¬(GoodCurve (X c.m) ∧ TorsionExact (X c.m))}.Finite :=
  ⟨theorem12c_first_clause,finite_not_good_torsion_exact hMazur hCohom hGeo hF⟩

end Z2Z4Rank6.TorsionCofiniteViaProjective
