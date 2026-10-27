module

public import Z2Z4Rank6.GTorsionCoverFaltings
public import Z2Z4Rank6.Torsion
public import Mathlib.Order.Filter.Cofinite

@[expose] public section

/-! Cofinite exact torsion on G, through its signed genus-nine covers. -/
namespace Z2Z4Rank6.GTorsionCoverCofinite
noncomputable section
open TorsionHyperelliptic

/-- The two nonsquare conditions already exclude every singular split fiber. -/
theorem good_torsion_exact_of_nonsquares (hMazur : MazurTorsionTheorem)
    (c : GQuarticPoint) (hp : ¬IsSquare (a c.m*b c.m))
    (hn : ¬IsSquare (-(a c.m*b c.m))) : GoodCurve (X c.m) ∧ TorsionExact (X c.m) := by
  have hab : a c.m*b c.m≠0 := by
    intro hz
    exact hp ⟨0,by rw [hz]; norm_num⟩
  have hdiff : (a c.m-b c.m)*(a c.m+b c.m)≠0 := by
    intro hz
    rcases mul_eq_zero.mp hz with h|h
    · have he : a c.m=b c.m := sub_eq_zero.mp h
      exact hp ⟨b c.m,by rw [he]⟩
    · have he : a c.m= -(b c.m) := eq_neg_of_add_eq_zero_left h
      apply hn
      exact ⟨b c.m,by rw [he]; ring⟩
  have hprod : a c.m*b c.m*((a c.m)^2-(b c.m)^2)≠0 := by
    rw [show (a c.m)^2-(b c.m)^2=(a c.m-b c.m)*(a c.m+b c.m) by ring]
    exact mul_ne_zero hab hdiff
  exact ⟨E_good _ _ hprod,E_torsion_exact hMazur _ _ hprod hp hn⟩

theorem finite_square_ab
    (hCohom : AffineCoverStructureSheafCohomologyTheorem)
    (hGeo : SmoothProperGlobalConstantsGeometricIntegralityTheorem)
    (hF : FaltingsProperCurveTheorem) :
    {c : GQuarticPoint | IsSquare (a c.m*b c.m)}.Finite := by
  simpa only [sign,Bool.false_eq_true,ite_false,one_mul] using
    GTorsionCoverFaltings.finite_signed_square_obstruction false hCohom hGeo hF

theorem finite_square_neg_ab
    (hCohom : AffineCoverStructureSheafCohomologyTheorem)
    (hGeo : SmoothProperGlobalConstantsGeometricIntegralityTheorem)
    (hF : FaltingsProperCurveTheorem) :
    {c : GQuarticPoint | IsSquare (-(a c.m*b c.m))}.Finite := by
  simpa only [sign,ite_true,neg_one_mul,neg_mul,one_mul] using
    GTorsionCoverFaltings.finite_signed_square_obstruction true hCohom hGeo hF

theorem finite_not_good_torsion_exact (hMazur : MazurTorsionTheorem)
    (hCohom : AffineCoverStructureSheafCohomologyTheorem)
    (hGeo : SmoothProperGlobalConstantsGeometricIntegralityTheorem)
    (hF : FaltingsProperCurveTheorem) :
    {c : GQuarticPoint | ¬(GoodCurve (X c.m) ∧ TorsionExact (X c.m))}.Finite := by
  apply ((finite_square_ab hCohom hGeo hF).union (finite_square_neg_ab hCohom hGeo hF)).subset
  intro c hc
  by_contra hout
  exact hc (good_torsion_exact_of_nonsquares hMazur c (not_or.mp hout).1 (not_or.mp hout).2)

theorem torsion_cofinite (hMazur : MazurTorsionTheorem)
    (hCohom : AffineCoverStructureSheafCohomologyTheorem)
    (hGeo : SmoothProperGlobalConstantsGeometricIntegralityTheorem)
    (hF : FaltingsProperCurveTheorem) :
    ∀ᶠ c : GQuarticPoint in Filter.cofinite,GoodCurve (X c.m) ∧ TorsionExact (X c.m) :=
  Filter.eventually_cofinite.mpr (finite_not_good_torsion_exact hMazur hCohom hGeo hF)
end
end Z2Z4Rank6.GTorsionCoverCofinite
