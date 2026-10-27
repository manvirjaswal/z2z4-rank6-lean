import Z2Z4Rank6.Main
import Z2Z4Rank6.GExactRank
import Z2Z4Rank6.SecondGenericRank

/-!
# The specified sections in Propositions 6.2, 7.2 and Theorem 8.1

These statements retain the individual printed sections, their integral
linear independence and both exact-rank conclusions of Proposition 7.2(b).
All concrete arithmetic conditions follow from the printed congruences;
the hypotheses are the published theorems displayed below.
-/

namespace Z2Z4Rank6
noncomputable section

private theorem congruence_m_ne_zero (c : CPoint) (hc : c ∈ congruenceSet) : c.m ≠ 0 := by
  have h0 := hc.2 0
  intro h
  have hD := denominator_unit_of_congruent 0 h0.1 h0.2.2.2.1
  simp [h, sectionDenominator] at hD

/-- The P1,...,P6 at a point of the printed set S. -/
def congruenceSixPoints (c : CPoint) (hc : c ∈ congruenceSet) :
    Fin 6 → RationalPoints (X c.m) := by
  letI : (X c.m).IsElliptic := X_good_of_congruent13 c.m hc.1
  exact sixPoints c.m c.u c.v c.u_sq c.v_sq
    (congruence_m_ne_zero c hc) c.u_ne_zero c.v_ne_zero

theorem congruenceSixPoints_independent
    (hMazur : MazurTorsionTheorem) (hReduction : GoodReductionHomomorphisms)
    (c : CPoint) (hc : c ∈ congruenceSet) :
    LinearIndependent ℤ (congruenceSixPoints c hc) := by
  let : (X c.m).IsElliptic := X_good_of_congruent13 c.m hc.1
  have hm := congruence_m_ne_zero c hc
  have hT := X_torsion_of_congruent13 hMazur c.m hc.1
  change LinearIndependent ℤ
    (sixPoints c.m c.u c.v c.u_sq c.v_sq hm c.u_ne_zero c.v_ne_zero)
  apply sixPoints_linearIndependent_of_reduction_data hReduction c hm hT
  · intro i
    exact X_integralModel (hc.2 i).1
  · intro i
    exact reducedModel_X_of_congruent i (hc.2 i).1 (hc.2 i).2.2.2.1
  · intro i j
    have hi := hc.2 i
    exact (c.reduction_coordinates_of_congruent i hi.1 hi.2.1 hi.2.2.1
      hi.2.2.2.1 hi.2.2.2.2.1 hi.2.2.2.2.2 j).1
  · intro i j
    have hi := hc.2 i
    exact (c.reduction_coordinates_of_congruent i hi.1 hi.2.1 hi.2.2.1
      hi.2.2.2.1 hi.2.2.2.2.1 hi.2.2.2.2.2 j).2.1
  · intro i j
    have hi := hc.2 i
    exact (c.reduction_coordinates_of_congruent i hi.1 hi.2.1 hi.2.2.1
      hi.2.2.2.1 hi.2.2.2.2.1 hi.2.2.2.2.2 j).2.2.1
  · intro i j
    have hi := hc.2 i
    exact (c.reduction_coordinates_of_congruent i hi.1 hi.2.1 hi.2.2.1
      hi.2.2.2.1 hi.2.2.2.2.1 hi.2.2.2.2.2 j).2.2.2

theorem proposition_6_2_full
    (hMazur : MazurTorsionTheorem) (hSilvermanVII34 : OddPrimeTorsionIntegrality)
    (hReduction : GoodReductionHomomorphisms) (hLocal : LocalEllipticTopology) :
    congruenceSet.Infinite ∧
      ∀ (c : CPoint) (hc : c ∈ congruenceSet),
        GoodCurve (X c.m) ∧ TorsionExact (X c.m) ∧
          LinearIndependent ℤ (congruenceSixPoints c hc) := by
  refine ⟨infinite_congruenceSet hSilvermanVII34 hLocal, ?_⟩
  intro c hc
  exact ⟨X_good_of_congruent13 c.m hc.1,
    X_torsion_of_congruent13 hMazur c.m hc.1,
    congruenceSixPoints_independent hMazur hReduction c hc⟩

/-- The two numbered clauses, followed by the key five-point independence and the final
finite-index assertion in the proof. -/
theorem proposition_7_2_b_full
    (hMazur : MazurTorsionTheorem) (hMW : MordellWeilTheorem)
    (hDescent : CompleteTwoDescentTheorem) (hReduction : GoodReductionHomomorphisms)
    (hFormal : FormalGoodReductionHomomorphisms)
    (hGT : GusicTadic.GusicTadicTheorem11)
    (hMWLN : MordellWeilLangNeronTheorem.{0}) :
    Module.rank ℤ (GusicTadic.genericModel GTwistSelmer.hPolynomial).toAffine.Point = 2 ∧
      Module.rank ℤ GFunctionField.QuadraticCharacters.PointGroup = 5 ∧
      LinearIndependent ℤ GFunctionField.points ∧
      (Submodule.span ℤ (Set.range GFunctionField.points)).toAddSubgroup.FiniteIndex := by
  exact ⟨GExactRank.h_rank_eq_two hMazur hMW hDescent hReduction hFormal hGT,
    GExactRank.rank_eq_five hMazur hMW hDescent hReduction hFormal hGT,
    GFunctionField.points_independent hMazur hReduction hFormal,
    GExactRank.printed_five_finite_index hMazur hMW hDescent hReduction hFormal hGT hMWLN⟩

/-- The six printed sections, displayed as their coordinate points
in the degree-eight function field, are independent. -/
theorem theorem_8_1_b_full
    (hMazur : MazurTorsionTheorem) (hReduction : GoodReductionHomomorphisms)
    (hFormal : FormalGoodReductionHomomorphisms) :
    LinearIndependent ℤ
      ![SecondFamily.Q1 SecondFunctionField.W,
        WeierstrassCurve.Affine.Point.mk
          (SecondFunctionField.genericBasePoint.Q2_untwisted_equation
            SecondFunctionField.qA_W_ne_zero),
        WeierstrassCurve.Affine.Point.mk
          (SecondFunctionField.genericBasePoint.Q3_untwisted_equation
            SecondFunctionField.qA_W_ne_zero),
        WeierstrassCurve.Affine.Point.mk
          (SecondFunctionField.genericBasePoint.Q4_untwisted_equation
            SecondFunctionField.W_ne_zero SecondFunctionField.qB_W_ne_zero),
        WeierstrassCurve.Affine.Point.mk
          (SecondFunctionField.genericBasePoint.Q5_untwisted_equation
            SecondFunctionField.W_ne_zero SecondFunctionField.qB_W_ne_zero),
        WeierstrassCurve.Affine.Point.mk
          (SecondFunctionField.genericBasePoint.Q6_untwisted_equation
            (SecondFamily.qH_ne_zero_of_qA_qB _
              SecondFunctionField.qA_W_ne_zero SecondFunctionField.qB_W_ne_zero))] ∧
      6 ≤ Module.rank ℤ (SecondFamily.F SecondFunctionField.W).toAffine.Point := by
  simpa only [SecondFunctionField.points, SecondFamily.G2Point.sixPoints,
    SecondFunctionField.genericBasePoint]
    using theorem_8_1_b hMazur hReduction hFormal

end
end Z2Z4Rank6
