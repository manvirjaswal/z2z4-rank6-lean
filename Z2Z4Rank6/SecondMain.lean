import Z2Z4Rank6.SecondCongruenceInfinitude
import Z2Z4Rank6.SecondCongruenceRank
import Z2Z4Rank6.SecondJDegree

/-!
# The second family's infinite set with exact torsion and rank at least six

Remark 8.2 of Jaswal, DOI 10.5281/zenodo.23437117.

Form of proof: we restrict the printed 3-adic neighborhood by the six good
prime congruences from the printed example in Section 8(d). The compact-group
recurrence and reduction argument of Section 6 then prove independence on
this infinite subset. This proves the same infinity assertion without the
cofinite specialization theorem cited in the remark. The separate cofinite
assertions of Theorem 8.1(c) are not asserted here. All curves, points,
local maps, valuations and reduction matrix entries have been constructed.
-/

namespace Z2Z4Rank6
noncomputable section

theorem second_desired_of_theta_congruences (hMazur : MazurTorsionTheorem)
    (hReduction : GoodReductionHomomorphisms) (P : SecondFamily.G2Point ℚ)
    (hP : P∈secondCongruenceThetaSet) : DesiredCurve (SecondFamily.F P.W) := by
  have hTor := secondThetaNeighborhood_torsion_exact hMazur P hP.1
  exact ⟨second_elliptic_of_congruent 0 P (hP.2 0),hTor,
    second_rankAtLeastSix_of_congruences hReduction P hP.2 hTor⟩

/-- Remark 8.2: infinitely many second-family fibers have
exact torsion Z/2×Z/4 and six independent rational points. Their
rational j-invariants form an infinite set. The witnessing subset is explicit. -/
theorem remark_8_2 (hMazur : MazurTorsionTheorem)
    (hReduction : GoodReductionHomomorphisms) (hSilvermanVII34 : OddPrimeTorsionIntegrality)
    (hLocal : LocalEllipticTopology) :
    secondCongruenceThetaSet.Infinite ∧
    (∀ P∈secondCongruenceThetaSet,DesiredCurve (SecondFamily.F P.W)) ∧
    ((fun P : SecondFamily.G2Point ℚ => jValue (SecondFamily.F P.W)) '' secondCongruenceThetaSet).Infinite := by
  have hInf := infinite_secondCongruenceThetaSet hSilvermanVII34 hLocal
  have hDes := second_desired_of_theta_congruences hMazur hReduction
  refine ⟨hInf,hDes,?_⟩
  intro hFinite
  apply hInf
  apply Set.Finite.of_finite_fibers (fun P : SecondFamily.G2Point ℚ => jValue (SecondFamily.F P.W)) hFinite
  intro j _
  exact (SecondFamily.finite_j_G2Point_fiber j).subset (fun P hP => ⟨(hDes P hP.1).1,hP.2⟩)

/-- Theorem 1.1 also follows from the second family's printed local condition
and reduction data, with the same four published inputs as the first proof. -/
theorem theorem_1_1_from_second_family (hMazur : MazurTorsionTheorem)
    (hReduction : GoodReductionHomomorphisms) (hSilvermanVII34 : OddPrimeTorsionIntegrality)
    (hLocal : LocalEllipticTopology) : Theorem11 :=
  SecondFamily.theorem11_of_infinite_desired_fibers secondCongruenceThetaSet
    (infinite_secondCongruenceThetaSet hSilvermanVII34 hLocal)
    (second_desired_of_theta_congruences hMazur hReduction)

end
end Z2Z4Rank6
