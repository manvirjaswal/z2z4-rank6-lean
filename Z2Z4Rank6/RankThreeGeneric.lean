import Z2Z4Rank6.RationalFunctionSpecialization
import Z2Z4Rank6.RankThreeLower

/-!
# The original three generic sections are independent

The lower bound in Proposition 2.3 of M. Jaswal,
DOI 10.5281/zenodo.23437117. The shifted formal place constructs a
specialization homomorphism at m=37/5. The checked two-descent independence
of its three point images then proves independence in the Q(m)-group.
-/

namespace Z2Z4Rank6.RationalFunctionFamily

noncomputable section

/-- The Q(m)-point group specializes at 37/5 with exactly the three
printed signed images used in the lower-bound certificate. -/
theorem exists_specialization_rankThreeFiber (hFormal : FormalGoodReductionHomomorphisms) :
    ∃ spec : curve.toAffine.Point →+ RationalPoints (X rankThreeParameter),
      ∀ j : Fin 3, spec (points j)=rankThreePoints j := by
  obtain ⟨spec,hspec⟩ := RationalFunctionSpecialization.exists_specialization hFormal rankThreeParameter
  refine ⟨spec,?_⟩
  intro j
  rw [hspec]
  fin_cases j <;> rfl

/-- Proposition 2.3, generic lower bound: the three printed sections of the
original Q(m) family are Z-linearly independent. The hypotheses are Mazur's classification, the
complete two-descent theorem and the formal good-reduction theorem. -/
theorem points_linearIndependent (hMazur : MazurTorsionTheorem)
    (hDescent : CompleteTwoDescentTheorem) (hFormal : FormalGoodReductionHomomorphisms) :
    LinearIndependent ℤ points := by
  obtain ⟨spec,hspec⟩ := exists_specialization_rankThreeFiber hFormal
  exact rankThree_independent_of_specialization hMazur hDescent points spec hspec

/-- The original rational-function curve has at least three
independent rational-function points, using the paper's specialization route. -/
theorem rank_at_least_three (hMazur : MazurTorsionTheorem)
    (hDescent : CompleteTwoDescentTheorem) (hFormal : FormalGoodReductionHomomorphisms) :
    ∃ P : Fin 3 → curve.toAffine.Point, LinearIndependent ℤ P :=
  ⟨points,points_linearIndependent hMazur hDescent hFormal⟩

end
end Z2Z4Rank6.RationalFunctionFamily
