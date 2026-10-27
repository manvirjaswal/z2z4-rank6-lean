import Z2Z4Rank6.SplitTwoDescentSha
import Z2Z4Rank6.PointScalingSha
import Z2Z4Rank6.GExampleRankSixSelmerExact

/-!
# Vanishing of Sha[2] for the rank-six fiber after Proposition 7.2

The local covering classes have been proved equal to the
rational descent image. The generic split-descent exact sequence then
makes the continuous-cohomology Tate–Shafarevich two-torsion zero.

Sources: Jaswal, the printed numerical example; Silverman, The Arithmetic
of Elliptic Curves, second edition, X.1.4 p. 315, X.3.6 p. 325, X.4.2(a) p. 333.
-/
namespace Z2Z4Rank6.GExampleRankSix
noncomputable section
open Common.Elliptic.TateShafarevich

theorem sha_two_subsingleton (hExact : SilvermanSplitTwoDescentExactSequence)
    (hDescent : CompleteTwoDescentTheorem) : Subsingleton (shaTwo curve) :=
  shaTwo_subsingleton_of_fullClasses_eq_descent_image hExact curve Selmer.r2 Selmer.r3
    Selmer.roots_nonzero_distinct.1 Selmer.roots_nonzero_distinct.2.1
    Selmer.roots_nonzero_distinct.2.2 curveElliptic Selmer.curve_split
    (Selmer.fullTwoSelmerClasses_eq_descent_image hDescent)

theorem sha_two_eq_zero (hExact : SilvermanSplitTwoDescentExactSequence)
    (hDescent : CompleteTwoDescentTheorem) (x : shaTwo curve) : x=0 :=
  @Subsingleton.elim _ (sha_two_subsingleton hExact hDescent) x 0

/-- No nonzero Tate–Shafarevich class is killed by two. -/
theorem sha_two_torsion_vanishes (hExact : SilvermanSplitTwoDescentExactSequence)
    (hDescent : CompleteTwoDescentTheorem) (x : sha curve)
    (hx : (2 : ℕ) • x=0) : x=0 := by
  have h := sha_two_eq_zero hExact hDescent (⟨x,hx⟩ : shaTwo curve)
  exact congrArg Subtype.val h

theorem sha_two_eq_bot (hExact : SilvermanSplitTwoDescentExactSequence)
    (hDescent : CompleteTwoDescentTheorem) : shaTwo curve=⊥ := by
  apply le_antisymm
  · intro x hx
    exact AddSubgroup.mem_bot.mpr (sha_two_torsion_vanishes hExact hDescent x hx)
  · exact bot_le


/-- The coordinate scaling is natural over every characteristic-zero field. -/
def original_fiber_natural_equiv : NaturalPointEquiv (X (291/53 : ℚ)) curve :=
  (NaturalPointEquiv.splitFamilyScaling (a GReductionData.baseM) (b GReductionData.baseM)
    GReductionData.scale (by norm_num [GReductionData.scale])).trans
      (NaturalPointEquiv.ofEq (by
        rw [GReductionData.scale_parameters.1,GReductionData.scale_parameters.2]
        exact curve_eq_rationalCurve.symm))

theorem original_fiber_sha_two_subsingleton (hExact : SilvermanSplitTwoDescentExactSequence)
    (hDescent : CompleteTwoDescentTheorem) :
    Subsingleton (shaTwo (X (291/53 : ℚ))) :=
  original_fiber_natural_equiv.shaTwo_subsingleton (sha_two_subsingleton hExact hDescent)

/-- The unscaled fiber's Tate–Shafarevich group has no nonzero two-torsion. -/
theorem original_fiber_sha_two_torsion_vanishes (hExact : SilvermanSplitTwoDescentExactSequence)
    (hDescent : CompleteTwoDescentTheorem) (x : sha (X (291/53 : ℚ)))
    (hx : (2 : ℕ) • x=0) : x=0 := by
  have h := @Subsingleton.elim _ (original_fiber_sha_two_subsingleton hExact hDescent)
    (⟨x,hx⟩ : shaTwo (X (291/53 : ℚ))) 0
  exact congrArg Subtype.val h

theorem original_fiber_sha_two_eq_bot (hExact : SilvermanSplitTwoDescentExactSequence)
    (hDescent : CompleteTwoDescentTheorem) : shaTwo (X (291/53 : ℚ))=⊥ := by
  apply le_antisymm
  · intro x hx
    exact AddSubgroup.mem_bot.mpr (original_fiber_sha_two_torsion_vanishes hExact hDescent x hx)
  · exact bot_le

end
end Z2Z4Rank6.GExampleRankSix
