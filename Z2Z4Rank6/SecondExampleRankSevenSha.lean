module

public import Z2Z4Rank6.SplitTwoDescentSha
public import Z2Z4Rank6.SecondExampleRankSevenSelmerExact

@[expose] public section

/-!
# Vanishing of Sha[2] for the rank-seven example after Theorem 8.1

The local covering classes have been proved equal to the
rational descent image. The generic split-descent exact sequence then
makes the continuous-cohomology Tate–Shafarevich two-torsion zero.

Sources: Jaswal, the printed numerical example; Silverman, The Arithmetic
of Elliptic Curves, second edition, X.1.4 p. 315, X.3.6 p. 325, X.4.2(a) p. 333.
-/
namespace Z2Z4Rank6.SecondExampleRankSeven
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

end
end Z2Z4Rank6.SecondExampleRankSeven
