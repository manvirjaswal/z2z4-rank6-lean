import Z2Z4Rank6.FirstExampleRankSixLower
import Z2Z4Rank6.FirstExampleRankSixSelmerCertificate
import Z2Z4Rank6.MordellWeil
import Z2Z4Rank6.RankModTwo
import Z2Z4Rank6.PointScaling
import Z2Z4Rank6.SplitTwoTorsion

/-! Exact rank six of the printed first example, Jaswal before
Proposition 6.2, DOI 10.5281/zenodo.23437117. The lower bound uses the six
points; the upper bound uses the 256-class complete-descent certificate. -/
namespace Z2Z4Rank6.FirstExampleRankSix

/-- The complete-descent upper certificate bounds rank by six. -/
theorem rank_at_most_six (hMW : MordellWeilTheorem)
    (hDescent : CompleteTwoDescentTheorem) : Module.rank ℤ (RationalPoints curve)≤6 := by
  let : AddGroup.FG (RationalPoints curve) := hMW curve curveElliptic
  obtain ⟨κ,hκ,hker⟩ := hDescent curve 0 (-(Selmer.r2:ℚ)) (-(Selmer.r3:ℚ))
    curveElliptic Selmer.curve_split
  obtain ⟨_,hcard⟩ := Selmer.descent_image_card_le κ hκ
  have hcurve : SplitTwoTorsion.curve (Selmer.r2:ℚ) (Selmer.r3:ℚ)=curve :=
    Selmer.curve_split.symm
  let : (SplitTwoTorsion.curve (Selmer.r2:ℚ) (Selmer.r3:ℚ)).IsElliptic := by
    rw [hcurve]
    exact curveElliptic
  obtain ⟨j,hj⟩ := SplitTwoTorsion.inclusion (Selmer.r2:ℚ) (Selmer.r3:ℚ)
    (by exact_mod_cast Selmer.roots_nonzero_distinct.1)
  let e := PointScaling.pointCongr hcurve
  let j' := e.toAddMonoidHom.comp j
  apply RankModTwo.rank_le_of_descent_image_card κ hker j' (e.injective.comp hj) 6
  simpa only [show (2:ℕ)^(6+2)=256 by decide] using hcard

/-- The unnumbered rank claim before Proposition 6.2: the printed
E_{7037226227200,3329722383911} has ordinary integral rank exactly six. -/
theorem rank_eq_six (hMazur : MazurTorsionTheorem) (hMW : MordellWeilTheorem)
    (hReduction : GoodReductionHomomorphisms) (hDescent : CompleteTwoDescentTheorem) :
    Module.rank ℤ (RationalPoints curve)=6 :=
  le_antisymm (rank_at_most_six hMW hDescent) (rank_at_least_six hMazur hReduction)

/-- The original unscaled c₀ fiber has the same exact rank. -/
theorem fiber_rank_eq_six (hMazur : MazurTorsionTheorem) (hMW : MordellWeilTheorem)
    (hReduction : GoodReductionHomomorphisms) (hDescent : CompleteTwoDescentTheorem) :
    Module.rank ℤ (RationalPoints (X baseC0.m))=6 :=
  fiberScaling.toIntLinearEquiv.rank_eq.trans (rank_eq_six hMazur hMW hReduction hDescent)

end Z2Z4Rank6.FirstExampleRankSix
