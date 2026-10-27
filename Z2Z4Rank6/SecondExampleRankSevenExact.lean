module

public import Z2Z4Rank6.SecondExampleRankSeven
public import Z2Z4Rank6.SecondExampleRankSevenSelmerCertificate
public import Z2Z4Rank6.MordellWeil
public import Z2Z4Rank6.RankModTwo
public import Z2Z4Rank6.PointScaling
public import Z2Z4Rank6.SplitTwoTorsion

@[expose] public section

/-! Exact rank seven of the printed second example, Jaswal after
Theorem 8.1, DOI 10.5281/zenodo.23437117. The lower bound uses the seven
points; the upper bound uses the 512-class complete-descent certificate. -/
namespace Z2Z4Rank6.SecondExampleRankSeven

/-- The complete-descent upper certificate bounds rank by seven. -/
theorem rank_at_most_seven (hMW : MordellWeilTheorem)
    (hDescent : CompleteTwoDescentTheorem) : Module.rank ℤ (RationalPoints curve)≤7 := by
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
  apply RankModTwo.rank_le_of_descent_image_card κ hker j' (e.injective.comp hj) 7
  simpa only [show (2:ℕ)^(7+2)=512 by decide] using hcard

/-- The unnumbered rank claim after Theorem 8.1: the printed
E_{460019200,11180308689} has ordinary integral rank exactly seven. -/
theorem rank_eq_seven (hMazur : MazurTorsionTheorem) (hMW : MordellWeilTheorem)
    (hDescent : CompleteTwoDescentTheorem) : Module.rank ℤ (RationalPoints curve)=7 :=
  le_antisymm (rank_at_most_seven hMW hDescent) (rank_at_least_seven hMazur hDescent)

end Z2Z4Rank6.SecondExampleRankSeven
