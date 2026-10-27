import Z2Z4Rank6.GExampleRankSixLower
import Z2Z4Rank6.GExampleRankSixSelmerCertificate
import Z2Z4Rank6.MordellWeil
import Z2Z4Rank6.RankModTwo
import Z2Z4Rank6.PointScaling
import Z2Z4Rank6.SplitTwoTorsion
import Z2Z4Rank6.GReductionRank

/-!
# Exact rank six of the printed G-fiber example

The six points are independent and the complete-descent image has
at most 256 classes. Source: Jaswal, the example following Proposition 7.2.
-/
namespace Z2Z4Rank6.GExampleRankSix

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

/-- The unnumbered rank claim following Proposition 7.2: the printed
E_{379291648,212565977} has ordinary integral rank exactly six. -/
theorem rank_eq_six (hMazur : MazurTorsionTheorem) (hMW : MordellWeilTheorem)
    (hDescent : CompleteTwoDescentTheorem) : Module.rank ℤ (RationalPoints curve)=6 :=
  le_antisymm (rank_at_most_six hMW hDescent) (rank_at_least_six hMazur hDescent)


theorem curve_eq_rationalCurve : curve=GReductionData.rationalCurve := by
  ext <;> norm_num [curve,A,B,E,GReductionData.rationalCurve,GReductionData.a0,GReductionData.b0]

noncomputable def fiberScaling :
    RationalPoints (X GReductionData.baseM) ≃+ RationalPoints curve :=
  GReductionData.fiberScalingEquiv.trans (PointScaling.pointCongr curve_eq_rationalCurve.symm)

/-- The original unscaled fiber at the printed parameter has the same exact rank. -/
theorem original_fiber_rank_eq_six (hMazur : MazurTorsionTheorem) (hMW : MordellWeilTheorem)
    (hDescent : CompleteTwoDescentTheorem) :
    Module.rank ℤ (RationalPoints (X (291/53 : ℚ)))=6 :=
  fiberScaling.toIntLinearEquiv.rank_eq.trans (rank_eq_six hMazur hMW hDescent)

end Z2Z4Rank6.GExampleRankSix
