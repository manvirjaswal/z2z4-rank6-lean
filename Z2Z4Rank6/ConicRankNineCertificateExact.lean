module

public import Z2Z4Rank6.ConicRankNineCertificate
public import Z2Z4Rank6.ConicRankNineCertificateSelmerCertificate
public import Z2Z4Rank6.MordellWeil
public import Z2Z4Rank6.RankModTwo
public import Z2Z4Rank6.PointScaling
public import Z2Z4Rank6.SplitTwoTorsion
public import Z2Z4Rank6.ConicRankNineModels

@[expose] public section

/-! Exact rank nine of the integral fiber in Proposition 7.1.
Nine published points are certified by independent descent images;
the 2048-class upper certificate uses generic local covering theory.
The hypotheses are the Mazur, Mordell–Weil and complete two-descent theorems. -/
namespace Z2Z4Rank6.ConicRankNineCertificate

/-- The complete-descent upper certificate bounds rank by nine. -/
theorem rank_at_most_nine (hMW : MordellWeilTheorem)
    (hDescent : CompleteTwoDescentTheorem) : Module.rank ℤ (RationalPoints curve)≤9 := by
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
  apply RankModTwo.rank_le_of_descent_image_card κ hker j' (e.injective.comp hj) 9
  simpa only [show (2:ℕ)^(9+2)=2048 by decide] using hcard

/-- Proposition 7.1(b): the printed
E_{46529164800,95880799729} has ordinary integral rank exactly nine. -/
theorem rank_eq_nine (hMazur : MazurTorsionTheorem) (hMW : MordellWeilTheorem)
    (hDescent : CompleteTwoDescentTheorem) : Module.rank ℤ (RationalPoints curve) = 9 :=
  le_antisymm (rank_at_most_nine hMW hDescent) (rank_at_least_nine hMazur hDescent)

/-- Exact point-group identification with the published minimal equation. -/
noncomputable def integralPublishedEquiv : RationalPoints curve ≃+ RationalPoints ConicRankNine.publishedModel :=
  (VariableChangePoints.pointEquiv curve ConicRankNine.integralToPublished).symm.trans
    (PointScaling.pointCongr (by
      simpa only [curve,A,B,ConicRankNine.integralFiber] using
        ConicRankNine.integral_published_change))

/-- The published minimal equation has exact ordinary rank nine. -/
theorem published_rank_nine (hMazur : MazurTorsionTheorem) (hMW : MordellWeilTheorem)
    (hDescent : CompleteTwoDescentTheorem) :
    Module.rank ℤ (RationalPoints ConicRankNine.publishedModel)=9 :=
  integralPublishedEquiv.toIntLinearEquiv.rank_eq.symm.trans
    (rank_eq_nine hMazur hMW hDescent)

end Z2Z4Rank6.ConicRankNineCertificate
