module

public import Z2Z4Rank6.GTwistSelmerCertificate
public import Z2Z4Rank6.SplitTwoTorsion
public import Z2Z4Rank6.MordellWeil
public import Z2Z4Rank6.RankModTwo

@[expose] public section

/-!
# h-twist rational rank upper bound

The sixteen-class complete-descent image and explicit full rational
two-torsion bound the integral rank by two. The hypotheses are the Mordell--Weil and complete
two-descent theorems.
Source: Jaswal, Proposition 7.2(b), DOI 10.5281/zenodo.23437117.
-/
namespace Z2Z4Rank6.GTwistSelmer

/-- The normalized h-twist rational point group at m=-80/3
has ordinary integral rank at most two. -/
theorem curve_rank_at_most_two (hMW : MordellWeilTheorem)
    (hDescent : CompleteTwoDescentTheorem) : Module.rank ℤ (RationalPoints curve)≤2 := by
  let : AddGroup.FG (RationalPoints curve) := hMW curve inferInstance
  obtain ⟨κ,hκ,hker⟩ := hDescent curve 0 (-(r2:ℚ)) (-(r3:ℚ)) curveElliptic rfl
  obtain ⟨_,hcard⟩ := descent_image_card_le κ hκ
  let : (SplitTwoTorsion.curve (r2:ℚ) (r3:ℚ)).IsElliptic := by
    change curve.IsElliptic
    infer_instance
  obtain ⟨j,hj⟩ := SplitTwoTorsion.inclusion (r2:ℚ) (r3:ℚ)
    (by exact_mod_cast roots_nonzero_distinct.1)
  apply RankModTwo.rank_le_of_descent_image_card κ hker j hj 2
  simpa only [show (2:ℕ)^(2+2)=16 by decide] using hcard

end Z2Z4Rank6.GTwistSelmer
