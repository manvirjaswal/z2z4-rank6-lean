module

public import Z2Z4Rank6.ThirdTwistRankPoint
public import Z2Z4Rank6.ThirdTwistSelmer0Certificate
public import Z2Z4Rank6.ThirdTwistSelmer1Certificate
public import Z2Z4Rank6.ThirdTwistSelmer2Certificate
public import Z2Z4Rank6.ThirdTwistSelmer3Certificate
public import Z2Z4Rank6.SplitTwoTorsion
public import Z2Z4Rank6.RankModTwo

@[expose] public section

/-!
# The four exact third-twist ranks

The unnumbered paragraph after Proposition 7.2 in Jaswal,
DOI 10.5281/zenodo.23437117. The finite covering certificates give
fiber rank upper bounds 1,0,0,0. The third-twist section supplies the
lower bound 1. Specialization transports the bounds to Q(m).
-/
namespace Z2Z4Rank6.ThirdTwist
noncomputable section
open GusicTadic

theorem normalized_descent_image_bound (k : Fin 4)
    (κ : RationalPoints (curve k)→+(RatSquareClassAdd×RatSquareClassAdd))
    (hκ : ∀P,κ P=completeDescentCoordinates (curve k) 0 (-(r2 k:ℚ)) (-(r3 k:ℚ)) P) :
    Finite κ.range ∧ Nat.card κ.range≤2^((if k=0 then 1 else 0)+2) := by
  fin_cases k
  · simpa using Selmer0.descent_image_card_le κ hκ
  · simpa using Selmer1.descent_image_card_le κ hκ
  · simpa using Selmer2.descent_image_card_le κ hκ
  · simpa using Selmer3.descent_image_card_le κ hκ

theorem normalized_rank_le (hMW : MordellWeilTheorem)
    (hDescent : CompleteTwoDescentTheorem) (k : Fin 4) :
    Module.rank ℤ (RationalPoints (curve k))≤(if k=0 then 1 else 0 : ℕ) := by
  let : AddGroup.FG (RationalPoints (curve k)) := hMW (curve k) inferInstance
  obtain ⟨κ,hκ,hker⟩ := hDescent (curve k) 0 (-(r2 k:ℚ)) (-(r3 k:ℚ))
    (curveElliptic k) rfl
  obtain ⟨_,hcard⟩ := normalized_descent_image_bound k κ hκ
  let : (SplitTwoTorsion.curve (r2 k:ℚ) (r3 k:ℚ)).IsElliptic := by
    change (curve k).IsElliptic
    infer_instance
  obtain ⟨j,hj⟩ := SplitTwoTorsion.inclusion (r2 k:ℚ) (r3 k:ℚ)
    (by exact_mod_cast (roots_nonzero_distinct k).1)
  exact RankModTwo.rank_le_of_descent_image_card κ hker j hj _ hcard

theorem generic_rank_le (hMW : MordellWeilTheorem)
    (hDescent : CompleteTwoDescentTheorem) (hGT : GusicTadicTheorem11) (k : Fin 4) :
    Module.rank ℤ (genericModel (twistPolynomial k)).toAffine.Point≤
      (if k=0 then 1 else 0 : ℕ) :=
  generic_rank_le_of_normalized_rank hGT k _ (normalized_rank_le hMW hDescent k)

/-- The q3,q3*q1,q3*q2,q3*q12 twists over Q(m) have ranks 1,0,0,0. -/
theorem generic_rank (hMW : MordellWeilTheorem)
    (hDescent : CompleteTwoDescentTheorem) (hGT : GusicTadicTheorem11)
    (hOdd : OddPrimeTorsionIntegrality) (k : Fin 4) :
    Module.rank ℤ (genericModel (twistPolynomial k)).toAffine.Point=
      if k=0 then 1 else 0 := by
  have hu := generic_rank_le hMW hDescent hGT k
  by_cases hk : k=0
  · subst k
    simpa using le_antisymm hu (generic_rank_at_least_one hGT hOdd)
  · have hu0 : Module.rank ℤ (genericModel (twistPolynomial k)).toAffine.Point≤0 := by
      simpa [hk] using hu
    simpa [hk] using le_antisymm hu0 (show 0≤Module.rank ℤ
      (genericModel (twistPolynomial k)).toAffine.Point from zero_le)

theorem four_generic_ranks (hMW : MordellWeilTheorem)
    (hDescent : CompleteTwoDescentTheorem) (hGT : GusicTadicTheorem11)
    (hOdd : OddPrimeTorsionIntegrality) :
    (fun k : Fin 4 => Module.rank ℤ (genericModel (twistPolynomial k)).toAffine.Point)=
      ![1,0,0,0] := by
  funext k
  rw [generic_rank hMW hDescent hGT hOdd]
  fin_cases k <;> rfl

end
end Z2Z4Rank6.ThirdTwist
