module

public import Z2Z4Rank6.SecondTorsionCoverLaurent

@[expose] public section

/-! Rational polynomial-tuple range helpers for the signed-cover
charts. These are unconditional coefficient identities; coordinate
restriction maps are connected in SecondTorsionCoverCechRanges. -/
namespace Z2Z4Rank6.SecondTorsionCoverCechRangesHelpers
noncomputable section
open SecondTorsionCoverLaurent

def weightedReverseEquiv : EightLaurent ≃ₗ[ℚ] EightLaurent where
  toFun := weightedReverse
  invFun := weightedReverse
  left_inv := weightedReverse_involutive
  right_inv := weightedReverse_involutive
  map_add' f g := by
    funext i
    simp [weightedReverse,add_mul]
  map_smul' q f := by
    funext i
    simp [weightedReverse]

theorem polynomialTupleMap_injective : Function.Injective polynomialTupleMap := by
  intro f g h
  funext i
  apply Polynomial.toLaurent_injective
  exact congrFun h i

def negativePolynomialTupleMap : (Fin 8 → Polynomial ℚ) →ₗ[ℚ] EightLaurent :=
  weightedReverseEquiv.toLinearMap.comp polynomialTupleMap

@[simp] theorem negativePolynomialTupleMap_apply (f : Fin 8 → Polynomial ℚ) (i : Fin 8) :
    negativePolynomialTupleMap f i =
      LaurentPolynomial.invert ((f i).toLaurent) * LaurentPolynomial.T (-weights i) := rfl

theorem negativePolynomialTupleMap_range :
    LinearMap.range negativePolynomialTupleMap = negativeEight := by
  ext f
  constructor
  · rintro ⟨p,rfl⟩
    apply (weightedReverse_mem_negative_iff _).mpr
    rw [←polynomialTupleMap_range]
    exact ⟨p,rfl⟩
  · intro hf
    have hp : weightedReverse f ∈ positiveEight := by
      apply (weightedReverse_mem_negative_iff (weightedReverse f)).mp
      rwa [weightedReverse_involutive]
    rw [←polynomialTupleMap_range] at hp
    obtain ⟨p,hp⟩ := hp
    refine ⟨p,?_⟩
    change weightedReverse (polynomialTupleMap p) = f
    rw [hp,weightedReverse_involutive]

theorem negativePolynomialTupleMap_injective : Function.Injective negativePolynomialTupleMap :=
  weightedReverseEquiv.injective.comp polynomialTupleMap_injective

end
end Z2Z4Rank6.SecondTorsionCoverCechRangesHelpers
