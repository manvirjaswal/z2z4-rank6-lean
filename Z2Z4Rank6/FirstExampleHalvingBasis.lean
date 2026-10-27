module

public import Z2Z4Rank6.FirstExampleHalving

@[expose] public section

/-! The eight explicit replacement classes form a basis of the whole
complete-descent image. Only the complete-descent theorem is needed:
the lower certificate consists of eight points, and the local upper certificate bounds the whole
image by 256. -/
namespace Z2Z4Rank6.FirstExampleHalving
noncomputable section
open ExampleOriginalDescent

private theorem replacement_span_eq_range
    (κ : RationalPoints curve →+ ClassPair)
    (hκ : ∀P,κ P=completeDescentCoordinates curve 0 (-(A^2)) (-(B^2)) P) :
    (replacementSpan : Set ClassPair)=(κ.range : Set ClassPair) := by
  have h2 : (FirstExampleRankSix.Selmer.r2:ℚ)=A^2 := by
    norm_num [FirstExampleRankSix.Selmer.r2,FirstExampleRankSix.A]
  have h3 : (FirstExampleRankSix.Selmer.r3:ℚ)=B^2 := by
    norm_num [FirstExampleRankSix.Selmer.r3,FirstExampleRankSix.B]
  have hκ' : ∀P,κ P=completeDescentCoordinates curve 0
      (-(FirstExampleRankSix.Selmer.r2:ℚ)) (-(FirstExampleRankSix.Selmer.r3:ℚ)) P := by
    simpa only [h2,h3] using hκ
  obtain ⟨hfinite,hupper⟩ := FirstExampleRankSix.Selmer.descent_image_card_le κ hκ'
  let : Finite κ.range := hfinite
  have hsub : replacementSpan≤SelmerClassSpace.rangeSpace κ := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    refine ⟨replacementPoints i,?_⟩
    rw [hκ]
    exact descent_coordinates i
  let : FiniteDimensional (ZMod 2) replacementSpan :=
    FiniteDimensional.span_of_finite (ZMod 2) (Set.finite_range classes)
  let : Finite replacementSpan := Module.finite_of_finite (ZMod 2)
  let : Fintype replacementSpan := Fintype.ofFinite _
  have hc : Nat.card replacementSpan=256 := by
    rw [Nat.card_eq_fintype_card,Module.card_eq_pow_finrank (K:=ZMod 2) (V:=replacementSpan),ZMod.card,replacementSpan_finrank]
    rfl
  apply Set.eq_of_subset_of_ncard_le (show (replacementSpan:Set ClassPair)⊆
    (κ.range:Set ClassPair) from hsub)
  · change Nat.card κ.range≤Nat.card replacementSpan
    rw [hc]
    exact hupper

/-- The explicit eight classes span the whole coordinate image. -/
theorem replacement_span_eq_descent_image (hDescent : CompleteTwoDescentTheorem) :
    (replacementSpan : Set ClassPair)=
      Set.range (completeDescentCoordinates curve 0 (-(A^2)) (-(B^2))) := by
  obtain ⟨κ,hκ,_⟩ := hDescent curve 0 (-(A^2)) (-(B^2))
    FirstExampleRankSix.curveElliptic (E_eq_splitWeierstrass A B)
  calc
    _=(κ.range:Set ClassPair) := replacement_span_eq_range κ hκ
    _=Set.range (completeDescentCoordinates curve 0 (-(A^2)) (-(B^2))) :=
      congrArg Set.range (funext hκ)

def actualDescentSpan : Submodule (ZMod 2) ClassPair :=
  Submodule.span (ZMod 2)
    (Set.range (completeDescentCoordinates curve 0 (-(A^2)) (-(B^2))))

theorem actualDescentSpan_eq_replacementSpan (hDescent : CompleteTwoDescentTheorem) :
    actualDescentSpan=replacementSpan := by
  unfold actualDescentSpan
  rw [←replacement_span_eq_descent_image hDescent,Submodule.span_eq]

/-- A basis of the whole complete-descent image, with the eight
point-coordinate images in the printed replacement order. -/
def actualDescentBasis (hDescent : CompleteTwoDescentTheorem) :
    Module.Basis (Fin 8) (ZMod 2) actualDescentSpan :=
  replacementBasis.map (LinearEquiv.ofEq _ _
    (actualDescentSpan_eq_replacementSpan hDescent).symm)

theorem actualDescentBasis_coordinates (hDescent : CompleteTwoDescentTheorem) (i : Fin 8) :
    (actualDescentBasis hDescent i : ClassPair)=completeDescentCoordinates curve
      0 (-(A^2)) (-(B^2)) (replacementPoints i) := by
  simpa only [actualDescentBasis,Module.Basis.map_apply,LinearEquiv.coe_ofEq_apply] using
    replacementBasis_coordinates i

theorem actualDescentSpan_finrank (hDescent : CompleteTwoDescentTheorem) :
    Module.finrank (ZMod 2) actualDescentSpan=8 := by
  rw [actualDescentSpan_eq_replacementSpan hDescent]
  exact replacementSpan_finrank

end
end Z2Z4Rank6.FirstExampleHalving
