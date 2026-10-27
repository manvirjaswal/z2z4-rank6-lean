import Z2Z4Rank6.GExampleRankSixExact
import Z2Z4Rank6.SelmerClassSpace

/-!
# Every locally soluble class of the G-fiber is realized

The eight independent rational descent images and the 256-class upper bound
identify the local covering classes with the rational descent image.
Source: Jaswal, the example following Proposition 7.2.
-/
namespace Z2Z4Rank6.GExampleRankSix.Selmer
noncomputable section

private theorem image_card_lower {G : Type} [AddCommGroup G]
    (κ : G→+(RatSquareClassAdd×RatSquareClassAdd)) [Finite κ.range]
    {n : ℕ} (P : Fin n→G)
    (hlin : LinearIndependent (ZMod 2) (fun i => κ (P i))) :
    2^n≤Nat.card κ.range := by
  let f : (Fin n→ZMod 2)→κ.range := fun v =>
    ⟨κ (∑i,(v i).val • P i),⟨∑i,(v i).val • P i,rfl⟩⟩
  have hformula (v : Fin n→ZMod 2) :
      (f v).val=∑i,v i • κ (P i) := by
    simp only [f,map_sum,map_nsmul,←Nat.cast_smul_eq_nsmul (ZMod 2),
      ZMod.natCast_zmod_val]
  have hf : Function.Injective f := by
    intro v w hvw
    apply hlin.fintypeLinearCombination_injective
    change (∑i,v i • κ (P i))=∑i,w i • κ (P i)
    rw [←hformula v,←hformula w]
    exact congrArg Subtype.val hvw
  have hcard := Nat.card_le_card_of_injective f hf
  simpa [Nat.card_eq_fintype_card] using hcard

/-- Either complete-descent root order has exactly 256 image classes. -/
theorem descent_image_card_eq (hDescent : CompleteTwoDescentTheorem)
    (κ : RationalPoints curve→+(RatSquareClassAdd×RatSquareClassAdd))
    (hκ : ∀P,κ P=completeDescentCoordinates curve 0 (-(r2:ℚ)) (-(r3:ℚ)) P)
    (hker : ∀P,κ P=0 ↔ ∃Q : RationalPoints curve,(2:ℕ) • Q=P) :
    Nat.card κ.range=256 := by
  obtain ⟨hfinite,hupper⟩ := descent_image_card_le κ hκ
  let : Finite κ.range := hfinite
  obtain ⟨κold,hκold,hkerold⟩ := hDescent curve 0 (-(A^2)) (-(B^2))
    curveElliptic (E_eq_splitWeierstrass A B)
  let e : κold.range≃+κ.range :=
    (RankModTwo.doublingQuotientEquivRange κold hkerold).symm.trans
      (RankModTwo.doublingQuotientEquivRange κ hker)
  let : Finite κold.range := Finite.of_equiv κ.range e.symm.toEquiv
  have hvalues : ∀i,κold (eightPoints i)=squareclasses i :=
    fun i => (hκold _).trans (descent_coordinates i)
  have hlin : LinearIndependent (ZMod 2) (fun i => κold (eightPoints i)) := by
    simpa only [hvalues] using squareclasses_independent
  have hlower := image_card_lower κold eightPoints hlin
  rw [Nat.card_congr e.toEquiv] at hlower
  exact le_antisymm hupper (by simpa using hlower)

/-- The locally soluble squareclass set is finite, of size at most 256. -/
theorem fullTwoSelmerClasses_card_le :
    (fullTwoSelmerClasses r2 r3).Finite ∧ (fullTwoSelmerClasses r2 r3).ncard≤256 := by
  obtain ⟨hfinite,hcard⟩ := fullTwoSelmerTriples_card_le
  exact ⟨hfinite.image _,(Set.ncard_image_le hfinite).trans hcard⟩

/-- All locally soluble classes are in the rational descent image. -/
theorem fullTwoSelmerClasses_eq_range (hDescent : CompleteTwoDescentTheorem)
    (κ : RationalPoints curve→+(RatSquareClassAdd×RatSquareClassAdd))
    (hκ : ∀P,κ P=completeDescentCoordinates curve 0 (-(r2:ℚ)) (-(r3:ℚ)) P)
    (hker : ∀P,κ P=0 ↔ ∃Q : RationalPoints curve,(2:ℕ) • Q=P) :
    fullTwoSelmerClasses r2 r3=(κ.range : Set (RatSquareClassAdd×RatSquareClassAdd)) := by
  have hsub : (κ.range : Set _)⊆fullTwoSelmerClasses r2 r3 := by
    rintro _ ⟨P,rfl⟩
    rw [hκ]
    exact split_completeDescent_coordinates_mem curve r2 r3 roots_nonzero_distinct.1
      roots_nonzero_distinct.2.1 roots_nonzero_distinct.2.2 curve_split P
  have hcard := descent_image_card_eq hDescent κ hκ hker
  apply (Set.eq_of_subset_of_ncard_le hsub ?_ fullTwoSelmerClasses_card_le.1).symm
  change (fullTwoSelmerClasses r2 r3).ncard≤Nat.card κ.range
  rw [hcard]
  exact fullTwoSelmerClasses_card_le.2

/-- The equality uses the coordinate function. -/
theorem fullTwoSelmerClasses_eq_descent_image (hDescent : CompleteTwoDescentTheorem) :
    fullTwoSelmerClasses r2 r3=
      Set.range (completeDescentCoordinates curve 0 (-(r2:ℚ)) (-(r3:ℚ))) := by
  obtain ⟨κ,hκ,hker⟩ := hDescent curve 0 (-(r2:ℚ)) (-(r3:ℚ)) curveElliptic curve_split
  calc
    _ = (κ.range : Set _) := fullTwoSelmerClasses_eq_range hDescent κ hκ hker
    _ = _ := congrArg Set.range (funext hκ)

theorem fullTwoSelmerClasses_card_eq (hDescent : CompleteTwoDescentTheorem) :
    (fullTwoSelmerClasses r2 r3).ncard=256 := by
  obtain ⟨κ,hκ,hker⟩ := hDescent curve 0 (-(r2:ℚ)) (-(r3:ℚ)) curveElliptic curve_split
  rw [fullTwoSelmerClasses_eq_range hDescent κ hκ hker]
  exact descent_image_card_eq hDescent κ hκ hker

/-- The canonical locally soluble triple set itself also has exactly 256 elements. -/
theorem fullTwoSelmerTriples_card_eq (hDescent : CompleteTwoDescentTheorem) :
    (fullTwoSelmerTriples r2 r3).ncard=256 := by
  apply le_antisymm fullTwoSelmerTriples_card_le.2
  calc
    256=(fullTwoSelmerClasses r2 r3).ncard := (fullTwoSelmerClasses_card_eq hDescent).symm
    _ ≤ (fullTwoSelmerTriples r2 r3).ncard :=
      Set.ncard_image_le fullTwoSelmerTriples_card_le.1

/-- Every modeled everywhere locally soluble covering class is represented
by a rational point of the printed elliptic curve. -/
theorem every_local_class_realized (hDescent : CompleteTwoDescentTheorem)
    (d : ECFullTriple) (hd : d∈fullTwoSelmerTriples r2 r3) :
    ∃P : RationalPoints curve,
      completeDescentCoordinates curve 0 (-(r2:ℚ)) (-(r3:ℚ)) P=
        (squareClass (d.1:ℚ),squareClass (d.2.1:ℚ)) := by
  have hmem : (squareClass (d.1:ℚ),squareClass (d.2.1:ℚ))∈fullTwoSelmerClasses r2 r3 :=
    ⟨d,hd,rfl⟩
  rw [fullTwoSelmerClasses_eq_descent_image hDescent] at hmem
  exact hmem


abbrev actualClassSpace : Submodule (ZMod 2) (RatSquareClassAdd×RatSquareClassAdd) :=
  Submodule.span (ZMod 2) (fullTwoSelmerClasses r2 r3)

theorem classSpace_carrier (hDescent : CompleteTwoDescentTheorem) :
    (actualClassSpace : Set (RatSquareClassAdd×RatSquareClassAdd))=
      fullTwoSelmerClasses r2 r3 := by
  obtain ⟨κ,hκ,hker⟩ := hDescent curve 0 (-(r2:ℚ)) (-(r3:ℚ)) curveElliptic curve_split
  exact SelmerClassSpace.coe_span_eq_of_range _ κ
    (fullTwoSelmerClasses_eq_range hDescent κ hκ hker)

theorem classSpace_finrank (hDescent : CompleteTwoDescentTheorem) :
    Module.finrank (ZMod 2) actualClassSpace=8 := by
  obtain ⟨κ,hκ,hker⟩ := hDescent curve 0 (-(r2:ℚ)) (-(r3:ℚ)) curveElliptic curve_split
  apply SelmerClassSpace.finrank_span_eq_of_range _ κ
    (fullTwoSelmerClasses_eq_range hDescent κ hκ hker)
    fullTwoSelmerClasses_card_le.1 8
  exact fullTwoSelmerClasses_card_eq hDescent

theorem modeled_dimension_eight (hDescent : CompleteTwoDescentTheorem) :
    (actualClassSpace : Set (RatSquareClassAdd×RatSquareClassAdd))=
        fullTwoSelmerClasses r2 r3 ∧
      (fullTwoSelmerClasses r2 r3).ncard=256 ∧
      Module.finrank (ZMod 2) actualClassSpace=8 :=
  ⟨classSpace_carrier hDescent,fullTwoSelmerClasses_card_eq hDescent,
    classSpace_finrank hDescent⟩

end
end Z2Z4Rank6.GExampleRankSix.Selmer
