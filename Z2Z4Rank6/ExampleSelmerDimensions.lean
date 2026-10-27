import Z2Z4Rank6.FirstExampleRankSixSelmerExact
import Z2Z4Rank6.SecondExampleRankSevenSelmerExact
import Z2Z4Rank6.SelmerClassSpace

/-!
# F₂ class spaces of the two numerical examples

The modeled everywhere locally soluble squareclass sets are
proved to be the carriers of F₂ submodules, of dimensions 8 and 9.
This follows from their already proved equality with additive
complete-descent images and their exact cardinalities 256 and 512.
The examples occur before Proposition 6.2 and after Theorem 8.1 in
Jaswal, DOI 10.5281/zenodo.23437117. These are statements about the
explicit complete-two-descent model.
-/
namespace Z2Z4Rank6
noncomputable section

namespace FirstExampleRankSix.Selmer

abbrev actualClassSpace : Submodule (ZMod 2) (RatSquareClassAdd×RatSquareClassAdd) :=
  Submodule.span (ZMod 2) (fullTwoSelmerClasses r2 r3)

/-- The class set itself is closed under addition and F₂ scalars. -/
theorem classSpace_carrier (hMazur : MazurTorsionTheorem) (hMW : MordellWeilTheorem)
    (hReduction : GoodReductionHomomorphisms) (hDescent : CompleteTwoDescentTheorem) :
    (actualClassSpace : Set (RatSquareClassAdd×RatSquareClassAdd))=
      fullTwoSelmerClasses r2 r3 := by
  obtain ⟨κ,hκ,hker⟩ := hDescent curve 0 (-(r2:ℚ)) (-(r3:ℚ)) curveElliptic curve_split
  exact SelmerClassSpace.coe_span_eq_of_range _ κ
    (fullTwoSelmerClasses_eq_range hMazur hMW hReduction hDescent κ hκ hker)

/-- The first numerical example's local class space has dimension 8. -/
theorem classSpace_finrank (hMazur : MazurTorsionTheorem) (hMW : MordellWeilTheorem)
    (hReduction : GoodReductionHomomorphisms) (hDescent : CompleteTwoDescentTheorem) :
    Module.finrank (ZMod 2) actualClassSpace=8 := by
  obtain ⟨κ,hκ,hker⟩ := hDescent curve 0 (-(r2:ℚ)) (-(r3:ℚ)) curveElliptic curve_split
  apply SelmerClassSpace.finrank_span_eq_of_range _ κ
    (fullTwoSelmerClasses_eq_range hMazur hMW hReduction hDescent κ hκ hker)
    fullTwoSelmerClasses_card_le.1 8
  exact fullTwoSelmerClasses_card_eq hMazur hMW hReduction hDescent

/-- Both cardinality and dimension concern the modeled local set. -/
theorem modeled_dimension_eight (hMazur : MazurTorsionTheorem) (hMW : MordellWeilTheorem)
    (hReduction : GoodReductionHomomorphisms) (hDescent : CompleteTwoDescentTheorem) :
    (actualClassSpace : Set (RatSquareClassAdd×RatSquareClassAdd))=
        fullTwoSelmerClasses r2 r3 ∧
      (fullTwoSelmerClasses r2 r3).ncard=256 ∧
      Module.finrank (ZMod 2) actualClassSpace=8 :=
  ⟨classSpace_carrier hMazur hMW hReduction hDescent,
    fullTwoSelmerClasses_card_eq hMazur hMW hReduction hDescent,
    classSpace_finrank hMazur hMW hReduction hDescent⟩

end FirstExampleRankSix.Selmer

namespace SecondExampleRankSeven.Selmer

abbrev actualClassSpace : Submodule (ZMod 2) (RatSquareClassAdd×RatSquareClassAdd) :=
  Submodule.span (ZMod 2) (fullTwoSelmerClasses r2 r3)

theorem classSpace_carrier (hDescent : CompleteTwoDescentTheorem) :
    (actualClassSpace : Set (RatSquareClassAdd×RatSquareClassAdd))=
      fullTwoSelmerClasses r2 r3 := by
  obtain ⟨κ,hκ,hker⟩ := hDescent curve 0 (-(r2:ℚ)) (-(r3:ℚ)) curveElliptic curve_split
  exact SelmerClassSpace.coe_span_eq_of_range _ κ
    (fullTwoSelmerClasses_eq_range hDescent κ hκ hker)

/-- The second example's local class space has dimension 9. Only
the generic complete-descent theorem is needed for this class statement. -/
theorem classSpace_finrank (hDescent : CompleteTwoDescentTheorem) :
    Module.finrank (ZMod 2) actualClassSpace=9 := by
  obtain ⟨κ,hκ,hker⟩ := hDescent curve 0 (-(r2:ℚ)) (-(r3:ℚ)) curveElliptic curve_split
  apply SelmerClassSpace.finrank_span_eq_of_range _ κ
    (fullTwoSelmerClasses_eq_range hDescent κ hκ hker)
    fullTwoSelmerClasses_card_le.1 9
  exact fullTwoSelmerClasses_card_eq hDescent

theorem modeled_dimension_nine (hDescent : CompleteTwoDescentTheorem) :
    (actualClassSpace : Set (RatSquareClassAdd×RatSquareClassAdd))=
        fullTwoSelmerClasses r2 r3 ∧
      (fullTwoSelmerClasses r2 r3).ncard=512 ∧
      Module.finrank (ZMod 2) actualClassSpace=9 :=
  ⟨classSpace_carrier hDescent,fullTwoSelmerClasses_card_eq hDescent,
    classSpace_finrank hDescent⟩

end SecondExampleRankSeven.Selmer
end
end Z2Z4Rank6
