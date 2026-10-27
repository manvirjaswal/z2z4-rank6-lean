module

public import Z2Z4Rank6.FirstExampleRankSixExact
public import Z2Z4Rank6.FirstExampleRankSixDoubling

@[expose] public section

/-!
# Every locally soluble class of the c₀ example is realized

The canonical full two-covering class set equals the rational
complete-descent image and has 256 elements. The proved upper certificate
and the rank-six/full-two-torsion doubling bound force equality.
The hypotheses are the Mazur, Mordell--Weil, reduction and complete-descent theorems.
This is an explicit local-cover model statement, with no cohomological
Tate--Shafarevich group definition or claim.
Source: Jaswal, before Proposition 6.2, DOI 10.5281/zenodo.23437117.
-/
namespace Z2Z4Rank6.FirstExampleRankSix.Selmer
noncomputable section

/-- The complete-descent image has exactly 256 classes. The lower
bound uses the proved rank and full two-torsion in the doubling quotient. -/
theorem descent_image_card_eq (hMazur : MazurTorsionTheorem) (hMW : MordellWeilTheorem)
    (hReduction : GoodReductionHomomorphisms) (hDescent : CompleteTwoDescentTheorem)
    (κ : RationalPoints curve→+(RatSquareClassAdd×RatSquareClassAdd))
    (hκ : ∀P,κ P=completeDescentCoordinates curve 0 (-(r2:ℚ)) (-(r3:ℚ)) P)
    (hker : ∀P,κ P=0 ↔ ∃Q : RationalPoints curve,(2:ℕ) • Q=P) :
    Nat.card κ.range=256 := by
  let : AddGroup.FG (RationalPoints curve) := hMW curve curveElliptic
  obtain ⟨_,hupper⟩ := descent_image_card_le κ hκ
  have hcurve : SplitTwoTorsion.curve (r2:ℚ) (r3:ℚ)=curve := curve_split.symm
  let : (SplitTwoTorsion.curve (r2:ℚ) (r3:ℚ)).IsElliptic := by
    rw [hcurve]
    exact curveElliptic
  obtain ⟨j,hj⟩ := SplitTwoTorsion.inclusion (r2:ℚ) (r3:ℚ)
    (by exact_mod_cast roots_nonzero_distinct.1)
  let e := PointScaling.pointCongr hcurve
  let j' := e.toAddMonoidHom.comp j
  have hlower := RankModTwo.card_doubling_lower_of_rank_eq (RationalPoints curve)
    j' (e.injective.comp hj) 6 (rank_eq_six hMazur hMW hReduction hDescent)
  rw [RankModTwo.card_doubling_eq_range κ hker] at hlower
  exact le_antisymm hupper (by simpa using hlower)

/-- The locally soluble squareclass set is finite, of size at most 256. -/
theorem fullTwoSelmerClasses_card_le :
    (fullTwoSelmerClasses r2 r3).Finite ∧ (fullTwoSelmerClasses r2 r3).ncard≤256 := by
  obtain ⟨hfinite,hcard⟩ := fullTwoSelmerTriples_card_le
  exact ⟨hfinite.image _,(Set.ncard_image_le hfinite).trans hcard⟩

/-- All locally soluble classes are in the rational descent image. -/
theorem fullTwoSelmerClasses_eq_range (hMazur : MazurTorsionTheorem) (hMW : MordellWeilTheorem)
    (hReduction : GoodReductionHomomorphisms) (hDescent : CompleteTwoDescentTheorem)
    (κ : RationalPoints curve→+(RatSquareClassAdd×RatSquareClassAdd))
    (hκ : ∀P,κ P=completeDescentCoordinates curve 0 (-(r2:ℚ)) (-(r3:ℚ)) P)
    (hker : ∀P,κ P=0 ↔ ∃Q : RationalPoints curve,(2:ℕ) • Q=P) :
    fullTwoSelmerClasses r2 r3=(κ.range : Set (RatSquareClassAdd×RatSquareClassAdd)) := by
  have hsub : (κ.range : Set _)⊆fullTwoSelmerClasses r2 r3 := by
    rintro _ ⟨P,rfl⟩
    rw [hκ]
    exact split_completeDescent_coordinates_mem curve r2 r3 roots_nonzero_distinct.1
      roots_nonzero_distinct.2.1 roots_nonzero_distinct.2.2 curve_split P
  have hcard := descent_image_card_eq hMazur hMW hReduction hDescent κ hκ hker
  apply (Set.eq_of_subset_of_ncard_le hsub ?_ fullTwoSelmerClasses_card_le.1).symm
  change (fullTwoSelmerClasses r2 r3).ncard≤Nat.card κ.range
  rw [hcard]
  exact fullTwoSelmerClasses_card_le.2

/-- The equality uses the coordinate function. -/
theorem fullTwoSelmerClasses_eq_descent_image (hMazur : MazurTorsionTheorem) (hMW : MordellWeilTheorem)
    (hReduction : GoodReductionHomomorphisms) (hDescent : CompleteTwoDescentTheorem) :
    fullTwoSelmerClasses r2 r3=
      Set.range (completeDescentCoordinates curve 0 (-(r2:ℚ)) (-(r3:ℚ))) := by
  obtain ⟨κ,hκ,hker⟩ := hDescent curve 0 (-(r2:ℚ)) (-(r3:ℚ)) curveElliptic curve_split
  calc
    _ = (κ.range : Set _) := fullTwoSelmerClasses_eq_range hMazur hMW hReduction hDescent κ hκ hker
    _ = _ := congrArg Set.range (funext hκ)

theorem fullTwoSelmerClasses_card_eq (hMazur : MazurTorsionTheorem) (hMW : MordellWeilTheorem)
    (hReduction : GoodReductionHomomorphisms) (hDescent : CompleteTwoDescentTheorem) :
    (fullTwoSelmerClasses r2 r3).ncard=256 := by
  obtain ⟨κ,hκ,hker⟩ := hDescent curve 0 (-(r2:ℚ)) (-(r3:ℚ)) curveElliptic curve_split
  rw [fullTwoSelmerClasses_eq_range hMazur hMW hReduction hDescent κ hκ hker]
  exact descent_image_card_eq hMazur hMW hReduction hDescent κ hκ hker

/-- The canonical locally soluble triple set itself also has exactly 256 elements. -/
theorem fullTwoSelmerTriples_card_eq (hMazur : MazurTorsionTheorem) (hMW : MordellWeilTheorem)
    (hReduction : GoodReductionHomomorphisms) (hDescent : CompleteTwoDescentTheorem) :
    (fullTwoSelmerTriples r2 r3).ncard=256 := by
  apply le_antisymm fullTwoSelmerTriples_card_le.2
  calc
    256=(fullTwoSelmerClasses r2 r3).ncard := (fullTwoSelmerClasses_card_eq hMazur hMW hReduction hDescent).symm
    _ ≤ (fullTwoSelmerTriples r2 r3).ncard :=
      Set.ncard_image_le fullTwoSelmerTriples_card_le.1

/-- Every modeled everywhere locally soluble covering class is represented
by a rational point of the printed elliptic curve. -/
theorem every_local_class_realized (hMazur : MazurTorsionTheorem) (hMW : MordellWeilTheorem)
    (hReduction : GoodReductionHomomorphisms) (hDescent : CompleteTwoDescentTheorem)
    (d : ECFullTriple) (hd : d∈fullTwoSelmerTriples r2 r3) :
    ∃P : RationalPoints curve,
      completeDescentCoordinates curve 0 (-(r2:ℚ)) (-(r3:ℚ)) P=
        (squareClass (d.1:ℚ),squareClass (d.2.1:ℚ)) := by
  have hmem : (squareClass (d.1:ℚ),squareClass (d.2.1:ℚ))∈fullTwoSelmerClasses r2 r3 :=
    ⟨d,hd,rfl⟩
  rw [fullTwoSelmerClasses_eq_descent_image hMazur hMW hReduction hDescent] at hmem
  exact hmem

end
end Z2Z4Rank6.FirstExampleRankSix.Selmer
