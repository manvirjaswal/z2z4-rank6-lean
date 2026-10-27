module

public import Z2Z4Rank6.FirstExampleRankSixDoubling
public import Z2Z4Rank6.SplitTwoTorsion
public import Z2Z4Rank6.PointScaling
public import Z2Z4Rank6.SelmerClassSpace

@[expose] public section

/-!
# Exact local classes from a proved rank and a covering bound

It identifies the explicit
locally soluble squareclass set with the rational descent image.
-/
namespace Z2Z4Rank6.SplitFiberClassExact
noncomputable section

abbrev ClassPair := RatSquareClassAdd×RatSquareClassAdd

/-- Generic exact class/image counts; every condition concerns a
curve, map, doubling kernel or local-cover set. -/
theorem eq_range_and_card (W : WeierstrassCurve ℚ) (r2 r3 : ℤ) (n : ℕ)
    (hGood : W.IsElliptic)
    (hW : W=splitWeierstrass 0 (-(r2:ℚ)) (-(r3:ℚ)))
    (hr2 : r2≠0) (hr3 : r3≠0) (hr23 : r2≠r3)
    [AddGroup.FG (RationalPoints W)] (hrank : Module.rank ℤ (RationalPoints W)=n)
    (hfinite : (fullTwoSelmerTriples r2 r3).Finite)
    (hupper : (fullTwoSelmerTriples r2 r3).ncard≤2^(n+2))
    (κ : RationalPoints W→+ClassPair)
    (hκ : ∀P,κ P=completeDescentCoordinates W 0 (-(r2:ℚ)) (-(r3:ℚ)) P)
    (hker : ∀P,κ P=0 ↔ ∃Q : RationalPoints W,(2:ℕ) • Q=P) :
    fullTwoSelmerClasses r2 r3=(κ.range : Set ClassPair) ∧
      Nat.card κ.range=2^(n+2) ∧
      (fullTwoSelmerClasses r2 r3).ncard=2^(n+2) ∧
      (fullTwoSelmerTriples r2 r3).ncard=2^(n+2) := by
  have hclassesFinite : (fullTwoSelmerClasses r2 r3).Finite := hfinite.image _
  have hclassesUpper : (fullTwoSelmerClasses r2 r3).ncard≤2^(n+2) :=
    (Set.ncard_image_le hfinite).trans hupper
  have hsub : (κ.range : Set ClassPair)⊆fullTwoSelmerClasses r2 r3 := by
    rintro _ ⟨P,rfl⟩
    rw [hκ]
    exact split_completeDescent_coordinates_mem W r2 r3 hr2 hr3 hr23 hW P
  have hu : Nat.card κ.range≤2^(n+2) :=
    (Set.ncard_le_ncard hsub hclassesFinite).trans hclassesUpper
  have hcurve : SplitTwoTorsion.curve (r2:ℚ) (r3:ℚ)=W := hW.symm
  let : (SplitTwoTorsion.curve (r2:ℚ) (r3:ℚ)).IsElliptic := by
    rw [hcurve]
    exact hGood
  obtain ⟨j,hj⟩ := SplitTwoTorsion.inclusion (r2:ℚ) (r3:ℚ) (by exact_mod_cast hr2)
  let e := PointScaling.pointCongr hcurve
  let j' := e.toAddMonoidHom.comp j
  have hl := RankModTwo.card_doubling_lower_of_rank_eq (RationalPoints W)
    j' (e.injective.comp hj) n hrank
  rw [RankModTwo.card_doubling_eq_range κ hker] at hl
  have hcard : Nat.card κ.range=2^(n+2) := le_antisymm hu hl
  have heq : fullTwoSelmerClasses r2 r3=(κ.range : Set ClassPair) := by
    apply (Set.eq_of_subset_of_ncard_le hsub ?_ hclassesFinite).symm
    change (fullTwoSelmerClasses r2 r3).ncard≤Nat.card κ.range
    rw [hcard]
    exact hclassesUpper
  have hc : (fullTwoSelmerClasses r2 r3).ncard=2^(n+2) := by
    rw [heq]
    exact hcard
  refine ⟨heq,hcard,hc,le_antisymm hupper ?_⟩
  calc
    2^(n+2)=(fullTwoSelmerClasses r2 r3).ncard := hc.symm
    _ ≤ (fullTwoSelmerTriples r2 r3).ncard := Set.ncard_image_le hfinite

/-- The same conclusion for the coordinate function, with
subspace closure and F₂ dimension n+2. -/
theorem coordinate_model_exact (hDescent : CompleteTwoDescentTheorem)
    (W : WeierstrassCurve ℚ) (r2 r3 : ℤ) (n : ℕ)
    (hGood : W.IsElliptic)
    (hW : W=splitWeierstrass 0 (-(r2:ℚ)) (-(r3:ℚ)))
    (hr2 : r2≠0) (hr3 : r3≠0) (hr23 : r2≠r3)
    [AddGroup.FG (RationalPoints W)] (hrank : Module.rank ℤ (RationalPoints W)=n)
    (hfinite : (fullTwoSelmerTriples r2 r3).Finite)
    (hupper : (fullTwoSelmerTriples r2 r3).ncard≤2^(n+2)) :
    fullTwoSelmerClasses r2 r3=
        Set.range (completeDescentCoordinates W 0 (-(r2:ℚ)) (-(r3:ℚ))) ∧
      (fullTwoSelmerClasses r2 r3).ncard=2^(n+2) ∧
      (fullTwoSelmerTriples r2 r3).ncard=2^(n+2) ∧
      (Submodule.span (ZMod 2) (fullTwoSelmerClasses r2 r3) : Set ClassPair)=
        fullTwoSelmerClasses r2 r3 ∧
      Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (fullTwoSelmerClasses r2 r3))=n+2 := by
  obtain ⟨κ,hκ,hker⟩ := hDescent W 0 (-(r2:ℚ)) (-(r3:ℚ)) hGood hW
  obtain ⟨heq,_,hc,ht⟩ := eq_range_and_card W r2 r3 n hGood hW hr2 hr3 hr23 hrank
    hfinite hupper κ hκ hker
  refine ⟨heq.trans (congrArg Set.range (funext hκ)),hc,ht,?_,?_⟩
  · exact SelmerClassSpace.coe_span_eq_of_range _ κ heq
  · exact SelmerClassSpace.finrank_span_eq_of_range _ κ heq (hfinite.image _) (n+2) hc

end
end Z2Z4Rank6.SplitFiberClassExact
