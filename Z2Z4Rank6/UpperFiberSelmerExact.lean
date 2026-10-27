module

public import Z2Z4Rank6.UpperFiberRanks
public import Z2Z4Rank6.SplitFiberClassExact

@[expose] public section

/-!
# Exact local classes for the four upper-bound fibers

The original 14/3 fiber has 32 locally soluble classes, and each of the
three normalized twist fibers has 8. Each set equals the coordinate
complete-descent image, and is the carrier of an F₂ submodule of
dimension 5 or 3.
Source: Jaswal Propositions 2.3/5.2, DOI 10.5281/zenodo.23437117.
No cohomological Tate--Shafarevich assertion is made.
-/
namespace Z2Z4Rank6
noncomputable section

namespace RankThreeSelmer

/-- The already checked certificate bounds the entire local-cover set. -/
theorem full_cover_finite_card_le :
    (fullTwoSelmerTriples r2 r3).Finite ∧ (fullTwoSelmerTriples r2 r3).ncard≤32 := by
  have hf := survivors.toFinset.finite_toSet
  refine ⟨hf.subset fullTwoSelmerTriples_subset_survivors,?_⟩
  calc
    _ ≤ (survivors.toFinset : Set ECFullTriple).ncard :=
      Set.ncard_le_ncard fullTwoSelmerTriples_subset_survivors hf
    _ = 32 := by rw [Set.ncard_coe_finset,survivors_card]

/-- The local-class span; its carrier is proved equal to the class set below. -/
abbrev actualClassSpace : Submodule (ZMod 2) (RatSquareClassAdd×RatSquareClassAdd) :=
  Submodule.span (ZMod 2) (fullTwoSelmerClasses r2 r3)

theorem model_exact (hMazur : MazurTorsionTheorem) (hMW : MordellWeilTheorem)
    (hDescent : CompleteTwoDescentTheorem) (hFormal : FormalGoodReductionHomomorphisms)
    (hGT : GusicTadic.GusicTadicTheorem11) :
    fullTwoSelmerClasses r2 r3=
        Set.range (completeDescentCoordinates curve 0 (-(r2:ℚ)) (-(r3:ℚ))) ∧
      (fullTwoSelmerClasses r2 r3).ncard=32 ∧
      (fullTwoSelmerTriples r2 r3).ncard=32 ∧
      (actualClassSpace : Set (RatSquareClassAdd×RatSquareClassAdd))=
        fullTwoSelmerClasses r2 r3 ∧
      Module.finrank (ZMod 2) actualClassSpace=5 := by
  let : AddGroup.FG (RationalPoints curve) := hMW curve curveElliptic
  have h := SplitFiberClassExact.coordinate_model_exact hDescent curve r2 r3 3
    curveElliptic curve_eq_split (by norm_num [r2,A]) (by norm_num [r3,B])
    (by norm_num [r2,r3,A,B]) (curve_rank_eq_three hMazur hMW hDescent hFormal hGT)
    full_cover_finite_card_le.1 (by simpa using full_cover_finite_card_le.2)
  simpa only [actualClassSpace,show (2:ℕ)^(3+2)=32 by decide,show (3:ℕ)+2=5 by decide] using h

theorem every_local_class_realized (hMazur : MazurTorsionTheorem) (hMW : MordellWeilTheorem)
    (hDescent : CompleteTwoDescentTheorem) (hFormal : FormalGoodReductionHomomorphisms)
    (hGT : GusicTadic.GusicTadicTheorem11) (d : ECFullTriple)
    (hd : d∈fullTwoSelmerTriples r2 r3) :
    ∃P : RationalPoints curve,
      completeDescentCoordinates curve 0 (-(r2:ℚ)) (-(r3:ℚ)) P=
        (squareClass (d.1:ℚ),squareClass (d.2.1:ℚ)) := by
  have hm : (squareClass (d.1:ℚ),squareClass (d.2.1:ℚ))∈fullTwoSelmerClasses r2 r3 := ⟨d,hd,rfl⟩
  rw [(model_exact hMazur hMW hDescent hFormal hGT).1] at hm
  exact hm

theorem classSpace_finrank (hMazur : MazurTorsionTheorem) (hMW : MordellWeilTheorem)
    (hDescent : CompleteTwoDescentTheorem) (hFormal : FormalGoodReductionHomomorphisms)
    (hGT : GusicTadic.GusicTadicTheorem11) : Module.finrank (ZMod 2) actualClassSpace=5 :=
  (model_exact hMazur hMW hDescent hFormal hGT).2.2.2.2

end RankThreeSelmer

namespace TwistSelmer

theorem full_cover_finite_card_le (k : Fin 3) :
    (fullTwoSelmerTriples (r2 k) (r3 k)).Finite ∧
      (fullTwoSelmerTriples (r2 k) (r3 k)).ncard≤8 := by
  have hf := (survivors k).finite_toSet
  refine ⟨hf.subset (fullTwoSelmerTriples_subset_survivors k),?_⟩
  calc
    _ ≤ (survivors k : Set ECFullTriple).ncard :=
      Set.ncard_le_ncard (fullTwoSelmerTriples_subset_survivors k) hf
    _ = 8 := by rw [Set.ncard_coe_finset,survivors_card]

abbrev actualClassSpace (k : Fin 3) : Submodule (ZMod 2) (RatSquareClassAdd×RatSquareClassAdd) :=
  Submodule.span (ZMod 2) (fullTwoSelmerClasses (r2 k) (r3 k))

theorem model_exact (hMazur : MazurTorsionTheorem)
    (hReduction : GoodReductionHomomorphisms) (hFormal : FormalGoodReductionHomomorphisms)
    (hGT : GusicTadic.GusicTadicTheorem11) (hMW : MordellWeilTheorem)
    (hDescent : CompleteTwoDescentTheorem) (k : Fin 3) :
    fullTwoSelmerClasses (r2 k) (r3 k)=
        Set.range (completeDescentCoordinates (curve k) 0 (-(r2 k:ℚ)) (-(r3 k:ℚ))) ∧
      (fullTwoSelmerClasses (r2 k) (r3 k)).ncard=8 ∧
      (fullTwoSelmerTriples (r2 k) (r3 k)).ncard=8 ∧
      (actualClassSpace k : Set (RatSquareClassAdd×RatSquareClassAdd))=
        fullTwoSelmerClasses (r2 k) (r3 k) ∧
      Module.finrank (ZMod 2) (actualClassSpace k)=3 := by
  let : AddGroup.FG (RationalPoints (curve k)) := hMW (curve k) inferInstance
  have hr := roots_nonzero_distinct k
  have h := SplitFiberClassExact.coordinate_model_exact hDescent (curve k) (r2 k) (r3 k) 1
    (curveElliptic k) rfl hr.1 hr.2.1 hr.2.2
    (curve_rank_eq_one hMazur hReduction hFormal hGT hMW hDescent k)
    (full_cover_finite_card_le k).1 (by simpa using (full_cover_finite_card_le k).2)
  simpa only [actualClassSpace,show (2:ℕ)^(1+2)=8 by decide,show (1:ℕ)+2=3 by decide] using h

theorem every_local_class_realized (hMazur : MazurTorsionTheorem)
    (hReduction : GoodReductionHomomorphisms) (hFormal : FormalGoodReductionHomomorphisms)
    (hGT : GusicTadic.GusicTadicTheorem11) (hMW : MordellWeilTheorem)
    (hDescent : CompleteTwoDescentTheorem) (k : Fin 3) (d : ECFullTriple)
    (hd : d∈fullTwoSelmerTriples (r2 k) (r3 k)) :
    ∃P : RationalPoints (curve k),
      completeDescentCoordinates (curve k) 0 (-(r2 k:ℚ)) (-(r3 k:ℚ)) P=
        (squareClass (d.1:ℚ),squareClass (d.2.1:ℚ)) := by
  have hm : (squareClass (d.1:ℚ),squareClass (d.2.1:ℚ))∈fullTwoSelmerClasses (r2 k) (r3 k) :=
    ⟨d,hd,rfl⟩
  rw [(model_exact hMazur hReduction hFormal hGT hMW hDescent k).1] at hm
  exact hm

theorem classSpace_finrank (hMazur : MazurTorsionTheorem)
    (hReduction : GoodReductionHomomorphisms) (hFormal : FormalGoodReductionHomomorphisms)
    (hGT : GusicTadic.GusicTadicTheorem11) (hMW : MordellWeilTheorem)
    (hDescent : CompleteTwoDescentTheorem) (k : Fin 3) :
    Module.finrank (ZMod 2) (actualClassSpace k)=3 :=
  (model_exact hMazur hReduction hFormal hGT hMW hDescent k).2.2.2.2

end TwistSelmer
end
end Z2Z4Rank6
