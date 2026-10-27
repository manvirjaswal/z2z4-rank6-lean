module

public import Z2Z4Rank6.GExactRank
public import Z2Z4Rank6.SecondJacobianExactRank
public import Z2Z4Rank6.SplitFiberClassExact

@[expose] public section

/-!
# Exact local class spaces of the later upper fibers

The normalized h-twist at m=-80/3 and the translated split model of J2
have exactly sixteen everywhere locally soluble classes. Their
class spaces have dimension four. Every local class is the complete
descent image of a rational point. The J2 statement also records
the translation equivalence from the printed Jacobian point group.

Source: Jaswal, Sections 7 and 8, DOI 10.5281/zenodo.23437117.
-/
namespace Z2Z4Rank6
noncomputable section

namespace GTwistSelmer

theorem curve_rank_eq_two (hMazur : MazurTorsionTheorem) (hMW : MordellWeilTheorem)
    (hDescent : CompleteTwoDescentTheorem) (hReduction : GoodReductionHomomorphisms)
    (hFormal : FormalGoodReductionHomomorphisms) (hGT : GusicTadic.GusicTadicTheorem11) :
    Module.rank ℤ (RationalPoints curve)=2 := by
  apply le_antisymm (curve_rank_at_most_two hMW hDescent)
  obtain ⟨σ,hσ⟩ := GSpecialization.h_injective_normalized_fiber hGT
  have hle := σ.toIntLinearMap.rank_le_of_injective hσ
  rwa [GExactRank.h_rank_eq_two hMazur hMW hDescent hReduction hFormal hGT] at hle

theorem full_cover_finite_card_le :
    (fullTwoSelmerTriples r2 r3).Finite ∧ (fullTwoSelmerTriples r2 r3).ncard≤16 := by
  have hf := hStageThird.toFinset.finite_toSet
  refine ⟨hf.subset fullTwoSelmerTriples_subset_survivors,?_⟩
  calc
    _ ≤ (hStageThird.toFinset : Set ECFullTriple).ncard :=
      Set.ncard_le_ncard fullTwoSelmerTriples_subset_survivors hf
    _ = 16 := by rw [Set.ncard_coe_finset,hSurvivors_card]

abbrev actualClassSpace : Submodule (ZMod 2) (RatSquareClassAdd×RatSquareClassAdd) :=
  Submodule.span (ZMod 2) (fullTwoSelmerClasses r2 r3)

theorem model_exact (hMazur : MazurTorsionTheorem) (hMW : MordellWeilTheorem)
    (hDescent : CompleteTwoDescentTheorem) (hReduction : GoodReductionHomomorphisms)
    (hFormal : FormalGoodReductionHomomorphisms) (hGT : GusicTadic.GusicTadicTheorem11) :
    fullTwoSelmerClasses r2 r3=
        Set.range (completeDescentCoordinates curve 0 (-(r2:ℚ)) (-(r3:ℚ))) ∧
      (fullTwoSelmerClasses r2 r3).ncard=16 ∧
      (fullTwoSelmerTriples r2 r3).ncard=16 ∧
      (actualClassSpace : Set (RatSquareClassAdd×RatSquareClassAdd))=
        fullTwoSelmerClasses r2 r3 ∧
      Module.finrank (ZMod 2) actualClassSpace=4 := by
  let : AddGroup.FG (RationalPoints curve) := hMW curve inferInstance
  have hr := roots_nonzero_distinct
  have h := SplitFiberClassExact.coordinate_model_exact hDescent curve r2 r3 2
    curveElliptic rfl hr.1 hr.2.1 hr.2.2
    (curve_rank_eq_two hMazur hMW hDescent hReduction hFormal hGT)
    full_cover_finite_card_le.1 (by simpa using full_cover_finite_card_le.2)
  simpa only [actualClassSpace,show (2:ℕ)^(2+2)=16 by decide,
    show (2:ℕ)+2=4 by decide] using h

theorem classSpace_finrank (hMazur : MazurTorsionTheorem) (hMW : MordellWeilTheorem)
    (hDescent : CompleteTwoDescentTheorem) (hReduction : GoodReductionHomomorphisms)
    (hFormal : FormalGoodReductionHomomorphisms) (hGT : GusicTadic.GusicTadicTheorem11) :
    Module.finrank (ZMod 2) actualClassSpace=4 :=
  (model_exact hMazur hMW hDescent hReduction hFormal hGT).2.2.2.2

theorem every_local_class_realized (hMazur : MazurTorsionTheorem)
    (hMW : MordellWeilTheorem) (hDescent : CompleteTwoDescentTheorem)
    (hReduction : GoodReductionHomomorphisms) (hFormal : FormalGoodReductionHomomorphisms)
    (hGT : GusicTadic.GusicTadicTheorem11) (q : RatSquareClassAdd×RatSquareClassAdd)
    (hq : q∈fullTwoSelmerClasses r2 r3) :
    ∃P : RationalPoints curve,
      completeDescentCoordinates curve 0 (-(r2:ℚ)) (-(r3:ℚ)) P=q := by
  rw [(model_exact hMazur hMW hDescent hReduction hFormal hGT).1] at hq
  exact hq

end GTwistSelmer

namespace SecondJacobianSelmer

/-- This is the rational point-group isomorphism induced by the Weierstrass translation. -/
abbrev originalPointEquiv : RationalPoints J2 ≃+ RationalPoints (E (393129:ℚ) 25921) :=
  secondJacobianSplitEquiv

abbrev actualClassSpace : Submodule (ZMod 2) (RatSquareClassAdd×RatSquareClassAdd) :=
  Submodule.span (ZMod 2) (fullTwoSelmerClasses A B)

/-- Equality with the descent image on the printed Jacobian point
group, using its translated coordinates. -/
theorem original_model_exact (hDescent : CompleteTwoDescentTheorem) :
    fullTwoSelmerClasses A B=
        Set.range (fun P : RationalPoints J2 =>
          completeDescentCoordinates (E 393129 25921) 0
            (-(A:ℚ)) (-(B:ℚ)) (originalPointEquiv P)) ∧
      (fullTwoSelmerClasses A B).ncard=16 ∧
      (actualClassSpace : Set (RatSquareClassAdd×RatSquareClassAdd))=
        fullTwoSelmerClasses A B ∧
      Module.finrank (ZMod 2) actualClassSpace=4 := by
  obtain ⟨κ,hκ,_,hcard⟩ := secondJacobian_descent_image_exact hDescent
  have hcoords : ∀P,κ P=completeDescentCoordinates (E 393129 25921) 0
      (-(A:ℚ)) (-(B:ℚ)) (originalPointEquiv P) := by
    intro P
    simpa [A,B,originalPointEquiv] using hκ P
  have hsub : (κ.range : Set (RatSquareClassAdd×RatSquareClassAdd))⊆
      fullTwoSelmerClasses A B := by
    rintro _ ⟨P,rfl⟩
    rw [hcoords]
    exact split_completeDescent_coordinates_mem (E (393129:ℚ) 25921) A B
      (by norm_num [A]) (by norm_num [B]) (by norm_num [A,B])
      (by convert E_eq_splitWeierstrass (393129:ℚ) 25921 using 1; norm_num [A,B]) _
  have heq : fullTwoSelmerClasses A B=
      (κ.range : Set (RatSquareClassAdd×RatSquareClassAdd)) := by
    apply (Set.eq_of_subset_of_ncard_le hsub ?_ classes_finite).symm
    change (fullTwoSelmerClasses A B).ncard≤Nat.card κ.range
    rw [hcard]
    exact classes_card_le
  have hc : (fullTwoSelmerClasses A B).ncard=16 := by
    rw [heq]
    exact hcard
  refine ⟨heq.trans (congrArg Set.range (funext hcoords)),hc,?_,?_⟩
  · exact SelmerClassSpace.coe_span_eq_of_range _ κ heq
  · exact SelmerClassSpace.finrank_span_eq_of_range _ κ heq classes_finite 4 hc

/-- Surjectivity of the translation equivalence identifies this
same class set with the whole normalized rational point-group image. -/
theorem model_exact (hDescent : CompleteTwoDescentTheorem) :
    fullTwoSelmerClasses A B=
        Set.range (completeDescentCoordinates (E 393129 25921) 0 (-(A:ℚ)) (-(B:ℚ))) ∧
      (fullTwoSelmerClasses A B).ncard=16 ∧
      (actualClassSpace : Set (RatSquareClassAdd×RatSquareClassAdd))=
        fullTwoSelmerClasses A B ∧
      Module.finrank (ZMod 2) actualClassSpace=4 := by
  obtain ⟨heq,hcard,hspace,hdim⟩ := original_model_exact hDescent
  refine ⟨heq.trans ?_,hcard,hspace,hdim⟩
  ext q
  constructor
  · rintro ⟨P,rfl⟩
    exact ⟨originalPointEquiv P,rfl⟩
  · rintro ⟨P,rfl⟩
    exact ⟨originalPointEquiv.symm P,by simp only [AddEquiv.apply_symm_apply]⟩

theorem classSpace_finrank (hDescent : CompleteTwoDescentTheorem) :
    Module.finrank (ZMod 2) actualClassSpace=4 :=
  (model_exact hDescent).2.2.2

theorem every_local_class_realized_on_J2 (hDescent : CompleteTwoDescentTheorem)
    (q : RatSquareClassAdd×RatSquareClassAdd) (hq : q∈fullTwoSelmerClasses A B) :
    ∃P : RationalPoints J2,
      completeDescentCoordinates (E 393129 25921) 0
        (-(A:ℚ)) (-(B:ℚ)) (originalPointEquiv P)=q := by
  rw [(original_model_exact hDescent).1] at hq
  exact hq

end SecondJacobianSelmer
end
end Z2Z4Rank6
