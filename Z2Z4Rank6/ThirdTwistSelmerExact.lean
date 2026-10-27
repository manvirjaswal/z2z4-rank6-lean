module

public import Z2Z4Rank6.ThirdTwistRank
public import Z2Z4Rank6.SelmerClassSpace
public import Z2Z4Rank6.ThirdTwistSelmerLower

@[expose] public section

/-!
# The third-twist fiber Selmer dimensions

The canonical locally soluble classes have cardinalities 8,4,4,4 and
dimensions 3,2,2,2. Rational points realize all these classes.
The two split-root points supply two independent descent classes on every
fiber; the printed third-twist point supplies the third class at m=42.
Source: Jaswal, paragraph after Proposition 7.2, DOI 10.5281/zenodo.23437117.
-/
namespace Z2Z4Rank6.ThirdTwist
noncomputable section
open scoped BigOperators

private theorem image_card_lower {G : Type} [AddCommGroup G]
    (κ : G→+(RatSquareClassAdd×RatSquareClassAdd)) [Finite κ.range]
    {n : ℕ} (P : Fin n→G)
    (hlin : LinearIndependent (ZMod 2) (fun i => κ (P i))) : 2^n≤Nat.card κ.range := by
  let f : (Fin n→ZMod 2)→κ.range := fun v =>
    ⟨κ (∑i,(v i).val • P i),⟨∑i,(v i).val • P i,rfl⟩⟩
  have hformula (v : Fin n→ZMod 2) : (f v).val=∑i,v i • κ (P i) := by
    simp only [f,map_sum,map_nsmul,←Nat.cast_smul_eq_nsmul (ZMod 2),ZMod.natCast_zmod_val]
  have hf : Function.Injective f := by
    intro v w hvw
    apply hlin.fintypeLinearCombination_injective
    change (∑i,v i • κ (P i))=∑i,w i • κ (P i)
    rw [←hformula v,←hformula w]
    exact congrArg Subtype.val hvw
  simpa [Nat.card_eq_fintype_card] using Nat.card_le_card_of_injective f hf

theorem descent_image_card_eq (k : Fin 4)
    (κ : RationalPoints (curve k)→+(RatSquareClassAdd×RatSquareClassAdd))
    (hκ : ∀P,κ P=completeDescentCoordinates (curve k) 0 (-(r2 k:ℚ)) (-(r3 k:ℚ)) P) :
    Nat.card κ.range=2^((if k=0 then 1 else 0)+2) := by
  obtain ⟨hf,hu⟩ := normalized_descent_image_bound k κ hκ
  let : Finite κ.range := hf
  apply le_antisymm hu
  by_cases hk : k=0
  · subst k
    have hv : ∀i,κ (threePoints i)=threeClasses i := fun i => (hκ _).trans (three_descent_coordinates i)
    have hl : LinearIndependent (ZMod 2) (fun i => κ (threePoints i)) := by
      simpa only [hv] using three_classes_independent
    simpa using image_card_lower κ threePoints hl
  · have hv : ∀i,κ (torsionPoints k i)=torsionClasses k i :=
      fun i => (hκ _).trans (torsion_descent_coordinates k i)
    have hl : LinearIndependent (ZMod 2) (fun i => κ (torsionPoints k i)) := by
      simpa only [hv] using torsion_classes_independent k
    simpa [hk] using image_card_lower κ (torsionPoints k) hl

theorem fullTwoSelmerTriples_card_le (k : Fin 4) :
    (fullTwoSelmerTriples (r2 k) (r3 k)).Finite ∧
      (fullTwoSelmerTriples (r2 k) (r3 k)).ncard≤2^((if k=0 then 1 else 0)+2) := by
  fin_cases k
  all_goals
    first
    | exact ⟨Selmer0.survivors.finite_toSet.subset Selmer0.fullTwoSelmerTriples_subset_survivors,
        (Set.ncard_le_ncard Selmer0.fullTwoSelmerTriples_subset_survivors Selmer0.survivors.finite_toSet).trans
          (by simp [Selmer0.survivors_card])⟩
    | exact ⟨Selmer1.survivors.finite_toSet.subset Selmer1.fullTwoSelmerTriples_subset_survivors,
        (Set.ncard_le_ncard Selmer1.fullTwoSelmerTriples_subset_survivors Selmer1.survivors.finite_toSet).trans
          (by simp [Selmer1.survivors_card])⟩
    | exact ⟨Selmer2.survivors.finite_toSet.subset Selmer2.fullTwoSelmerTriples_subset_survivors,
        (Set.ncard_le_ncard Selmer2.fullTwoSelmerTriples_subset_survivors Selmer2.survivors.finite_toSet).trans
          (by simp [Selmer2.survivors_card])⟩
    | exact ⟨Selmer3.survivors.finite_toSet.subset Selmer3.fullTwoSelmerTriples_subset_survivors,
        (Set.ncard_le_ncard Selmer3.fullTwoSelmerTriples_subset_survivors Selmer3.survivors.finite_toSet).trans
          (by simp [Selmer3.survivors_card])⟩

theorem fullTwoSelmerClasses_card_le (k : Fin 4) :
    (fullTwoSelmerClasses (r2 k) (r3 k)).Finite ∧
      (fullTwoSelmerClasses (r2 k) (r3 k)).ncard≤2^((if k=0 then 1 else 0)+2) := by
  obtain ⟨hf,hc⟩ := fullTwoSelmerTriples_card_le k
  exact ⟨hf.image _,(Set.ncard_image_le hf).trans hc⟩

theorem fullTwoSelmerClasses_eq_range (k : Fin 4)
    (κ : RationalPoints (curve k)→+(RatSquareClassAdd×RatSquareClassAdd))
    (hκ : ∀P,κ P=completeDescentCoordinates (curve k) 0 (-(r2 k:ℚ)) (-(r3 k:ℚ)) P) :
    fullTwoSelmerClasses (r2 k) (r3 k)=(κ.range : Set (RatSquareClassAdd×RatSquareClassAdd)) := by
  have hsub : (κ.range : Set _)⊆fullTwoSelmerClasses (r2 k) (r3 k) := by
    rintro _ ⟨P,rfl⟩
    rw [hκ]
    exact split_completeDescent_coordinates_mem (curve k) (r2 k) (r3 k)
      (roots_nonzero_distinct k).1 (roots_nonzero_distinct k).2.1
      (roots_nonzero_distinct k).2.2 rfl P
  apply (Set.eq_of_subset_of_ncard_le hsub ?_ (fullTwoSelmerClasses_card_le k).1).symm
  change (fullTwoSelmerClasses (r2 k) (r3 k)).ncard≤Nat.card κ.range
  rw [descent_image_card_eq k κ hκ]
  exact (fullTwoSelmerClasses_card_le k).2

theorem fullTwoSelmerClasses_card_eq (hDescent : CompleteTwoDescentTheorem) (k : Fin 4) :
    (fullTwoSelmerClasses (r2 k) (r3 k)).ncard=2^((if k=0 then 1 else 0)+2) := by
  obtain ⟨κ,hκ,_⟩ := hDescent (curve k) 0 (-(r2 k:ℚ)) (-(r3 k:ℚ)) (curveElliptic k) rfl
  rw [fullTwoSelmerClasses_eq_range k κ hκ]
  exact descent_image_card_eq k κ hκ

theorem fullTwoSelmerTriples_card_eq (hDescent : CompleteTwoDescentTheorem) (k : Fin 4) :
    (fullTwoSelmerTriples (r2 k) (r3 k)).ncard=2^((if k=0 then 1 else 0)+2) := by
  apply le_antisymm (fullTwoSelmerTriples_card_le k).2
  rw [←fullTwoSelmerClasses_card_eq hDescent k]
  exact Set.ncard_image_le (fullTwoSelmerTriples_card_le k).1

theorem fullTwoSelmerClasses_eq_descent_image (hDescent : CompleteTwoDescentTheorem) (k : Fin 4) :
    fullTwoSelmerClasses (r2 k) (r3 k)=
      Set.range (completeDescentCoordinates (curve k) 0 (-(r2 k:ℚ)) (-(r3 k:ℚ))) := by
  obtain ⟨κ,hκ,_⟩ := hDescent (curve k) 0 (-(r2 k:ℚ)) (-(r3 k:ℚ)) (curveElliptic k) rfl
  calc
    _ = (κ.range : Set _) := fullTwoSelmerClasses_eq_range k κ hκ
    _ = _ := congrArg Set.range (funext hκ)

theorem every_local_class_realized (hDescent : CompleteTwoDescentTheorem) (k : Fin 4)
    (d : ECFullTriple) (hd : d∈fullTwoSelmerTriples (r2 k) (r3 k)) :
    ∃P : RationalPoints (curve k),
      completeDescentCoordinates (curve k) 0 (-(r2 k:ℚ)) (-(r3 k:ℚ)) P=
        (squareClass (d.1:ℚ),squareClass (d.2.1:ℚ)) := by
  have hm : (squareClass (d.1:ℚ),squareClass (d.2.1:ℚ))∈fullTwoSelmerClasses (r2 k) (r3 k) :=
    ⟨d,hd,rfl⟩
  rw [fullTwoSelmerClasses_eq_descent_image hDescent k] at hm
  exact hm

abbrev actualClassSpace (k : Fin 4) : Submodule (ZMod 2) (RatSquareClassAdd×RatSquareClassAdd) :=
  Submodule.span (ZMod 2) (fullTwoSelmerClasses (r2 k) (r3 k))

theorem classSpace_carrier (hDescent : CompleteTwoDescentTheorem) (k : Fin 4) :
    (actualClassSpace k : Set (RatSquareClassAdd×RatSquareClassAdd))=
      fullTwoSelmerClasses (r2 k) (r3 k) := by
  obtain ⟨κ,hκ,_⟩ := hDescent (curve k) 0 (-(r2 k:ℚ)) (-(r3 k:ℚ)) (curveElliptic k) rfl
  exact SelmerClassSpace.coe_span_eq_of_range _ κ (fullTwoSelmerClasses_eq_range k κ hκ)

theorem classSpace_finrank (hDescent : CompleteTwoDescentTheorem) (k : Fin 4) :
    Module.finrank (ZMod 2) (actualClassSpace k)=(if k=0 then 1 else 0)+2 := by
  obtain ⟨κ,hκ,_⟩ := hDescent (curve k) 0 (-(r2 k:ℚ)) (-(r3 k:ℚ)) (curveElliptic k) rfl
  exact SelmerClassSpace.finrank_span_eq_of_range _ κ
    (fullTwoSelmerClasses_eq_range k κ hκ) (fullTwoSelmerClasses_card_le k).1 _
    (fullTwoSelmerClasses_card_eq hDescent k)

theorem four_classSpace_dimensions (hDescent : CompleteTwoDescentTheorem) :
    (fun k : Fin 4 => Module.finrank (ZMod 2) (actualClassSpace k))=![3,2,2,2] := by
  funext k
  rw [classSpace_finrank hDescent k]
  fin_cases k <;> rfl

end
end Z2Z4Rank6.ThirdTwist
