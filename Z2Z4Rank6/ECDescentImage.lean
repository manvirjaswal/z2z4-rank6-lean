module

public import Z2Z4Rank6.ECFullSelmer
public import Z2Z4Rank6.ECSquarefreeCoordinates
public import Z2Z4Rank6.ECFullSupportRefinement
public import Z2Z4Rank6.BaseTorsion
public import Mathlib.Algebra.Group.Subgroup.Finite

@[expose] public section

/-!
# The complete-descent image has at most eight classes

The point coordinates give explicit
rational intersections of quadrics, including every two-torsion case. Square
extraction and the proved elementary local support refinement put them in
the kernel-checked full local-solubility model.
-/
namespace Z2Z4Rank6

theorem ecSplit_raw_descent_cover (P : RationalPoints (E (27 : ℚ) 22)) :
    ∃ q1 q2 q3 : ℚ, q1≠0 ∧ q2≠0 ∧ q3≠0 ∧ IsSquare (q1*q2*q3) ∧
      SplitCoverSoluble q1 q2 q3 729 484 ∧
      completeDescentCoordinates (E 27 22) 0 (-729) (-484) P =
        (squareClass q1,squareClass q2) := by
  cases P with
  | zero =>
    refine ⟨1,1,1,by norm_num,by norm_num,by norm_num,⟨1,by norm_num⟩,?_,?_⟩
    · refine ⟨![1,1,1,0],⟨0,by norm_num⟩,by norm_num,by norm_num⟩
    · simp only [completeDescentCoordinates,squareClass_one]
  | some x y h =>
    by_cases hx0 : x=0
    · subst x
      refine ⟨484/729,729,484,by norm_num,by norm_num,by norm_num,⟨484,by norm_num⟩,?_,?_⟩
      · refine ⟨![0,1,1,1],⟨3,by norm_num⟩,by norm_num,by norm_num⟩
      · norm_num [completeDescentCoordinates]
    by_cases hx2 : x = -729
    · subst x
      refine ⟨-729,245/729,-245,by norm_num,by norm_num,by norm_num,⟨245,by norm_num⟩,?_,?_⟩
      · refine ⟨![1,0,1,1],⟨3,by norm_num⟩,by norm_num,by norm_num⟩
      · norm_num [completeDescentCoordinates]
    by_cases hx3 : x = -484
    · subst x
      refine ⟨-484,245,-118580,by norm_num,by norm_num,by norm_num,⟨118580,by norm_num⟩,?_,?_⟩
      · refine ⟨![1,1,0,1],⟨3,by norm_num⟩,by norm_num,by norm_num⟩
      · norm_num [completeDescentCoordinates]
    · have heq : y^2=x*(x+729)*(x+484) := by
        convert (E_equation_iff 27 22 x y).mp h.1 using 1; norm_num
      refine ⟨x,x+729,x+484,hx0,by intro hh; apply hx2; linarith,
        by intro hh; apply hx3; linarith,⟨y,by simpa only [pow_two] using heq.symm⟩,?_,?_⟩
      · refine ⟨![1,1,1,1],⟨3,by norm_num⟩,?_,?_⟩ <;> norm_num
      · simp only [completeDescentCoordinates,ite_eq_right hx0,ite_eq_right hx2,sub_zero,sub_neg_eq_add]

theorem ecSplit_descent_coordinates_mem (P : RationalPoints (E (27 : ℚ) 22)) :
    completeDescentCoordinates (E 27 22) 0 (-729) (-484) P ∈
      fullTwoSelmerClasses 729 484 := by
  obtain ⟨q1,q2,q3,hq1,hq2,hq3,hsq,hcover,hcoord⟩ := ecSplit_raw_descent_cover P
  obtain ⟨d,hs1,hs2,hs3,hdsq,hdcover,hclass⟩ :=
    canonicalize_splitCover q1 q2 q3 729 484 hq1 hq2 hq3 hsq hcover
  have hloc : SplitCoverEverywhereLocallySoluble d 729 484 :=
    splitCover_global_implies_everywhere d 729 484 hdcover
  obtain ⟨hd1,hd2,hd3⟩ := splitCover_support_all d 729 484 hs1 hs2 hs3 hdsq hloc
  refine ⟨d,⟨hs1,hs2,hs3,hd1,hd2,hd3,hdsq,hloc⟩,?_⟩
  exact (hcoord.trans hclass).symm

theorem ecSplit_descent_image_bound
    (κ : RationalPoints (E (27 : ℚ) 22) →+ (RatSquareClassAdd × RatSquareClassAdd))
    (hκ : ∀ P, κ P = completeDescentCoordinates (E 27 22) 0 (-729) (-484) P) :
    Finite κ.range ∧ Nat.card κ.range ≤ 8 := by
  have hsub : (κ.range : Set _) ⊆ fullTwoSelmerClasses 729 484 := by
    rintro q ⟨P,rfl⟩
    rw [hκ]
    exact ecSplit_descent_coordinates_mem P
  have hfin : (fullTwoSelmerClasses 729 484).Finite := by
    rw [fullTwoSelmerClasses,ec_fullTwoSelmerTriples]
    exact (Finset.finite_toSet _).image _
  refine ⟨(hfin.subset hsub).to_subtype,?_⟩
  change (κ.range : Set (RatSquareClassAdd × RatSquareClassAdd)).ncard ≤ 8
  rw [←ec_fullTwoSelmerClasses_card]
  exact Set.ncard_le_ncard hsub hfin

/-- The complete-descent homomorphism on the printed E_C group has
kernel exactly 2E_C(Q), finite image, and image cardinality at most 8. -/
theorem ec_descent_image_bound (hDescent : CompleteTwoDescentTheorem) :
    ∃ κ : RationalPoints EC →+ (RatSquareClassAdd × RatSquareClassAdd),
      (∀ P, κ P = completeDescentCoordinates (E 27 22) 0 (-729) (-484) (ecSplitEquiv P)) ∧
      (∀ P, κ P = 0 ↔ ∃ Q : RationalPoints EC, (2 : ℕ) • Q = P) ∧
      Finite κ.range ∧ Nat.card κ.range ≤ 8 := by
  obtain ⟨κ,hκ,hker⟩ := hDescent (E (27 : ℚ) 22) 0 (-729) (-484)
    ecSplit_isElliptic (by convert E_eq_splitWeierstrass (27 : ℚ) 22 using 1; norm_num)
  let κEC : RationalPoints EC →+ (RatSquareClassAdd × RatSquareClassAdd) :=
    κ.comp ecSplitEquiv.toAddMonoidHom
  refine ⟨κEC,fun P => hκ (ecSplitEquiv P),?_,?_,?_⟩
  · intro P
    change κ (ecSplitEquiv P) = 0 ↔ _
    rw [hker]
    constructor
    · rintro ⟨Q,hQ⟩
      refine ⟨ecSplitEquiv.symm Q,ecSplitEquiv.injective ?_⟩
      simpa only [map_nsmul,AddEquiv.apply_symm_apply] using hQ
    · rintro ⟨Q,rfl⟩
      exact ⟨ecSplitEquiv Q,(map_nsmul ecSplitEquiv 2 Q).symm⟩
  · have hsub : (κEC.range : Set _) ⊆ fullTwoSelmerClasses 729 484 := by
      rintro q ⟨P,rfl⟩
      change κ (ecSplitEquiv P) ∈ _
      rw [hκ]
      exact ecSplit_descent_coordinates_mem _
    have hfin : (fullTwoSelmerClasses 729 484).Finite := by
      rw [fullTwoSelmerClasses,ec_fullTwoSelmerTriples]
      exact (Finset.finite_toSet _).image _
    exact (hfin.subset hsub).to_subtype
  · have hsub : (κEC.range : Set _) ⊆ fullTwoSelmerClasses 729 484 := by
      rintro q ⟨P,rfl⟩
      change κ (ecSplitEquiv P) ∈ _
      rw [hκ]
      exact ecSplit_descent_coordinates_mem _
    have hfin : (fullTwoSelmerClasses 729 484).Finite := by
      rw [fullTwoSelmerClasses,ec_fullTwoSelmerTriples]
      exact (Finset.finite_toSet _).image _
    change (κEC.range : Set (RatSquareClassAdd × RatSquareClassAdd)).ncard ≤ 8
    rw [←ec_fullTwoSelmerClasses_card]
    exact Set.ncard_le_ncard hsub hfin

end Z2Z4Rank6
