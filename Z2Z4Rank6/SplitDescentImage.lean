module

public import Z2Z4Rank6.ECSquarefreeCoordinates
public import Z2Z4Rank6.ECFullSupportRefinement

@[expose] public section

/-!
# Complete-descent image in the explicit local-solubility model

A generic elementary companion to Silverman X.1.4: every rational point gives
a rational two-quadric covering point, including O and all three two-torsion
roots. Square extraction and proved local support refinement then put its
squareclasses in the canonical explicit full two-Selmer model.
-/
namespace Z2Z4Rank6

theorem splitWeierstrass_equation_iff (r2 r3 x y : ℚ) :
    (splitWeierstrass 0 (-r2) (-r3)).toAffine.Equation x y ↔
      y^2=x*(x+r2)*(x+r3) := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp only [splitWeierstrass,zero_mul,zero_add,add_zero]
  constructor <;> intro h <;> linear_combination h

theorem split_raw_descent_cover (W : WeierstrassCurve ℚ) (r2 r3 : ℚ)
    (hr2 : r2≠0) (hr3 : r3≠0) (hr23 : r2≠r3)
    (hW : W=splitWeierstrass 0 (-r2) (-r3)) (P : RationalPoints W) :
    ∃ q1 q2 q3 : ℚ, q1≠0 ∧ q2≠0 ∧ q3≠0 ∧ IsSquare (q1*q2*q3) ∧
      SplitCoverSoluble q1 q2 q3 r2 r3 ∧
      completeDescentCoordinates W 0 (-r2) (-r3) P = (squareClass q1,squareClass q2) := by
  have h32 : r3-r2≠0 := sub_ne_zero.mpr hr23.symm
  have h23 : r2-r3≠0 := sub_ne_zero.mpr hr23
  cases P with
  | zero =>
    refine ⟨1,1,1,by norm_num,by norm_num,by norm_num,⟨1,by norm_num⟩,?_,?_⟩
    · refine ⟨![1,1,1,0],⟨0,by norm_num⟩,by norm_num,by norm_num⟩
    · simp only [completeDescentCoordinates,squareClass_one]
  | some x y h =>
    by_cases hx0 : x=0
    · subst x
      refine ⟨r3/r2,r2,r3,div_ne_zero hr3 hr2,hr2,hr3,⟨r3,?_⟩,?_,?_⟩
      · field_simp
      · refine ⟨![0,1,1,1],⟨3,by norm_num⟩,by norm_num,by norm_num⟩
      · simp [completeDescentCoordinates,sub_neg_eq_add]
    by_cases hx2 : x = -r2
    · subst x
      refine ⟨-r2,(r3-r2)/(-r2),r3-r2,neg_ne_zero.mpr hr2,
        div_ne_zero h32 (neg_ne_zero.mpr hr2),h32,⟨r3-r2,?_⟩,?_,?_⟩
      · field_simp
      · refine ⟨![1,0,1,1],⟨3,by norm_num⟩,?_,?_⟩ <;> norm_num
      · simp [completeDescentCoordinates,hr2,sub_eq_add_neg,add_comm]
    by_cases hx3 : x = -r3
    · subst x
      refine ⟨-r3,r2-r3,(-r3)*(r2-r3),neg_ne_zero.mpr hr3,h23,
        mul_ne_zero (neg_ne_zero.mpr hr3) h23,⟨(-r3)*(r2-r3),by ring⟩,?_,?_⟩
      · refine ⟨![1,1,0,1],⟨3,by norm_num⟩,?_,?_⟩ <;> norm_num
      · simp [completeDescentCoordinates,hr3,hx2,sub_eq_add_neg,add_comm]
    · have heq : y^2=x*(x+r2)*(x+r3) := by
        rw [hW] at h
        exact (splitWeierstrass_equation_iff r2 r3 x y).mp h.1
      refine ⟨x,x+r2,x+r3,hx0,by intro hh; apply hx2; linarith,
        by intro hh; apply hx3; linarith,⟨y,by simpa only [pow_two] using heq.symm⟩,?_,?_⟩
      · refine ⟨![1,1,1,1],⟨3,by norm_num⟩,?_,?_⟩ <;> norm_num
      · simp only [completeDescentCoordinates,ite_eq_right hx0,ite_eq_right hx2,sub_zero,sub_neg_eq_add]

theorem split_completeDescent_coordinates_mem (W : WeierstrassCurve ℚ) (r2 r3 : ℤ)
    (hr2 : r2≠0) (hr3 : r3≠0) (hr23 : r2≠r3)
    (hW : W=splitWeierstrass 0 (-(r2 : ℚ)) (-(r3 : ℚ))) (P : RationalPoints W) :
    completeDescentCoordinates W 0 (-(r2 : ℚ)) (-(r3 : ℚ)) P ∈
      fullTwoSelmerClasses r2 r3 := by
  obtain ⟨q1,q2,q3,hq1,hq2,hq3,hsq,hcover,hcoord⟩ :=
    split_raw_descent_cover W r2 r3 (by exact_mod_cast hr2) (by exact_mod_cast hr3)
      (by exact_mod_cast hr23) hW P
  obtain ⟨d,hs1,hs2,hs3,hdsq,hdcover,hclass⟩ :=
    canonicalize_splitCover q1 q2 q3 r2 r3 hq1 hq2 hq3 hsq hcover
  have hloc := splitCover_global_implies_everywhere d r2 r3 hdcover
  obtain ⟨hd1,hd2,hd3⟩ := splitCover_support_all d r2 r3 hs1 hs2 hs3 hdsq hloc
  refine ⟨d,⟨hs1,hs2,hs3,hd1,hd2,hd3,hdsq,hloc⟩,?_⟩
  exact (hcoord.trans hclass).symm

theorem split_descent_image_card_le (W : WeierstrassCurve ℚ) (r2 r3 : ℤ)
    (hr2 : r2≠0) (hr3 : r3≠0) (hr23 : r2≠r3)
    (hW : W=splitWeierstrass 0 (-(r2 : ℚ)) (-(r3 : ℚ)))
    (s : Finset ECFullTriple) (hs : fullTwoSelmerTriples r2 r3 ⊆ (s : Set ECFullTriple))
    (κ : RationalPoints W →+ (RatSquareClassAdd × RatSquareClassAdd))
    (hκ : ∀ P, κ P=completeDescentCoordinates W 0 (-(r2 : ℚ)) (-(r3 : ℚ)) P) :
    Finite κ.range ∧ Nat.card κ.range ≤ s.card := by
  let f : ECFullTriple → RatSquareClassAdd × RatSquareClassAdd :=
    fun d => (squareClass (d.1 : ℚ),squareClass (d.2.1 : ℚ))
  have hsub : (κ.range : Set _) ⊆ f '' (s : Set ECFullTriple) := by
    rintro q ⟨P,rfl⟩
    obtain ⟨d,hd,hcoord⟩ := split_completeDescent_coordinates_mem W r2 r3 hr2 hr3 hr23 hW P
    exact ⟨d,hs hd,hcoord.trans (hκ P).symm⟩
  have hfin : (f '' (s : Set ECFullTriple)).Finite := (Finset.finite_toSet s).image f
  refine ⟨(hfin.subset hsub).to_subtype,?_⟩
  change (κ.range : Set (RatSquareClassAdd × RatSquareClassAdd)).ncard ≤ s.card
  calc
    _ ≤ (f '' (s : Set ECFullTriple)).ncard := Set.ncard_le_ncard hsub hfin
    _ ≤ (s : Set ECFullTriple).ncard := Set.ncard_image_le (Finset.finite_toSet s)
    _ = s.card := Set.ncard_coe_finset s

end Z2Z4Rank6
