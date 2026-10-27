module

public import Z2Z4Rank6.SecondJInvariant
public import Z2Z4Rank6.TorsionSquareLiftData
public import Mathlib.FieldTheory.Separable

@[expose] public section

/-!
# Rational-point data for the second signed torsion covers

The signed square lifts are the points of the displayed genus-nine
covers. Their rational parameter fibers are finite. Source: Jaswal,
Theorem 8.1(c), DOI 10.5281/zenodo.23437117.
-/

namespace Z2Z4Rank6.SecondTorsionHyperelliptic

open Polynomial SecondFamily
open scoped BigOperators
noncomputable section

abbrev sign := TorsionHyperelliptic.sign

@[ext] structure SquareLift (ε : Bool) where
  c : G2Point ℚ
  r : ℚ
  r_sq : r^2=sign ε*V c.W

private theorem rational_eq_of_sq_eq_and_sign (r s : ℚ) (hsq : r^2=s^2)
    (hsign : decide (0≤r)=decide (0≤s)) : r=s := by
  have hiff : (0≤r)↔(0≤s) := decide_eq_decide.mp hsign
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
  · exact h
  · by_cases hr : 0≤r
    · have hs := hiff.mp hr
      linarith
    · have hs : ¬0≤s := mt hiff.mpr hr
      linarith

/-- Each rational G₂ fiber over W has at most eight points. -/
theorem G2_W_fiber_ncard_le_eight (w : ℚ) : {P : G2Point ℚ | P.W=w}.ncard≤8 := by
  classical
  let S : Set (G2Point ℚ) := {P | P.W=w}
  have : Finite S := (finite_G2Point_W_fiber w).to_subtype
  let f : S → Bool×Bool×Bool := fun P =>
    (decide (0≤P.val.s1),decide (0≤P.val.s2),decide (0≤P.val.s3))
  have hf : Function.Injective f := by
    intro P Q he
    have hw : P.val.W=Q.val.W := P.property.trans Q.property.symm
    have h1 := congrArg Prod.fst he
    have h2 := congrArg (fun z : Bool×Bool×Bool => z.2.1) he
    have h3 := congrArg (fun z : Bool×Bool×Bool => z.2.2) he
    apply Subtype.ext
    apply G2Point.ext hw
    · apply rational_eq_of_sq_eq_and_sign _ _ _ h1
      rw [P.val.s1_sq,Q.val.s1_sq,hw]
    · apply rational_eq_of_sq_eq_and_sign _ _ _ h2
      rw [P.val.s2_sq,Q.val.s2_sq,hw]
    · apply rational_eq_of_sq_eq_and_sign _ _ _ h3
      rw [P.val.s3_sq,Q.val.s3_sq,hw]
  have hc := Nat.card_le_card_of_injective f hf
  change Nat.card S≤8
  norm_num only [Nat.card_prod,Nat.card_eq_fintype_card,Fintype.card_prod,Fintype.card_bool] at hc
  exact hc

theorem finite_lift_W_fiber (ε : Bool) (w : ℚ) :
    {P : SquareLift ε | P.c.W=w}.Finite := by
  let f : SquareLift ε → G2Point ℚ×ℚ := fun P => (P.c,P.r)
  have hsub : f '' {P : SquareLift ε | P.c.W=w} ⊆
      {P : G2Point ℚ | P.W=w} ×ˢ {r : ℚ | r^2=sign ε*V w} := by
    rintro _ ⟨P,hP,rfl⟩
    change P.c.W=w at hP
    refine ⟨hP,?_⟩
    change P.r^2=sign ε*V w
    simpa only [hP] using P.r_sq
  exact (((finite_G2Point_W_fiber w).prod
    (TorsionHyperelliptic.finite_square_fiber (sign ε*V w))).subset hsub).of_finite_image (by
      intro P hP Q hQ he
      apply SquareLift.ext
      · exact congrArg Prod.fst he
      · exact congrArg Prod.snd he)

end
end Z2Z4Rank6.SecondTorsionHyperelliptic
