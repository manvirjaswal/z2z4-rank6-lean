import Z2Z4Rank6.SecondFamily
import Mathlib.Tactic

/-!
# Exact classification of the second family's parameter intersections

The two parameter equations printed before Theorem 8.1 have exactly the three
rational intersections stated there. A Bezout identity eliminates beta; its
remaining quadratic factor is strictly positive. All identities and the
rational classification are proved directly.
-/
namespace Z2Z4Rank6.SecondParameterSelection

variable {R : Type*} [CommRing R]

def firstCondition (l b : R) : R :=
  l^4-16*l^3+(16*b+30)*l^2+(160*b-16)*l+64*b^2+16*b+1

def secondCondition (l b : R) : R :=
  16*l^4+32*l^3+(8-8*b)*l^2-(24*b+8)*l+b^2-18*b+1

def linearCoefficient (l : R) : R := 528*l^2+1696*l+1168
def constantCoefficient (l : R) : R := -1023*l^4-2064*l^3-482*l^2+496*l-63
def secondLinearCoefficient (l : R) : R := -8*l^2-24*l-18

theorem linear_elimination (l b : R) :
    firstCondition l b-64*secondCondition l b=
      linearCoefficient l*b+constantCoefficient l := by
  unfold firstCondition secondCondition linearCoefficient constantCoefficient
  ring

theorem linear_elimination_factored (l b : R) :
    firstCondition l b-64*secondCondition l b=
      (l+1)*((528*l+1168)*b-1023*l^3-1041*l^2+559*l-63) := by
  unfold firstCondition secondCondition
  ring

/-- Exact Bezout certificate for eliminating beta from the two quadratics. -/
theorem elimination_identity (l b : R) :
    (linearCoefficient l^2+64*(linearCoefficient l*b+
        linearCoefficient l*secondLinearCoefficient l-constantCoefficient l))*secondCondition l b-
      (linearCoefficient l*b+linearCoefficient l*secondLinearCoefficient l-
        constantCoefficient l)*firstCondition l b=
      (l+1)^4*(9*l-1)*(1089*l-361)*(121*l^2+206*l+121) := by
  unfold firstCondition secondCondition linearCoefficient constantCoefficient secondLinearCoefficient
  ring

/-- The last factor of the elimination polynomial has no rational zero. -/
theorem remaining_factor_positive (l : ℚ) : 0<121*l^2+206*l+121 := by
  nlinarith [sq_nonneg (121*l+103)]

theorem rational_intersections (l b : ℚ) :
    firstCondition l b=0 ∧ secondCondition l b=0 ↔
      (l=-1 ∧ b=1) ∨ (l=1/9 ∧ b=1/81) ∨
        (l=361/1089 ∧ b=(161/1089)^2) := by
  constructor
  · rintro ⟨hfirst,hsecond⟩
    have hres : (l+1)^4*(9*l-1)*(1089*l-361)*(121*l^2+206*l+121)=0 := by
      rw [←elimination_identity,hfirst,hsecond]
      ring
    have hlinear : linearCoefficient l*b+constantCoefficient l=0 := by
      rw [←linear_elimination,hfirst,hsecond]
      ring
    have hprod : (l+1)^4*(9*l-1)*(1089*l-361)=0 :=
      (mul_eq_zero.mp hres).resolve_right (ne_of_gt (remaining_factor_positive l))
    rcases mul_eq_zero.mp hprod with hleft | hchosen
    · rcases mul_eq_zero.mp hleft with hdegenerate | hsmall
      · have hl : l=-1 := by have hh := eq_zero_of_pow_eq_zero hdegenerate; linarith
        subst l
        have hb : b=1 := by
          norm_num [secondCondition] at hsecond
          nlinarith [sq_nonneg (b-1)]
        exact Or.inl ⟨rfl,hb⟩
      · have hl : l=1/9 := by linarith
        subst l
        have hb : b=1/81 := by
          norm_num [linearCoefficient,constantCoefficient] at hlinear
          linarith
        exact Or.inr (Or.inl ⟨rfl,hb⟩)
    · have hl : l=361/1089 := by linarith
      subst l
      have hb : b=(161/1089)^2 := by
        norm_num [linearCoefficient,constantCoefficient] at hlinear
        linarith
      exact Or.inr (Or.inr ⟨rfl,hb⟩)
  · rintro (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩) <;>
      norm_num [firstCondition,secondCondition]

/-- The nondegenerate parameter pair is unique after removing beta=lambda². -/
theorem nondegenerate_intersection (l b : ℚ)
    (hfirst : firstCondition l b=0) (hsecond : secondCondition l b=0)
    (hbranch : b≠l^2) : l=361/1089 ∧ b=(161/1089)^2 := by
  rcases (rational_intersections l b).mp ⟨hfirst,hsecond⟩ with h | h | h
  · rcases h with ⟨rfl,rfl⟩
    norm_num at hbranch
  · rcases h with ⟨rfl,rfl⟩
    norm_num at hbranch
  · exact h

/-- Both prescribed section equations hold at the already defined constants. -/
theorem chosen_parameters :
    firstCondition (SecondFamily.lambda : ℚ) SecondFamily.beta=0 ∧
      secondCondition (SecondFamily.lambda : ℚ) SecondFamily.beta=0 :=
  ⟨SecondFamily.first_parameter_equation,SecondFamily.second_parameter_equation⟩

end Z2Z4Rank6.SecondParameterSelection
