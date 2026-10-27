module

public import Z2Z4Rank6.SecondQuarticMaps
public import Mathlib.FieldTheory.Separable

@[expose] public section

/-!
# Polynomial nonsingularity data for the second quartic

The quartic in Theorem 8.1(a) is separable of degree 4. These are
polynomial claims; the scheme-level genus/Jacobian foundation is separate.
The discriminant expression uses CFS's I,J convention (Definition 2.2, p. 4).
-/
namespace Z2Z4Rank6
open Polynomial

noncomputable def secondQuarticPolynomial : ℚ[X] :=
  1326538900*Polynomial.X^4-77611154441*Polynomial.X^2+1115619214900

theorem secondQuarticPolynomial_natDegree : secondQuarticPolynomial.natDegree=4 := by
  unfold secondQuarticPolynomial
  compute_degree!

theorem secondQuarticPolynomial_separable : secondQuarticPolynomial.Separable := by
  rw [separable_def]
  refine ⟨(-Polynomial.C (155222308882/87331247355688604866521 : ℚ)*Polynomial.X^2+
      Polynomial.C (1/1115619214900 : ℚ)),
    (Polynomial.C (77611154441/174662494711377209733042 : ℚ)*Polynomial.X^3-
      Polynomial.C (3063666721360134802481/231696593605686141284338828333800 : ℚ)*Polynomial.X),?_⟩
  apply Polynomial.funext
  intro x
  norm_num [secondQuarticPolynomial,derivative_add,derivative_sub,derivative_mul,derivative_pow]
  ring

theorem secondQuarticPolynomial_squarefree : Squarefree secondQuarticPolynomial :=
  secondQuarticPolynomial_separable.squarefree

theorem secondQuartic_invariant_I :
    (12*1326538900*1115619214900+(-77611154441)^2 : ℚ)=23782438727492469342481 := by norm_num

theorem secondQuartic_invariant_J :
    (72*1326538900*(-77611154441)*1115619214900-2*(-77611154441)^3 : ℚ)=
      -7334774245845152430286112662743758 := by norm_num

theorem secondQuartic_discriminant_value :
    ((4*23782438727492469342481^3-(-7334774245845152430286112662743758)^2)/27 : ℚ)=
      2^8*3^8*5^4*7^8*11^8*17^4*19^8*23^8*29^2*197^2*233^2 := by norm_num

end Z2Z4Rank6
