module

public import Z2Z4Rank6.GQuarticMaps
public import Mathlib.FieldTheory.Separable

@[expose] public section

/-!
# Checked polynomial geometry data for G

The quartic is squarefree of degree 4, has its printed rational point, and has
the invariants/discriminant of Proposition 7.2(a). These are polynomial facts;
the scheme-level genus and Jacobian-variety statement remains separate.
The invariant convention is CFS, arXiv:0908.1741v1, Definition 2.2, p. 4.
-/
namespace Z2Z4Rank6
open Polynomial

noncomputable def gQuarticPolynomial : ℚ[X] := 99*Polynomial.X^4-9998*Polynomial.X^2+970299

theorem gQuarticPolynomial_natDegree : gQuarticPolynomial.natDegree=4 := by
  unfold gQuarticPolynomial
  compute_degree!

theorem gQuarticPolynomial_separable : gQuarticPolynomial.Separable := by
  rw [separable_def]
  refine ⟨(Polynomial.C (4999/696553149600 : ℚ)*Polynomial.X^2+Polynomial.C (1/970299 : ℚ)),
    (-Polynomial.C (4999/2786212598400 : ℚ)*Polynomial.X^3-Polynomial.C (46079599/275835047241600 : ℚ)*Polynomial.X),?_⟩
  apply Polynomial.funext
  intro x
  norm_num [gQuarticPolynomial,derivative_add,derivative_sub,derivative_mul,derivative_pow]
  ring

theorem gQuarticPolynomial_squarefree : Squarefree gQuarticPolynomial :=
  gQuarticPolynomial_separable.squarefree

def gQuarticPrintedPoint : GQuarticPoint where
  m:=57
  eta:=31836
  equation:=by norm_num [gQuartic]

theorem gQuartic_invariant_I :
    (12*99*970299+(-9998)^2 : ℚ)=1252675216 := by norm_num

theorem gQuartic_invariant_J :
    (72*99*(-9998)*970299-2*(-9998)^3 : ℚ)=-67150279897472 := by norm_num

/-- The standard polynomial discriminant (4I³−J²)/27, with CFS's I,J. -/
theorem gQuartic_discriminant_value :
    ((4*1252675216^3-(-67150279897472)^2)/27 : ℚ)=
      2^18*3^8*5^4*7^8*11^4*37^2 := by norm_num

theorem gQuartic_JG_invariants :
    JG.c₄=1252675216 ∧ JG.c₆=-33575139948736 := by
  norm_num [JG,WeierstrassCurve.c₄,WeierstrassCurve.c₆,
    WeierstrassCurve.b₂,WeierstrassCurve.b₄,WeierstrassCurve.b₆]

end Z2Z4Rank6
