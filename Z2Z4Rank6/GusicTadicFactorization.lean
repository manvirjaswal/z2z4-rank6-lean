module

public import Z2Z4Rank6.FamilyIdentities
public import Z2Z4Rank6.GusicTadicData
public import Mathlib.RingTheory.Polynomial.Content
public import Mathlib.Algebra.GCDMonoid.Nat

@[expose] public section

/-!
# Polynomial products in the specialization criterion

The integer polynomial factorizations and exact contents in the proof of
Proposition 2.3 of Manvir Jaswal, *Infinitely many elliptic curves with torsion
Z/2Z × Z/4Z and rank at least six*,
DOI 10.5281/zenodo.23437117. The twist products in Proposition 5.2 multiply
these products by q², so their contents have only the displayed content primes.
-/

namespace Z2Z4Rank6.GusicTadic

open Polynomial

noncomputable section

local notation "T" => (Polynomial.X : ℤ[X])

def aPoly : ℤ[X] := a T
def bPoly : ℤ[X] := b T
def quarticFactor : ℤ[X] := T^4-2*T^2+9801
def quadraticFactor : ℤ[X] := T^2-99

/-- The three root-difference products in Gusić–Tadić's criterion. -/
def rootDifferenceProducts : Fin 3 → ℤ[X] :=
  ![aPoly^2*bPoly^2,
    aPoly^2*(aPoly^2-bPoly^2),
    -bPoly^2*(aPoly^2-bPoly^2)]

theorem aPoly_content : aPoly.content=7 := by
  let p : ℤ[X] := (T-99)*(T+1)*(T-11)*(T+9)
  have hp : p.Monic := by dsimp [p]; monicity!
  have he : aPoly=C 7*p := by dsimp [aPoly, a, p]; norm_num; ring
  rw [he]
  rw [content_C_mul, hp.isPrimitive.content_eq_one, mul_one]
  norm_num [← Int.abs_eq_normalize]

theorem bPoly_content : bPoly.content=7 := by
  let p : ℤ[X] := (T+99)*(T-1)*(T+11)*(T-9)
  have hp : p.Monic := by dsimp [p]; monicity!
  have he : bPoly=C (-7)*p := by dsimp [bPoly, b, p]; norm_num; ring
  rw [he]
  rw [content_C_mul, hp.isPrimitive.content_eq_one, mul_one]
  norm_num [← Int.abs_eq_normalize]

theorem aPoly_sub_bPoly : aPoly-bPoly=14*quarticFactor := a_sub_b T

theorem aPoly_add_bPoly : aPoly+bPoly= -1400*T*quadraticFactor := a_add_b T

theorem quarticFactor_content : quarticFactor.content=1 := by
  apply Polynomial.IsPrimitive.content_eq_one
  apply Polynomial.Monic.isPrimitive
  unfold quarticFactor
  monicity!

theorem quadraticFactor_content : quadraticFactor.content=1 := by
  apply Polynomial.IsPrimitive.content_eq_one
  apply Polynomial.Monic.isPrimitive
  unfold quadraticFactor
  monicity!

theorem aPoly_sub_bPoly_content : (aPoly-bPoly).content=14 := by
  rw [aPoly_sub_bPoly]
  change (C 14*quarticFactor).content=14
  rw [content_C_mul, quarticFactor_content, mul_one]
  norm_num [← Int.abs_eq_normalize]

theorem aPoly_add_bPoly_content : (aPoly+bPoly).content=1400 := by
  rw [aPoly_add_bPoly]
  rw [show -1400*T*quadraticFactor=C (-1400)*(T*quadraticFactor) by norm_num; ring]
  rw [content_C_mul, content_X_mul, quadraticFactor_content, mul_one]
  norm_num [← Int.abs_eq_normalize]

theorem square_difference_content : (aPoly^2-bPoly^2).content=19600 := by
  rw [sq_sub_sq, content_mul, aPoly_sub_bPoly_content, aPoly_add_bPoly_content]
  norm_num

private theorem content_sq (p : ℤ[X]) : (p^2).content=p.content^2 := by
  rw [pow_two, content_mul, pow_two]

/-- The exact contents printed in Proposition 2.3: 7⁴ and 2⁴·5²·7⁴. -/
theorem rootDifferenceProducts_content (i : Fin 3) :
    (rootDifferenceProducts i).content=![7^4, 2^4*5^2*7^4, 2^4*5^2*7^4] i := by
  fin_cases i
  · change (aPoly^2*bPoly^2).content=7^4
    rw [content_mul, content_sq, content_sq, aPoly_content, bPoly_content]
    norm_num
  · change (aPoly^2*(aPoly^2-bPoly^2)).content=2^4*5^2*7^4
    rw [content_mul, content_sq, aPoly_content, square_difference_content]
    norm_num
  · have he : -bPoly^2*(aPoly^2-bPoly^2)=C (-1)*(bPoly^2*(aPoly^2-bPoly^2)) := by norm_num
    change (-bPoly^2*(aPoly^2-bPoly^2)).content=2^4*5^2*7^4
    rw [he, content_C_mul, content_mul, content_sq, bPoly_content, square_difference_content]
    norm_num [← Int.abs_eq_normalize]

def q1Poly : ℤ[X] := q1 (T^2)
def q2Poly : ℤ[X] := q2 (T^2)
def q12Poly : ℤ[X] := q12 (T^2)

private theorem content_eq_one_of_coeff_bezout (p : ℤ[X]) (A B r : ℤ)
    (h0 : p.coeff 0=A) (h2 : p.coeff 2=B) (hbez : r*B-A=1) : p.content=1 := by
  have ha : p.content ∣ A := h0 ▸ content_dvd_coeff (p := p) 0
  have hb : p.content ∣ B := h2 ▸ content_dvd_coeff (p := p) 2
  have h1 : p.content ∣ 1 := hbez ▸ dvd_sub (dvd_mul_of_dvd_right hb r) ha
  have hn : normalize p.content=1 := normalize_eq_one.mpr (isUnit_of_dvd_one h1)
  simpa only [normalize_content] using hn

theorem q1Core_content : (3*T^2+242).content=1 := by
  apply content_eq_one_of_coeff_bezout _ 242 3 81 <;> norm_num

theorem q2Core_content : (2*T^2+243).content=1 := by
  apply content_eq_one_of_coeff_bezout _ 243 2 122 <;> norm_num

/-- The twist q₁ has exactly content 5. -/
theorem q1Poly_content : q1Poly.content=5 := by
  change (C 5*(3*T^2+242)).content=5
  rw [content_C_mul, q1Core_content, mul_one]
  norm_num [← Int.abs_eq_normalize]

/-- The twist q₂ has exactly content 5. -/
theorem q2Poly_content : q2Poly.content=5 := by
  change (C 5*(2*T^2+243)).content=5
  rw [content_C_mul, q2Core_content, mul_one]
  norm_num [← Int.abs_eq_normalize]

/-- The twist q₁₂ is primitive. -/
theorem q12Poly_content : q12Poly.content=1 := by
  change ((3*T^2+242)*(2*T^2+243)).content=1
  rw [content_mul, q1Core_content, q2Core_content, one_mul]

/-- The three products for a twist are exactly q² times the three untwisted products. -/
theorem twisted_products_identity (q : ℤ[X]) :
    ![((0 : ℤ[X])-(-q*aPoly^2))*(0-(-q*bPoly^2)),
      ((-q*aPoly^2)-0)*((-q*aPoly^2)-(-q*bPoly^2)),
      ((-q*bPoly^2)-0)*((-q*bPoly^2)-(-q*aPoly^2))] =
      fun i => q^2*rootDifferenceProducts i := by
  funext i
  fin_cases i <;> dsimp [rootDifferenceProducts] <;> ring

/-- Exact contents for any twist; the three used twists introduce only the prime 5. -/
theorem twisted_products_content (q : ℤ[X]) (i : Fin 3) :
    (q^2*rootDifferenceProducts i).content=
      q.content^2*![7^4, 2^4*5^2*7^4, 2^4*5^2*7^4] i := by
  rw [content_mul, content_sq, rootDifferenceProducts_content]

theorem q1_twisted_products_content (i : Fin 3) :
    (q1Poly^2*rootDifferenceProducts i).content=
      25*![7^4, 2^4*5^2*7^4, 2^4*5^2*7^4] i := by
  rw [twisted_products_content, q1Poly_content]
  norm_num

theorem q2_twisted_products_content (i : Fin 3) :
    (q2Poly^2*rootDifferenceProducts i).content=
      25*![7^4, 2^4*5^2*7^4, 2^4*5^2*7^4] i := by
  rw [twisted_products_content, q2Poly_content]
  norm_num

theorem q12_twisted_products_content (i : Fin 3) :
    (q12Poly^2*rootDifferenceProducts i).content=
      ![7^4, 2^4*5^2*7^4, 2^4*5^2*7^4] i := by
  rw [twisted_products_content, q12Poly_content]
  norm_num

end

end Z2Z4Rank6.GusicTadic
