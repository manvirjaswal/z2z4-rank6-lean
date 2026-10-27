module

public import Z2Z4Rank6.GusicTadicCandidates

@[expose] public section

/-!
# Common radical products for the specialization criterion

The explicit factorizations of Propositions 2.3 and 5.2 of Manvir Jaswal,
DOI 10.5281/zenodo.23437117. Each root-difference product divides
a fixed power of its printed factor pool. A squarefree divisor therefore
divides the product of those factors with exponent one.
-/

namespace Z2Z4Rank6.GusicTadic

open Polynomial
open scoped BigOperators
noncomputable section

local notation "T" => (Polynomial.X : ℤ[X])

def linearA : ℤ[X] := (T-99)*(T+1)*(T-11)*(T+9)
def linearB : ℤ[X] := (T+99)*(T-1)*(T+11)*(T-9)

def baseRadical : ℤ[X] := 70*linearA*linearB*T*quadraticFactor*quarticFactor
def twist14Radical : ℤ[X] := baseRadical*(3*T^2+242)
def twist50Radical : ℤ[X] := baseRadical*(2*T^2+243)
def product50Radical : ℤ[X] := baseRadical*(2*T^2+243)*(3*T^2+242)

theorem aPoly_eq_linear : aPoly=7*linearA := by unfold aPoly a linearA; ring
theorem bPoly_eq_linear : bPoly= -7*linearB := by unfold bPoly b linearB; ring

theorem square_difference_factorization :
    aPoly^2-bPoly^2= -19600*T*quadraticFactor*quarticFactor := by
  rw [sq_sub_sq, aPoly_sub_bPoly, aPoly_add_bPoly]
  ring

theorem rootDifferenceProducts_factorization (i : Fin 3) :
    rootDifferenceProducts i=
      ![2401*linearA^2*linearB^2,
        -960400*linearA^2*T*quadraticFactor*quarticFactor,
        960400*linearB^2*T*quadraticFactor*quarticFactor] i := by
  fin_cases i
  · change aPoly^2*bPoly^2= _
    rw [aPoly_eq_linear, bPoly_eq_linear]
    dsimp
    ring
  · change aPoly^2*(aPoly^2-bPoly^2)= _
    rw [square_difference_factorization, aPoly_eq_linear]
    dsimp
    ring
  · change -bPoly^2*(aPoly^2-bPoly^2)= _
    rw [square_difference_factorization, bPoly_eq_linear]
    dsimp
    ring

/-- Every untwisted criterion product divides the fourth power of the factor pool. -/
theorem rootDifferenceProducts_dvd_radical (i : Fin 3) :
    rootDifferenceProducts i ∣ baseRadical^4 := by
  fin_cases i
  · refine ⟨10000*linearA^2*linearB^2*(T*quadraticFactor*quarticFactor)^4, ?_⟩
    rw [rootDifferenceProducts_factorization]
    dsimp
    unfold baseRadical
    ring
  · refine ⟨-25*linearA^2*linearB^4*T^3*quadraticFactor^3*quarticFactor^3, ?_⟩
    rw [rootDifferenceProducts_factorization]
    dsimp
    unfold baseRadical
    ring
  · refine ⟨25*linearA^4*linearB^2*T^3*quadraticFactor^3*quarticFactor^3, ?_⟩
    rw [rootDifferenceProducts_factorization]
    dsimp
    unfold baseRadical
    ring

theorem base14_pool_product :
    (∏ i : Fin 14, base14Polynomials (base14Order i.castSucc))=baseRadical := by
  norm_num [Fin.prod_univ_succ, base14Polynomials, base14Order, baseFactors,
    baseRadical, linearA, linearB, quadraticFactor, quarticFactor]
  ring

theorem twist14_pool_product :
    (∏ i : Fin 15, twist14Polynomials (twist14Order i.castSucc))=twist14Radical := by
  norm_num [Fin.prod_univ_succ, twist14Polynomials, twist14Order, baseFactors,
    twist14Radical, baseRadical, linearA, linearB, quadraticFactor, quarticFactor]
  ring

theorem twist50_pool_product :
    (∏ i : Fin 15, twist50Polynomials (twist50Order i.castSucc))=twist50Radical := by
  norm_num [Fin.prod_univ_succ, twist50Polynomials, twist50Order, baseFactors,
    twist50Radical, baseRadical, linearA, linearB, quadraticFactor, quarticFactor]
  ring

theorem product50_pool_product :
    (∏ i : Fin 16, product50Polynomials (product50Order i.castSucc))=product50Radical := by
  norm_num [Fin.prod_univ_succ, product50Polynomials, product50Order, baseFactors,
    product50Radical, baseRadical, linearA, linearB, quadraticFactor, quarticFactor]
  ring

theorem q1Poly_dvd_radical : q1Poly ∣ twist14Radical := by
  refine ⟨14*linearA*linearB*T*quadraticFactor*quarticFactor, ?_⟩
  unfold q1Poly q1 twist14Radical baseRadical
  ring

theorem q2Poly_dvd_radical : q2Poly ∣ twist50Radical := by
  refine ⟨14*linearA*linearB*T*quadraticFactor*quarticFactor, ?_⟩
  unfold q2Poly q2 twist50Radical baseRadical
  ring

theorem q12Poly_dvd_radical : q12Poly ∣ product50Radical := by
  refine ⟨baseRadical, ?_⟩
  unfold q12Poly q12 product50Radical
  ring

private theorem twisted_divisibility {q R : ℤ[X]} (hq : q ∣ R) (hR : baseRadical ∣ R)
    (i : Fin 3) : q^2*rootDifferenceProducts i ∣ R^6 := by
  have hq2 := pow_dvd_pow_of_dvd hq 2
  have hp4 := (rootDifferenceProducts_dvd_radical i).trans (pow_dvd_pow_of_dvd hR 4)
  have hprod := mul_dvd_mul hq2 hp4
  simpa only [← pow_add, show 2+4=6 by decide] using hprod

theorem q1_products_dvd_radical (i : Fin 3) :
    q1Poly^2*rootDifferenceProducts i ∣ twist14Radical^6 :=
  twisted_divisibility q1Poly_dvd_radical (dvd_mul_right _ _) i

theorem q2_products_dvd_radical (i : Fin 3) :
    q2Poly^2*rootDifferenceProducts i ∣ twist50Radical^6 :=
  twisted_divisibility q2Poly_dvd_radical (dvd_mul_right _ _) i

theorem q12_products_dvd_radical (i : Fin 3) :
    q12Poly^2*rootDifferenceProducts i ∣ product50Radical^6 := by
  apply twisted_divisibility q12Poly_dvd_radical
  exact (dvd_mul_right _ _).trans (dvd_mul_right _ _)

end

end Z2Z4Rank6.GusicTadic
