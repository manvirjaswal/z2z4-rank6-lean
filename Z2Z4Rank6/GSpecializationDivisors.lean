module

public import Z2Z4Rank6.GSpecializationData
public import Z2Z4Rank6.GSpecializationQuartic
public import Z2Z4Rank6.GusicTadicDivisors
public import Z2Z4Rank6.GusicTadicRadicals

@[expose] public section

/-!
# Every squarefree divisor in the h-twist specialization criterion

Proposition 7.2(b) of Jaswal, DOI: 10.5281/zenodo.23437117.
The proof exhausts all squarefree integer-polynomial divisors, including
content and sign, rather than testing only a proposed list of candidates.
-/

namespace Z2Z4Rank6.GSpecialization

open Polynomial GusicTadic
open scoped BigOperators
noncomputable section
local notation "T" => (Polynomial.X : ℤ[X])

def hRadical : ℤ[X] := baseRadical*hPoly

/-- The primitive h-factor introduces no new content primes. -/
theorem h_products_content (i : Fin 3) :
    (hPoly^2*rootDifferenceProducts i).content=
      ![7^4,2^4*5^2*7^4,2^4*5^2*7^4] i := by
  rw [twisted_products_content,hPoly_content]
  norm_num

theorem h_products_dvd_radical (i : Fin 3) :
    hPoly^2*rootDifferenceProducts i ∣ hRadical^6 := by
  have hq : hPoly ∣ hRadical := dvd_mul_left hPoly baseRadical
  have hR : baseRadical ∣ hRadical := dvd_mul_right baseRadical hPoly
  have hq2 := pow_dvd_pow_of_dvd hq 2
  have hp4 := (rootDifferenceProducts_dvd_radical i).trans (pow_dvd_pow_of_dvd hR 4)
  simpa only [←pow_add,show 2+4=6 by decide] using mul_dvd_mul hq2 hp4

theorem pool_product : (∏ i : Fin 15, polynomials (order i.castSucc))=hRadical := by
  norm_num [Fin.prod_univ_succ,polynomials,order,baseFactors,hRadical,baseRadical,
    linearA,linearB,quadraticFactor,quarticFactor]
  ring

private theorem ordered_irreducible (i : Fin 15) :
    Irreducible (polynomials (order i.castSucc)) := by
  fin_cases i
  · simpa [polynomials,order] using baseFactors_irreducible 0
  · simpa [polynomials,order] using baseFactors_irreducible 1
  · simpa [polynomials,order] using baseFactors_irreducible 2
  · simpa [polynomials,order] using baseFactors_irreducible 3
  · simpa [polynomials,order] using baseFactors_irreducible 4
  · simpa [polynomials,order] using baseFactors_irreducible 5
  · simpa [polynomials,order] using baseFactors_irreducible 6
  · simpa [polynomials,order] using baseFactors_irreducible 7
  · simpa [polynomials,order] using baseFactors_irreducible 9
  · simpa [polynomials,order] using baseFactors_irreducible 10
  · simpa [polynomials,order] using hPoly_irreducible
  · simpa [polynomials,order] using baseFactors_irreducible 8
  · simpa [polynomials,order] using contentPrime_irreducible 2 (by decide)
  · simpa [polynomials,order] using contentPrime_irreducible 5 (by decide)
  · simpa [polynomials,order] using contentPrime_irreducible 7 (by decide)

/-- All canonical squarefree polynomial divisors have exact signed binary
representations in the twelve-factor pool and the three content primes. -/
theorem divisor_representation (i : Fin 3) (g : ℤ[X])
    (hsq : Squarefree g) (hdiv : g ∣ hPoly^2*rootDifferenceProducts i) :
    ∃ b : Fin 16 → Fin 2, g=∏ j, polynomials j^(b j).val := by
  have hR : g ∣ hRadical := (hsq.dvd_pow_iff_dvd (by decide : 6≠0)).mp
    (hdiv.trans (h_products_dvd_radical i))
  rw [←pool_product] at hR
  apply binary_representation_unpermute polynomials order g
  exact divisor_binary_representation (fun j => polynomials (order j))
    ordered_irreducible rfl g hR

/-- Complete condition (A) at m=-80/3: every nonconstant squarefree divisor
of every root-difference product has nonsquare rational value. -/
theorem divisor_test (i : Fin 3) (g : ℤ[X])
    (hsq : Squarefree g) (hdiv : g ∣ hPoly^2*rootDifferenceProducts i)
    (hnonconstant : g.natDegree≠0) : ¬IsSquare (evalAt parameter g) := by
  obtain ⟨b,hb⟩ := divisor_representation i g hsq hdiv
  exact nonconstant_candidate g b hb hnonconstant

end
end Z2Z4Rank6.GSpecialization
