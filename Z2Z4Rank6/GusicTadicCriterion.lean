import Z2Z4Rank6.GusicTadicDivisors
import Z2Z4Rank6.GusicTadicRadicals

/-!
# Complete squarefree-divisor tests at the printed specializations

The arithmetic hypothesis of the Gusić–Tadić specialization theorem used in
Propositions 2.3 and 5.2 of Manvir Jaswal,
DOI 10.5281/zenodo.23437117. Every nonconstant squarefree integer polynomial
divisor of any of the three root-difference products is proved to have
nonsquare value at the printed specialization.
-/

namespace Z2Z4Rank6.GusicTadic

open Polynomial
open scoped BigOperators
noncomputable section

local notation "T" => (Polynomial.X : ℤ[X])

private theorem base14_ordered_irreducible (i : Fin 14) :
    Irreducible (base14Polynomials (base14Order i.castSucc)) := by
  fin_cases i
  · simpa [base14Polynomials, base14Order] using baseFactors_irreducible 0
  · simpa [base14Polynomials, base14Order] using baseFactors_irreducible 1
  · simpa [base14Polynomials, base14Order] using baseFactors_irreducible 2
  · simpa [base14Polynomials, base14Order] using baseFactors_irreducible 3
  · simpa [base14Polynomials, base14Order] using baseFactors_irreducible 4
  · simpa [base14Polynomials, base14Order] using baseFactors_irreducible 5
  · simpa [base14Polynomials, base14Order] using baseFactors_irreducible 6
  · simpa [base14Polynomials, base14Order] using baseFactors_irreducible 7
  · simpa [base14Polynomials, base14Order] using baseFactors_irreducible 9
  · simpa [base14Polynomials, base14Order] using baseFactors_irreducible 10
  · simpa [base14Polynomials, base14Order] using baseFactors_irreducible 8
  · simpa [base14Polynomials, base14Order] using contentPrime_irreducible 2 (by decide)
  · simpa [base14Polynomials, base14Order] using contentPrime_irreducible 5 (by decide)
  · simpa [base14Polynomials, base14Order] using contentPrime_irreducible 7 (by decide)

/-- Every squarefree divisor of the criterion products is represented by the
printed irreducible factor pool, including its sign and content primes. -/
theorem base14_divisor_representation (i : Fin 3) (g : ℤ[X])
    (hsq : Squarefree g) (hdiv : g ∣ rootDifferenceProducts i) :
    ∃ b : Fin 15 → Fin 2, g=∏ j, base14Polynomials j^(b j).val := by
  have hR : g ∣ baseRadical := (hsq.dvd_pow_iff_dvd (by decide : 4 ≠ 0)).mp
    (hdiv.trans (rootDifferenceProducts_dvd_radical i))
  rw [← base14_pool_product] at hR
  apply binary_representation_unpermute base14Polynomials base14Order g
  exact divisor_binary_representation (fun j => base14Polynomials (base14Order j))
    base14_ordered_irreducible rfl g hR

/-- The complete Gusić–Tadić arithmetic test at m=14/3: every nonconstant
squarefree divisor of a root-difference product has nonsquare rational value. -/
theorem base14_divisor_test (i : Fin 3) (g : ℤ[X])
    (hsq : Squarefree g) (hdiv : g ∣ rootDifferenceProducts i) (hnonconstant : g.natDegree ≠ 0) :
    ¬IsSquare (evalAt (14/3) g) := by
  obtain ⟨b,hb⟩ := base14_divisor_representation i g hsq hdiv
  exact base14_nonconstant_candidate g b hb hnonconstant

private theorem twist14_ordered_irreducible (i : Fin 15) :
    Irreducible (twist14Polynomials (twist14Order i.castSucc)) := by
  fin_cases i
  · simpa [twist14Polynomials, twist14Order] using baseFactors_irreducible 0
  · simpa [twist14Polynomials, twist14Order] using baseFactors_irreducible 1
  · simpa [twist14Polynomials, twist14Order] using baseFactors_irreducible 2
  · simpa [twist14Polynomials, twist14Order] using baseFactors_irreducible 3
  · simpa [twist14Polynomials, twist14Order] using baseFactors_irreducible 4
  · simpa [twist14Polynomials, twist14Order] using baseFactors_irreducible 5
  · simpa [twist14Polynomials, twist14Order] using baseFactors_irreducible 6
  · simpa [twist14Polynomials, twist14Order] using baseFactors_irreducible 7
  · simpa [twist14Polynomials, twist14Order] using baseFactors_irreducible 9
  · simpa [twist14Polynomials, twist14Order] using baseFactors_irreducible 10
  · simpa [twist14Polynomials, twist14Order] using q1Core_irreducible
  · simpa [twist14Polynomials, twist14Order] using baseFactors_irreducible 8
  · simpa [twist14Polynomials, twist14Order] using contentPrime_irreducible 2 (by decide)
  · simpa [twist14Polynomials, twist14Order] using contentPrime_irreducible 5 (by decide)
  · simpa [twist14Polynomials, twist14Order] using contentPrime_irreducible 7 (by decide)

/-- Every squarefree divisor of the criterion products is represented by the
printed irreducible factor pool, including its sign and content primes. -/
theorem twist14_divisor_representation (i : Fin 3) (g : ℤ[X])
    (hsq : Squarefree g) (hdiv : g ∣ q1Poly^2*rootDifferenceProducts i) :
    ∃ b : Fin 16 → Fin 2, g=∏ j, twist14Polynomials j^(b j).val := by
  have hR : g ∣ twist14Radical := (hsq.dvd_pow_iff_dvd (by decide : 6 ≠ 0)).mp
    (hdiv.trans (q1_products_dvd_radical i))
  rw [← twist14_pool_product] at hR
  apply binary_representation_unpermute twist14Polynomials twist14Order g
  exact divisor_binary_representation (fun j => twist14Polynomials (twist14Order j))
    twist14_ordered_irreducible rfl g hR

/-- The complete Gusić–Tadić arithmetic test at m=14/3: every nonconstant
squarefree divisor of a root-difference product has nonsquare rational value. -/
theorem twist14_divisor_test (i : Fin 3) (g : ℤ[X])
    (hsq : Squarefree g) (hdiv : g ∣ q1Poly^2*rootDifferenceProducts i) (hnonconstant : g.natDegree ≠ 0) :
    ¬IsSquare (evalAt (14/3) g) := by
  obtain ⟨b,hb⟩ := twist14_divisor_representation i g hsq hdiv
  exact twist14_nonconstant_candidate g b hb hnonconstant

private theorem twist50_ordered_irreducible (i : Fin 15) :
    Irreducible (twist50Polynomials (twist50Order i.castSucc)) := by
  fin_cases i
  · simpa [twist50Polynomials, twist50Order] using baseFactors_irreducible 0
  · simpa [twist50Polynomials, twist50Order] using baseFactors_irreducible 1
  · simpa [twist50Polynomials, twist50Order] using baseFactors_irreducible 2
  · simpa [twist50Polynomials, twist50Order] using baseFactors_irreducible 3
  · simpa [twist50Polynomials, twist50Order] using baseFactors_irreducible 4
  · simpa [twist50Polynomials, twist50Order] using baseFactors_irreducible 5
  · simpa [twist50Polynomials, twist50Order] using baseFactors_irreducible 6
  · simpa [twist50Polynomials, twist50Order] using baseFactors_irreducible 7
  · simpa [twist50Polynomials, twist50Order] using baseFactors_irreducible 9
  · simpa [twist50Polynomials, twist50Order] using baseFactors_irreducible 10
  · simpa [twist50Polynomials, twist50Order] using q2Core_irreducible
  · simpa [twist50Polynomials, twist50Order] using baseFactors_irreducible 8
  · simpa [twist50Polynomials, twist50Order] using contentPrime_irreducible 2 (by decide)
  · simpa [twist50Polynomials, twist50Order] using contentPrime_irreducible 5 (by decide)
  · simpa [twist50Polynomials, twist50Order] using contentPrime_irreducible 7 (by decide)

/-- Every squarefree divisor of the criterion products is represented by the
printed irreducible factor pool, including its sign and content primes. -/
theorem twist50_divisor_representation (i : Fin 3) (g : ℤ[X])
    (hsq : Squarefree g) (hdiv : g ∣ q2Poly^2*rootDifferenceProducts i) :
    ∃ b : Fin 16 → Fin 2, g=∏ j, twist50Polynomials j^(b j).val := by
  have hR : g ∣ twist50Radical := (hsq.dvd_pow_iff_dvd (by decide : 6 ≠ 0)).mp
    (hdiv.trans (q2_products_dvd_radical i))
  rw [← twist50_pool_product] at hR
  apply binary_representation_unpermute twist50Polynomials twist50Order g
  exact divisor_binary_representation (fun j => twist50Polynomials (twist50Order j))
    twist50_ordered_irreducible rfl g hR

/-- The complete Gusić–Tadić arithmetic test at m=50/3: every nonconstant
squarefree divisor of a root-difference product has nonsquare rational value. -/
theorem twist50_divisor_test (i : Fin 3) (g : ℤ[X])
    (hsq : Squarefree g) (hdiv : g ∣ q2Poly^2*rootDifferenceProducts i) (hnonconstant : g.natDegree ≠ 0) :
    ¬IsSquare (evalAt (50/3) g) := by
  obtain ⟨b,hb⟩ := twist50_divisor_representation i g hsq hdiv
  exact twist50_nonconstant_candidate g b hb hnonconstant

private theorem product50_ordered_irreducible (i : Fin 16) :
    Irreducible (product50Polynomials (product50Order i.castSucc)) := by
  fin_cases i
  · simpa [product50Polynomials, product50Order] using baseFactors_irreducible 0
  · simpa [product50Polynomials, product50Order] using baseFactors_irreducible 1
  · simpa [product50Polynomials, product50Order] using baseFactors_irreducible 2
  · simpa [product50Polynomials, product50Order] using baseFactors_irreducible 3
  · simpa [product50Polynomials, product50Order] using baseFactors_irreducible 4
  · simpa [product50Polynomials, product50Order] using baseFactors_irreducible 5
  · simpa [product50Polynomials, product50Order] using baseFactors_irreducible 6
  · simpa [product50Polynomials, product50Order] using baseFactors_irreducible 7
  · simpa [product50Polynomials, product50Order] using baseFactors_irreducible 9
  · simpa [product50Polynomials, product50Order] using baseFactors_irreducible 10
  · simpa [product50Polynomials, product50Order] using q2Core_irreducible
  · simpa [product50Polynomials, product50Order] using q1Core_irreducible
  · simpa [product50Polynomials, product50Order] using baseFactors_irreducible 8
  · simpa [product50Polynomials, product50Order] using contentPrime_irreducible 2 (by decide)
  · simpa [product50Polynomials, product50Order] using contentPrime_irreducible 5 (by decide)
  · simpa [product50Polynomials, product50Order] using contentPrime_irreducible 7 (by decide)

/-- Every squarefree divisor of the criterion products is represented by the
printed irreducible factor pool, including its sign and content primes. -/
theorem product50_divisor_representation (i : Fin 3) (g : ℤ[X])
    (hsq : Squarefree g) (hdiv : g ∣ q12Poly^2*rootDifferenceProducts i) :
    ∃ b : Fin 17 → Fin 2, g=∏ j, product50Polynomials j^(b j).val := by
  have hR : g ∣ product50Radical := (hsq.dvd_pow_iff_dvd (by decide : 6 ≠ 0)).mp
    (hdiv.trans (q12_products_dvd_radical i))
  rw [← product50_pool_product] at hR
  apply binary_representation_unpermute product50Polynomials product50Order g
  exact divisor_binary_representation (fun j => product50Polynomials (product50Order j))
    product50_ordered_irreducible rfl g hR

/-- The complete Gusić–Tadić arithmetic test at m=50/3: every nonconstant
squarefree divisor of a root-difference product has nonsquare rational value. -/
theorem product50_divisor_test (i : Fin 3) (g : ℤ[X])
    (hsq : Squarefree g) (hdiv : g ∣ q12Poly^2*rootDifferenceProducts i) (hnonconstant : g.natDegree ≠ 0) :
    ¬IsSquare (evalAt (50/3) g) := by
  obtain ⟨b,hb⟩ := product50_divisor_representation i g hsq hdiv
  exact product50_nonconstant_candidate g b hb hnonconstant

end

end Z2Z4Rank6.GusicTadic
