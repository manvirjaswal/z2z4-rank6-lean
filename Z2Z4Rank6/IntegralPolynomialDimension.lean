import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.Ideal.GoingUp

/-! # Dimension one for integral algebras containing Q[t]

Integral incomparability gives the upper bound. Lying over the zero prime
and going up to the kernel of evaluation at zero give a strict prime chain.
The algebra need not be a domain.
-/
namespace Z2Z4Rank6.IntegralPolynomialDimension
noncomputable section

theorem integral_ringKrullDim_le (R A : Type*) [CommRing R] [CommRing A]
    [Algebra R A] [Algebra.IsIntegral R A] : ringKrullDim A≤ringKrullDim R := by
  apply Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap R A))
  intro I J hIJ
  exact Ideal.IsIntegral.under_lt_under hIJ

theorem polynomial_dimension : ringKrullDim (Polynomial ℚ)=1 := by
  rw [Polynomial.ringKrullDim_of_isNoetherianRing,ringKrullDim_eq_zero_of_field]
  simp

/-- An integral algebra with an injective Q[t] coefficient map has
dimension exactly one, whether or not the algebra is a domain. -/
theorem dimension_eq_one (A : Type*) [CommRing A] [Algebra (Polynomial ℚ) A]
    [Algebra.IsIntegral (Polynomial ℚ) A]
    (hinj : Function.Injective (algebraMap (Polynomial ℚ) A)) : ringKrullDim A=1 := by
  apply le_antisymm ((integral_ringKrullDim_le (Polynomial ℚ) A).trans polynomial_dimension.le)
  apply Order.one_le_krullDim_iff.mpr
  have hbot : (⊥ : Ideal A).under (Polynomial ℚ)≤(⊥ : Ideal (Polynomial ℚ)) := by
    change Ideal.comap (algebraMap (Polynomial ℚ) A) ⊥≤⊥
    rw [←RingHom.ker_eq_comap_bot,(RingHom.injective_iff_ker_eq_bot _).mp hinj]
  obtain ⟨P,_,hP,hP0⟩ := Ideal.exists_ideal_over_prime_of_isIntegral
    (⊥ : Ideal (Polynomial ℚ)) (⊥ : Ideal A) hbot
  let : P.IsPrime := hP
  let M : Ideal (Polynomial ℚ) := RingHom.ker (Polynomial.evalRingHom (0:ℚ))
  let : M.IsPrime := RingHom.ker_isPrime _
  have hM : M≠⊥ := by
    intro h
    have hX : Polynomial.X∈M := by simp [M]
    rw [h,Ideal.mem_bot] at hX
    exact Polynomial.X_ne_zero hX
  obtain ⟨Q,hPQ,hQ,hQM⟩ := Ideal.exists_ideal_over_prime_of_isIntegral_of_isPrime M P
    (by rw [hP0]; exact bot_le)
  refine ⟨⟨P,hP⟩,⟨Q,hQ⟩,?_⟩
  change P<Q
  refine lt_iff_le_and_ne.mpr ⟨hPQ,?_⟩
  intro h
  apply hM
  exact hQM.symm.trans (by simpa only [h] using hP0)

end
end Z2Z4Rank6.IntegralPolynomialDimension
