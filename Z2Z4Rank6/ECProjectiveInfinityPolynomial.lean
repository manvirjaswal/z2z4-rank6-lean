import Z2Z4Rank6.ECProjectiveSchemeInfinity
import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
import Mathlib.RingTheory.AdjoinRoot

/-! The Y-chart cubic, monic in x over Q[z], is Eisenstein at(z).
The constant coefficient has z-adic order exactly 1. This proves the
AdjoinRoot algebra is a domain.
Source: Jaswal, DOI 10.5281/zenodo.23437117, Theorem 1.2(a), Lemma 4.1.
-/
namespace Z2Z4Rank6.ECProjectiveInfinityPolynomial
noncomputable section
open scoped Classical Polynomial.Bivariate
open Polynomial

abbrev Poly := Polynomial ℚ
def cubic : Poly[X] := Polynomial.X^3+C (Polynomial.X:Poly)*Polynomial.X^2-
  C (137620*(Polynomial.X:Poly)^2)*Polynomial.X-
  C (10504000*(Polynomial.X:Poly)^3+(Polynomial.X:Poly))

theorem cubic_monic : cubic.Monic := by
  have he : cubic=Polynomial.X^3+(C (Polynomial.X:Poly)*Polynomial.X^2-
      C (137620*(Polynomial.X:Poly)^2)*Polynomial.X-
      C (10504000*(Polynomial.X:Poly)^3+(Polynomial.X:Poly))) := by
    unfold cubic
    ring
  rw [he]
  apply monic_X_pow_add
  compute_degree!

theorem cubic_natDegree : cubic.natDegree=3 := by
  unfold cubic
  compute_degree!

def primeIdeal : Ideal Poly := Ideal.span {(Polynomial.X:Poly)}

theorem primeIdeal_prime : primeIdeal.IsPrime :=
  Ideal.isPrime_span_singleton_of_prime Polynomial.prime_X

theorem cubic_eisenstein : cubic.IsEisensteinAt primeIdeal := by
  apply cubic_monic.isEisensteinAt_of_mem_of_notMem primeIdeal_prime.ne_top
  · intro n hn
    rw [cubic_natDegree] at hn
    interval_cases n <;>
      simp only [cubic,coeff_sub,coeff_C_mul,coeff_mul_X,coeff_C]
    all_goals norm_num [primeIdeal,Ideal.mem_span_singleton,Polynomial.X_dvd_iff]
  · intro h
    rw [primeIdeal,Ideal.span_singleton_pow,Ideal.mem_span_singleton] at h
    have he := Polynomial.X_pow_dvd_iff.mp h 1 (by decide:1<2)
    simp only [cubic,coeff_sub,coeff_C_mul,coeff_C] at he
    norm_num at he

theorem cubic_irreducible : Irreducible cubic :=
  cubic_eisenstein.irreducible primeIdeal_prime cubic_monic.isPrimitive (by rw [cubic_natDegree];decide)

theorem cubic_prime : Prime cubic := cubic_irreducible.prime

abbrev Tower := AdjoinRoot cubic
instance towerIsDomain : IsDomain Tower := AdjoinRoot.isDomain_of_prime cubic_prime
instance towerFinite : Module.Finite Poly Tower := cubic_monic.finite_adjoinRoot
instance towerFree : Module.Free Poly Tower := cubic_monic.free_adjoinRoot

def powerBasis : PowerBasis Poly Tower := AdjoinRoot.powerBasis' cubic_monic

theorem powerBasis_dim : powerBasis.dim=3 := cubic_natDegree

end
end Z2Z4Rank6.ECProjectiveInfinityPolynomial
