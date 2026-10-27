module

public import Z2Z4Rank6.SecondExampleConductorModel
public import Mathlib.Data.Nat.Squarefree

@[expose] public section

/-!
# The squarefree conductor of the printed second example

Jaswal, after Theorem 8.1(d), DOI 10.5281/zenodo.23437117. The good/multiplicative component theorem
is applied to minimal regular proper models.
-/
namespace Z2Z4Rank6.SecondExampleConductor
noncomputable section
open Common.Elliptic.GeometricConductor
set_option maxHeartbeats 1600000

def badPrimes : Finset ℕ := {2,3,5,7,11,13,17,23,31,53,61,83,89,137,241,401,433,457,1171,2089}

theorem badPrimes_prime : ∀ p∈badPrimes,p.Prime := by
  norm_num [badPrimes]

theorem discriminant_factorization : integerModel.Δ.natAbs =
    2^28*3^12*5^8*7^2*11^4*13^2*17^4*23^2*31^4*53^2*61^4*83^4*89^2*137^2*241^2*401^2*433^4*457^2*1171^4*2089^2 := by
  norm_num [integerModel,WeierstrassCurve.Δ,WeierstrassCurve.b₂,
    WeierstrassCurve.b₄,WeierstrassCurve.b₆,WeierstrassCurve.b₈]

theorem primeFactors_eq : integerModel.Δ.natAbs.primeFactors=badPrimes := by
  rw [discriminant_factorization]
  have h2 : Nat.Prime 2 := by norm_num
  have h3 : Nat.Prime 3 := by norm_num
  have h5 : Nat.Prime 5 := by norm_num
  have h7 : Nat.Prime 7 := by norm_num
  have h11 : Nat.Prime 11 := by norm_num
  have h13 : Nat.Prime 13 := by norm_num
  have h17 : Nat.Prime 17 := by norm_num
  have h23 : Nat.Prime 23 := by norm_num
  have h31 : Nat.Prime 31 := by norm_num
  have h53 : Nat.Prime 53 := by norm_num
  have h61 : Nat.Prime 61 := by norm_num
  have h83 : Nat.Prime 83 := by norm_num
  have h89 : Nat.Prime 89 := by norm_num
  have h137 : Nat.Prime 137 := by norm_num
  have h241 : Nat.Prime 241 := by norm_num
  have h401 : Nat.Prime 401 := by norm_num
  have h433 : Nat.Prime 433 := by norm_num
  have h457 : Nat.Prime 457 := by norm_num
  have h1171 : Nat.Prime 1171 := by norm_num
  have h2089 : Nat.Prime 2089 := by norm_num
  simp (disch := norm_num) only [Nat.primeFactors_mul,Nat.primeFactors_pow,
    h2.primeFactors,h3.primeFactors,h5.primeFactors,h7.primeFactors,h11.primeFactors,h13.primeFactors,h17.primeFactors,h23.primeFactors,h31.primeFactors,h53.primeFactors,h61.primeFactors,h83.primeFactors,h89.primeFactors,h137.primeFactors,h241.primeFactors,h401.primeFactors,h433.primeFactors,h457.primeFactors,h1171.primeFactors,h2089.primeFactors]
  norm_num [badPrimes]

theorem exponent_eq (hTate : CremonaTateSteps4And19to21) (D : Data integerModel)
    (p : ℕ) [hp : Fact p.Prime] :
    D.exponent p=if p∣integerModel.Δ.natAbs then 1 else 0 := by
  apply D.semistable_exponent hTate p
  by_cases hd : p∣integerModel.Δ.natAbs
  · right
    intro hc
    have hΔ : (p:ℤ)∣integerModel.Δ := Int.natCast_dvd.mpr hd
    have hone : (p:ℤ)∣(1:ℤ) := by
      obtain ⟨r,s,h⟩ := invariant_coprime
      rw [←h]
      exact dvd_add (dvd_mul_of_dvd_right hc r) (dvd_mul_of_dvd_right hΔ s)
    have hpone : (p:ℤ)=1 ∨ (p:ℤ)= -1 := Int.isUnit_iff.mp (isUnit_of_dvd_one hone)
    have hge := hp.out.two_le
    rcases hpone with h|h <;> omega
  · exact Or.inl hd

theorem conductor_eq (hTate : CremonaTateSteps4And19to21) (D : Data integerModel) :
    D.conductor=55712032256650048538220027355278990 := by
  have hf (p : ℕ) (hp : p∈badPrimes) : D.factor p=p := by
    let : Fact p.Prime := ⟨badPrimes_prime p hp⟩
    have hd : p∣integerModel.Δ.natAbs :=
      (Nat.mem_primeFactors.mp (by rwa [primeFactors_eq])).2.1
    rw [Data.factor_eq_prime_pow,exponent_eq hTate D p]
    simp [hd]
  calc
    D.conductor=∏ p∈badPrimes,p := by
      rw [Data.conductor,primeFactors_eq]
      exact Finset.prod_congr rfl hf
    _=55712032256650048538220027355278990 := by norm_num [badPrimes]

theorem conductor_squarefree (hTate : CremonaTateSteps4And19to21) (D : Data integerModel) :
    Squarefree D.conductor := by
  rw [conductor_eq hTate D]
  have hprod : (∏ p∈badPrimes,p)=55712032256650048538220027355278990 := by
    norm_num [badPrimes]
  rw [←hprod]
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p hp q hq hpq
    exact Nat.coprime_iff_isRelPrime.mp
      ((Nat.coprime_primes (badPrimes_prime p hp) (badPrimes_prime q hq)).mpr hpq)
  · exact fun p hp=>(badPrimes_prime p hp).squarefree

theorem example_conductor (hModels : EllipticMinimalModelsTheorem)
    (hTate : CremonaTateSteps4And19to21) :
    conductor hModels=55712032256650048538220027355278990 :=
  conductor_eq hTate (data hModels)

end
end Z2Z4Rank6.SecondExampleConductor
