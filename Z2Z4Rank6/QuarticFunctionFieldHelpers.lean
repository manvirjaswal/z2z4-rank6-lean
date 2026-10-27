module

public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Polynomial.IsIntegral
public import Mathlib.FieldTheory.Separable
public import Mathlib.FieldTheory.AlgebraicClosure

@[expose] public section

/-!
# Elementary function-field prerequisites for quartic birational maps

A nonconstant squarefree polynomial stays nonsquare in its rational-function
field. The proof uses integral closedness and the Squarefree predicate.
-/
namespace Z2Z4Rank6
open Polynomial

theorem not_isSquare_fraction_of_squarefree {F : Type*} [Field F]
    (p : F[X]) (hp : Squarefree p) (hd : 0<p.natDegree) :
    ¬IsSquare (algebraMap F[X] (RatFunc F) p) := by
  rintro ⟨z,hz⟩
  have hint : IsIntegral F[X] (z^2) := by
    rw [sq,←hz]
    exact isIntegral_algebraMap
  obtain ⟨r,hr⟩ := IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow
    (R:=F[X]) (by decide : 0<(2:ℕ)) hint
  have heq : p=r*r := by
    apply RatFunc.algebraMap_injective F
    simpa only [map_mul,hr] using hz
  have hu : IsUnit r := hp r (by rw [heq])
  exact (Polynomial.not_isUnit_of_natDegree_pos p hd) (by simpa only [heq] using hu.mul hu)

theorem not_isSquare_fraction_of_odd_degree {F : Type*} [Field F]
    (p : F[X]) (hp : Odd p.natDegree) :
    ¬IsSquare (algebraMap F[X] (RatFunc F) p) := by
  rintro ⟨z,hz⟩
  have hint : IsIntegral F[X] (z^2) := by
    rw [sq,←hz]
    exact isIntegral_algebraMap
  obtain ⟨r,hr⟩ := IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow
    (R:=F[X]) (by decide : 0<(2:ℕ)) hint
  have heq : p=r*r := by
    apply RatFunc.algebraMap_injective F
    simpa only [map_mul,hr] using hz
  have hr0 : r≠0 := by
    intro h
    rw [heq,h,mul_zero] at hp
    norm_num at hp
  have hd := congrArg Polynomial.natDegree heq
  rw [Polynomial.natDegree_mul hr0 hr0] at hd
  obtain ⟨n,hn⟩ := hp
  omega

end Z2Z4Rank6
