module

public import Z2Z4Rank6.LaurentCechQuotient
public import Mathlib.Algebra.Polynomial.Basis

@[expose] public section

/-!
# Polynomial chart coefficients inside the Laurent module

The positive-chart range calculation for the algebraic two-chart component
of Jaswal Section 3, DOI 10.5281/zenodo.23437117. The range is proved using
polynomial/Laurent coefficient maps. The chart restriction is linked separately.
-/

namespace Z2Z4Rank6.PositiveLaurentRange
noncomputable section
open LaurentCechQuotient Polynomial
open scoped Classical

def polynomialCoefficients : ℚ[X]≃ₗ[ℚ](ℕ→₀ℚ) :=
  (Polynomial.toFinsuppIsoLinear ℚ).trans (AddMonoidAlgebra.coeffLinearEquiv ℚ)

@[simp] theorem polynomialCoefficients_apply (p : ℚ[X]) :
    polynomialCoefficients p=p.toFinsupp.coeff := rfl

theorem polynomial_range_iff (p : LaurentPolynomial ℚ) :
    (∃q : ℚ[X],q.toLaurent=p)↔∀n : ℤ,n<0→p.coeff n=0 := by
  constructor
  · rintro ⟨q,rfl⟩ n hn
    rw [LaurentPolynomial.coeff_toLaurent]
    apply Finsupp.mapDomain_of_notMem_range
    rintro ⟨k,hk⟩
    have hk0 : (0:ℤ)≤(k:ℤ) := Int.natCast_nonneg k
    exact (not_le_of_gt hn) (hk ▸ hk0)
  · intro h
    have hrange : p.coeff∈Set.range (Finsupp.mapDomain (fun n : ℕ => (n:ℤ))) := by
      apply (Finsupp.mem_range_mapDomain_iff _ Nat.cast_injective p.coeff).mpr
      intro n hn
      apply h n
      by_contra hnot
      have hnonneg : 0≤n := le_of_not_gt hnot
      obtain ⟨k,rfl⟩ := Int.eq_ofNat_of_zero_le hnonneg
      exact hn ⟨k,rfl⟩
    obtain ⟨f,hf⟩ := hrange
    refine ⟨polynomialCoefficients.symm f,?_⟩
    apply LaurentPolynomial.ext
    intro n
    rw [LaurentPolynomial.coeff_toLaurent]
    have hcoeff : (polynomialCoefficients.symm f).toFinsupp.coeff=f :=
      polynomialCoefficients.apply_symm_apply f
    rw [hcoeff]
    exact congrArg (fun g : ℤ→₀ℚ => g n) hf

theorem mem_positiveFour_iff (f : FourLaurent) :
    f∈positiveFour↔∀(i : Fin 4) (n : ℤ),n<0→(f i).coeff n=0 := by
  rw [positiveFour,Submodule.mem_map]
  constructor
  · rintro ⟨g,hg,rfl⟩ i n hn
    have hs := (Finsupp.mem_supported' ℚ g).mp hg
    change (coordinatesEquiv g i).coeff n=0
    rw [coordinatesEquiv_coeff]
    apply hs (i,n)
    change ¬0≤n
    omega
  · intro h
    refine ⟨coordinatesEquiv.symm f,?_,coordinatesEquiv.apply_symm_apply f⟩
    rw [positivePart,Finsupp.mem_supported']
    intro p hp
    have hn : p.2<0 := by
      change ¬0≤p.2 at hp
      omega
    have hc := coordinatesEquiv_coeff (coordinatesEquiv.symm f) p.1 p.2
    rw [coordinatesEquiv.apply_symm_apply] at hc
    exact hc.symm.trans (h p.1 p.2 hn)

def polynomialTupleMap : (Fin 4→ℚ[X])→ₗ[ℚ]FourLaurent :=
  LinearMap.pi fun i : Fin 4 =>
    (Polynomial.toLaurentAlg : ℚ[X]→ₐ[ℚ]LaurentPolynomial ℚ).toLinearMap.comp (LinearMap.proj i)

@[simp] theorem polynomialTupleMap_apply (f : Fin 4→ℚ[X]) (i : Fin 4) :
    polynomialTupleMap f i=(f i).toLaurent := rfl

/-- The range of four polynomial coefficient embeddings is exactly
the positive Laurent coefficient submodule used in the quotient. -/
theorem polynomialTupleMap_range : LinearMap.range polynomialTupleMap=positiveFour := by
  ext f
  constructor
  · rintro ⟨q,rfl⟩
    apply (mem_positiveFour_iff _).mpr
    intro i
    exact (polynomial_range_iff _).mp ⟨q i,rfl⟩
  · intro hf
    have hq : ∀i : Fin 4,∃q : ℚ[X],q.toLaurent=f i :=
      fun i => (polynomial_range_iff _).mpr ((mem_positiveFour_iff _).mp hf i)
    choose q hq using hq
    exact ⟨q,funext hq⟩

end
end Z2Z4Rank6.PositiveLaurentRange
