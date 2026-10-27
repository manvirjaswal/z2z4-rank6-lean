import Z2Z4Rank6.InfinityBaseOverlapCoordinates
import Z2Z4Rank6.PositiveLaurentRange

/-! Weighted Laurent inversion identifies the infinity restriction
range with the precise negative exponent submodule. -/
namespace Z2Z4Rank6.NegativeLaurentRange
noncomputable section
open LaurentCechQuotient AffineBaseFunctionFieldIso PositiveLaurentRange

def weightedReverse (f : FourLaurent) (i : Fin 4) : LaurentPolynomial ℚ :=
  LaurentPolynomial.invert (f i)*LaurentPolynomial.T (-weights i)

theorem weightedReverse_involutive (f : FourLaurent) : weightedReverse (weightedReverse f)=f := by
  funext i
  simp only [weightedReverse,map_mul,LaurentPolynomial.invert_T,neg_neg]
  rw [mul_assoc,←LaurentPolynomial.T_add,add_neg_cancel,LaurentPolynomial.T_zero,mul_one]
  exact LaurentPolynomial.involutive_invert (f i)

theorem weightedReverse_coeff (f : FourLaurent) (i : Fin 4) (n : ℤ) :
    (weightedReverse f i).coeff n=(f i).coeff (-n-weights i) := by
  simp only [weightedReverse,LaurentPolynomial.T,AddMonoidAlgebra.coeff_mul_single_apply,
    mul_one,LaurentPolynomial.invert_apply]
  congr 1
  omega

theorem mem_negativeFour_iff (f : FourLaurent) :
    f∈negativeFour↔∀(i : Fin 4)(n : ℤ),-weights i<n→(f i).coeff n=0 := by
  rw [negativeFour,Submodule.mem_map]
  constructor
  · rintro ⟨g,hg,rfl⟩ i n hn
    have hs := (Finsupp.mem_supported' ℚ g).mp hg
    change (coordinatesEquiv g i).coeff n=0
    rw [coordinatesEquiv_coeff]
    apply hs (i,n)
    change ¬n≤-weights i
    omega
  · intro h
    refine ⟨coordinatesEquiv.symm f,?_,coordinatesEquiv.apply_symm_apply f⟩
    rw [negativePart,Finsupp.mem_supported']
    intro p hp
    have hn : -weights p.1<p.2 := by
      change ¬p.2≤-weights p.1 at hp
      omega
    have hc := coordinatesEquiv_coeff (coordinatesEquiv.symm f) p.1 p.2
    rw [coordinatesEquiv.apply_symm_apply] at hc
    exact hc.symm.trans (h p.1 p.2 hn)

theorem weightedReverse_mem_negative_iff (f : FourLaurent) :
    weightedReverse f∈negativeFour↔f∈positiveFour := by
  rw [mem_negativeFour_iff,mem_positiveFour_iff]
  constructor
  · intro h i n hn
    have hh := h i (-n-weights i) (by omega)
    rw [weightedReverse_coeff] at hh
    have he : -(-n-weights i)-weights i=n := by omega
    rwa [he] at hh
  · intro h i n hn
    rw [weightedReverse_coeff]
    exact h i (-n-weights i) (by omega)

def negativeRestriction : ProjectiveBaseSchemeCharts.InfinityCoordinateRing→ₗ[ℚ]FourLaurent :=
  overlapCoordinates.toLinearMap.comp infinityRestriction.toLinearMap
@[simp] theorem negativeRestriction_apply
    (c : ProjectiveBaseSchemeCharts.InfinityCoordinateRing) (i : Fin 4) :
    negativeRestriction c i=reversePolynomial (infinityBasis.repr c i)*LaurentPolynomial.T (-weights i) :=
  overlapCoordinates_infinityRestriction c i

/-- The image of the infinity quotient restriction, expressed in the
localized basis, is exactly the negative Laurent coefficient module. -/
theorem negativeRestriction_range : LinearMap.range negativeRestriction=negativeFour := by
  ext f
  constructor
  · rintro ⟨c,rfl⟩
    let p : Fin 4→Poly := fun i=>infinityBasis.repr c i
    have hp : polynomialTupleMap p∈positiveFour := by
      rw [←polynomialTupleMap_range]
      exact ⟨p,rfl⟩
    have he : negativeRestriction c=weightedReverse (polynomialTupleMap p) := by
      funext i
      rw [negativeRestriction_apply]
      simp only [weightedReverse,polynomialTupleMap_apply,←reversePolynomial_eq_invert,p]
    rw [he]
    exact (weightedReverse_mem_negative_iff _).mpr hp
  · intro hf
    have hh : weightedReverse f∈positiveFour := by
      apply (weightedReverse_mem_negative_iff (weightedReverse f)).mp
      rwa [weightedReverse_involutive]
    rw [←polynomialTupleMap_range] at hh
    obtain ⟨p,hp⟩ := hh
    let coeffs : Fin 4→₀Poly := (Finsupp.linearEquivFunOnFinite Poly Poly (Fin 4)).symm p
    let c : ProjectiveBaseSchemeCharts.InfinityCoordinateRing := infinityBasis.repr.symm coeffs
    refine ⟨c,?_⟩
    funext i
    have hc : infinityBasis.repr c i=p i := by
      change infinityBasis.repr (infinityBasis.repr.symm coeffs) i=p i
      rw [infinityBasis.repr.apply_symm_apply]
      rfl
    rw [negativeRestriction_apply,hc,reversePolynomial_eq_invert]
    have hp' : Polynomial.toLaurent (p i)=weightedReverse f i := congrFun hp i
    rw [hp']
    exact congrFun (weightedReverse_involutive f) i
end
end Z2Z4Rank6.NegativeLaurentRange
