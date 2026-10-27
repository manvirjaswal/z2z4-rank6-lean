module

public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
public import Mathlib.Tactic.Ring

@[expose] public section

/-! The exact transition for a numerator of arbitrary weight on two
degree-one homogeneous charts. -/
namespace Z2Z4Rank6.WeightedHomogeneousChartTransition
noncomputable section
open scoped Classical
variable {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

theorem transition (f g a : A) (n : ℕ) (hf : f∈𝒜 1) (hg : g∈𝒜 1)
    (ha : a∈𝒜 (n • (1:ℕ))) :
    HomogeneousLocalization.awayMap 𝒜 hf (mul_comm f g)
      (HomogeneousLocalization.Away.mk 𝒜 hg n a ha)*
    HomogeneousLocalization.awayMap 𝒜 hg (rfl : f*g=f*g)
      (HomogeneousLocalization.Away.mk 𝒜 hf 1 g hg)^n=
    HomogeneousLocalization.awayMap 𝒜 hg (rfl : f*g=f*g)
      (HomogeneousLocalization.Away.mk 𝒜 hf n a ha) := by
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.val_mul,HomogeneousLocalization.val_pow,
    HomogeneousLocalization.awayMap_mk,HomogeneousLocalization.Away.val_mk,pow_one]
  rw [Localization.mk_pow,Localization.mk_mul,Localization.mk_eq_mk_iff,
    Localization.r_iff_exists]
  refine ⟨1,?_⟩
  simp only [OneMemClass.coe_one,one_mul,Submonoid.coe_mul,SubmonoidClass.coe_pow]
  simp only [mul_pow]
  ring
end
end Z2Z4Rank6.WeightedHomogeneousChartTransition
