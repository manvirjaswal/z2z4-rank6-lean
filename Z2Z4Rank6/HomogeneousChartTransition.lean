module

public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
public import Mathlib.Tactic.Ring

@[expose] public section

/-! The transition identity between two degree-one homogeneous charts,
proved generically before instantiating complicated coordinate quotient rings. -/
namespace Z2Z4Rank6.HomogeneousChartTransition
noncomputable section
open scoped Classical

variable {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

theorem transition (f g a : A) (hf : f∈𝒜 1) (hg : g∈𝒜 1) (ha : a∈𝒜 1) :
    HomogeneousLocalization.awayMap 𝒜 hf (mul_comm f g)
      (HomogeneousLocalization.Away.mk 𝒜 hg 1 a ha)*
    HomogeneousLocalization.awayMap 𝒜 hg (rfl : f*g=f*g)
      (HomogeneousLocalization.Away.mk 𝒜 hf 1 g hg)=
    HomogeneousLocalization.awayMap 𝒜 hg (rfl : f*g=f*g)
      (HomogeneousLocalization.Away.mk 𝒜 hf 1 a ha) := by
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.val_mul,HomogeneousLocalization.awayMap_mk,
    HomogeneousLocalization.Away.val_mk,pow_one]
  rw [Localization.mk_mul,Localization.mk_eq_mk_iff,Localization.r_iff_exists]
  refine ⟨1,?_⟩
  simp only [OneMemClass.coe_one,one_mul,Submonoid.coe_mul]
  ring

end
end Z2Z4Rank6.HomogeneousChartTransition
