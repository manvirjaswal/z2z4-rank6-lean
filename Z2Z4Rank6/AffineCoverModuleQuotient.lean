import Mathlib.LinearAlgebra.Prod
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# The restriction cokernel for two affine charts

Pure module algebra used with the two-open Mayer–Vietoris comparison.
The difference-map image is the sum of the two restriction images, and
a linear equivalence carrying those images transports the quotient.
-/
namespace Z2Z4Rank6.AffineCoverModuleQuotient
noncomputable section

variable {R M N V W : Type*} [CommRing R]
variable [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
variable [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]

/-- The two-open Čech differential, restriction left minus restriction right. -/
def difference (f : M →ₗ[R] V) (g : N →ₗ[R] V) : M×N →ₗ[R] V := f.coprod (-g)

@[simp] theorem difference_apply (f : M →ₗ[R] V) (g : N →ₗ[R] V) (x : M) (y : N) :
    difference f g (x,y)=f x-g y := by simp [difference,sub_eq_add_neg]

theorem range_difference (f : M →ₗ[R] V) (g : N →ₗ[R] V) :
    LinearMap.range (difference f g)=LinearMap.range f ⊔ LinearMap.range g := by
  rw [difference,LinearMap.range_coprod,LinearMap.range_neg]

/-- Transport of the restriction cokernel under identified image submodules. -/
def quotientTransport (f : M →ₗ[R] V) (g : N →ₗ[R] V) (e : V ≃ₗ[R] W)
    (P Q : Submodule R W) (hf : (LinearMap.range f).map e.toLinearMap=P)
    (hg : (LinearMap.range g).map e.toLinearMap=Q) :
    (V ⧸ LinearMap.range (difference f g)) ≃ₗ[R] W ⧸ (P⊔Q) :=
  Submodule.Quotient.equiv _ _ e (by rw [range_difference,Submodule.map_sup,hf,hg])

/-- An equivalent formulation useful when the two image ranges are already transported. -/
theorem map_range_difference (f : M →ₗ[R] V) (g : N →ₗ[R] V) (e : V ≃ₗ[R] W) :
    (LinearMap.range (difference f g)).map e.toLinearMap=
      LinearMap.range (e.toLinearMap.comp f) ⊔ LinearMap.range (e.toLinearMap.comp g) := by
  rw [range_difference,Submodule.map_sup,←LinearMap.range_comp,←LinearMap.range_comp]

end
end Z2Z4Rank6.AffineCoverModuleQuotient
