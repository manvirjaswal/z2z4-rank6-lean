module

public import Z2Z4Rank6.TwoChartEqualizer

@[expose] public section

/-!
# Transport of compatible chart pairs

A commutative diagram of linear equivalences transports the kernel
of the two chart restriction difference.
-/

namespace Z2Z4Rank6.TwoChartKernelTransport
noncomputable section
open TwoChartEqualizer

variable {R A B C A' B' C' : Type*} [Field R]
variable [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
variable [AddCommGroup A'] [AddCommGroup B'] [AddCommGroup C']
variable [Module R A] [Module R B] [Module R C]
variable [Module R A'] [Module R B'] [Module R C']

def equiv (f : A→ₗ[R]B) (g : C→ₗ[R]B) (f' : A'→ₗ[R]B') (g' : C'→ₗ[R]B')
    (eA : A≃ₗ[R]A') (eC : C≃ₗ[R]C') (eB : B≃ₗ[R]B')
    (hf : ∀a,eB (f a)=f' (eA a)) (hg : ∀c,eB (g c)=g' (eC c)) :
    LinearMap.ker (difference f g)≃ₗ[R]LinearMap.ker (difference f' g') where
  toFun p := ⟨(eA p.1.1,eC p.1.2),by
    apply (mem_ker_difference f' g' _).mpr
    exact (hf _).symm.trans ((congrArg eB ((mem_ker_difference f g _).mp p.2)).trans (hg _))⟩
  invFun p := ⟨(eA.symm p.1.1,eC.symm p.1.2),by
    apply (mem_ker_difference f g _).mpr
    apply eB.injective
    rw [hf,hg,eA.apply_symm_apply,eC.apply_symm_apply]
    exact (mem_ker_difference f' g' _).mp p.2⟩
  left_inv p := Subtype.ext (Prod.ext (eA.symm_apply_apply _) (eC.symm_apply_apply _))
  right_inv p := Subtype.ext (Prod.ext (eA.apply_symm_apply _) (eC.apply_symm_apply _))
  map_add' p q := Subtype.ext (Prod.ext (map_add eA _ _) (map_add eC _ _))
  map_smul' r p := Subtype.ext (Prod.ext (map_smul eA r _) (map_smul eC r _))

end
end Z2Z4Rank6.TwoChartKernelTransport
