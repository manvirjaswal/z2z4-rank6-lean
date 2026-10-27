import Z2Z4Rank6.ThirdTwistField
import Z2Z4Rank6.FunctionFieldAutomorphisms

/-! The three root signs of Q(m,u,v,w), with common fixed
field precisely the embedded Q(m). -/

namespace Z2Z4Rank6.ThirdTwistField
noncomputable section

@[simp] theorem oldSigmaU_d3 : FunctionField.sigmaU d3Old=d3Old :=
  FunctionField.sigmaU.commutes d3

@[simp] theorem oldSigmaV_d3 : FunctionField.sigmaV d3Old=d3Old :=
  FunctionField.sigmaV.commutes d3

def sigmaU : K ≃ₐ[Base] K where
  toFun z := ⟨FunctionField.sigmaU z.re,FunctionField.sigmaU z.im⟩
  invFun z := ⟨FunctionField.sigmaU z.re,FunctionField.sigmaU z.im⟩
  left_inv z := by apply QuadraticAlgebra.ext <;> exact FunctionField.sigmaU_involutive _
  right_inv z := by apply QuadraticAlgebra.ext <;> exact FunctionField.sigmaU_involutive _
  map_add' z t := by apply QuadraticAlgebra.ext <;> simp
  map_mul' z t := by
    apply QuadraticAlgebra.ext <;> simp only [QuadraticAlgebra.re_mul,
      QuadraticAlgebra.im_mul,map_add,map_mul,map_zero,oldSigmaU_d3]
  commutes' c := by
    rw [IsScalarTower.algebraMap_apply Base FunctionField.K K]
    apply QuadraticAlgebra.ext
    · exact FunctionField.sigmaU.commutes c
    · simp

def sigmaV : K ≃ₐ[Base] K where
  toFun z := ⟨FunctionField.sigmaV z.re,FunctionField.sigmaV z.im⟩
  invFun z := ⟨FunctionField.sigmaV z.re,FunctionField.sigmaV z.im⟩
  left_inv z := by apply QuadraticAlgebra.ext <;> exact FunctionField.sigmaV_involutive _
  right_inv z := by apply QuadraticAlgebra.ext <;> exact FunctionField.sigmaV_involutive _
  map_add' z t := by apply QuadraticAlgebra.ext <;> simp
  map_mul' z t := by
    apply QuadraticAlgebra.ext <;> simp only [QuadraticAlgebra.re_mul,
      QuadraticAlgebra.im_mul,map_add,map_mul,map_zero,oldSigmaV_d3]
  commutes' c := by
    rw [IsScalarTower.algebraMap_apply Base FunctionField.K K]
    apply QuadraticAlgebra.ext
    · exact FunctionField.sigmaV.commutes c
    · simp

def sigmaW : K ≃ₐ[Base] K :=
  {starRingAut with
    commutes' := by
      intro c
      rw [IsScalarTower.algebraMap_apply Base FunctionField.K K]
      apply QuadraticAlgebra.ext <;> simp}

@[simp] theorem sigmaW_apply (z : K) : sigmaW z=star z := rfl

@[simp] theorem sigmaU_old (z : FunctionField.K) :
    sigmaU (algebraMap FunctionField.K K z)=algebraMap FunctionField.K K (FunctionField.sigmaU z) := by
  apply QuadraticAlgebra.ext <;> simp [sigmaU]

@[simp] theorem sigmaV_old (z : FunctionField.K) :
    sigmaV (algebraMap FunctionField.K K z)=algebraMap FunctionField.K K (FunctionField.sigmaV z) := by
  apply QuadraticAlgebra.ext <;> simp [sigmaV]

@[simp] theorem sigmaW_old (z : FunctionField.K) :
    sigmaW (algebraMap FunctionField.K K z)=algebraMap FunctionField.K K z := by
  apply QuadraticAlgebra.ext <;> simp

@[simp] theorem sigmaU_base (c : Base) : sigmaU (algebraMap Base K c)=algebraMap Base K c :=
  sigmaU.commutes c
@[simp] theorem sigmaV_base (c : Base) : sigmaV (algebraMap Base K c)=algebraMap Base K c :=
  sigmaV.commutes c
@[simp] theorem sigmaW_base (c : Base) : sigmaW (algebraMap Base K c)=algebraMap Base K c :=
  sigmaW.commutes c

@[simp] theorem sigmaU_m : sigmaU m=m := by rw [m,sigmaU_old,FunctionField.sigmaU_m]
@[simp] theorem sigmaV_m : sigmaV m=m := by rw [m,sigmaV_old,FunctionField.sigmaV_m]
@[simp] theorem sigmaW_m : sigmaW m=m := by rw [m,sigmaW_old]
@[simp] theorem sigmaU_u : sigmaU u= -u := by rw [u,sigmaU_old,FunctionField.sigmaU_u,map_neg]
@[simp] theorem sigmaU_v : sigmaU v=v := by rw [v,sigmaU_old,FunctionField.sigmaU_v]
@[simp] theorem sigmaV_u : sigmaV u=u := by rw [u,sigmaV_old,FunctionField.sigmaV_u]
@[simp] theorem sigmaV_v : sigmaV v= -v := by rw [v,sigmaV_old,FunctionField.sigmaV_v,map_neg]
@[simp] theorem sigmaW_u : sigmaW u=u := by rw [u,sigmaW_old]
@[simp] theorem sigmaW_v : sigmaW v=v := by rw [v,sigmaW_old]

@[simp] theorem sigmaU_w : sigmaU w=w := by
  apply QuadraticAlgebra.ext <;> simp [sigmaU,w,QuadraticAlgebra.omega]
@[simp] theorem sigmaV_w : sigmaV w=w := by
  apply QuadraticAlgebra.ext <;> simp [sigmaV,w,QuadraticAlgebra.omega]
@[simp] theorem sigmaW_w : sigmaW w= -w := by
  apply QuadraticAlgebra.ext <;> simp [w,QuadraticAlgebra.omega]

theorem sigmaU_involutive (z : K) : sigmaU (sigmaU z)=z := by
  apply QuadraticAlgebra.ext <;> exact FunctionField.sigmaU_involutive _
theorem sigmaV_involutive (z : K) : sigmaV (sigmaV z)=z := by
  apply QuadraticAlgebra.ext <;> exact FunctionField.sigmaV_involutive _
theorem sigmaW_involutive (z : K) : sigmaW (sigmaW z)=z := star_star z

theorem sigmaU_sigmaV_commute (z : K) : sigmaU (sigmaV z)=sigmaV (sigmaU z) := by
  apply QuadraticAlgebra.ext <;> exact FunctionField.sigmaU_sigmaV_commute _
theorem sigmaU_sigmaW_commute (z : K) : sigmaU (sigmaW z)=sigmaW (sigmaU z) := by
  apply QuadraticAlgebra.ext <;> simp [sigmaU]
theorem sigmaV_sigmaW_commute (z : K) : sigmaV (sigmaW z)=sigmaW (sigmaV z) := by
  apply QuadraticAlgebra.ext <;> simp [sigmaV]

theorem fixed_iff_in_base (z : K) :
    (sigmaU z=z ∧ sigmaV z=z ∧ sigmaW z=z) ↔ ∃ c : Base,algebraMap Base K c=z := by
  constructor
  · rintro ⟨hU,hV,hW⟩
    have hi : z.im=0 := by
      have h := congrArg QuadraticAlgebra.im hW
      change -z.im=z.im at h
      have h2 : (2 : FunctionField.K)*z.im=0 := by linear_combination -h
      exact (mul_eq_zero.mp h2).resolve_left (by norm_num)
    have hUr : FunctionField.sigmaU z.re=z.re := congrArg QuadraticAlgebra.re hU
    have hVr : FunctionField.sigmaV z.re=z.re := congrArg QuadraticAlgebra.re hV
    obtain ⟨c,hc⟩ := FunctionField.exists_base_of_fixed z.re hUr hVr
    refine ⟨c,?_⟩
    rw [IsScalarTower.algebraMap_apply Base FunctionField.K K]
    apply QuadraticAlgebra.ext
    · exact hc
    · exact hi.symm
  · rintro ⟨c,rfl⟩
    exact ⟨sigmaU_base c,sigmaV_base c,sigmaW_base c⟩

end
end Z2Z4Rank6.ThirdTwistField
