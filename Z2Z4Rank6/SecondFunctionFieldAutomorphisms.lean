module

public import Z2Z4Rank6.SecondFunctionField
public import Z2Z4Rank6.PointMap

@[expose] public section

/-! The two sign changes of s₂ and s₃ in the field Q(G₂).
They fix Q(W,s₁). These two commuting involutions already separate the
four character classes used by the six printed sections. -/

namespace Z2Z4Rank6.SecondFunctionField
noncomputable section

def secondConjugation : Second ≃ₐ[First] Second :=
  { starRingAut with
    commutes' := by
      intro c
      apply QuadraticAlgebra.ext <;> simp }

@[simp] theorem secondConjugation_apply (z : Second) : secondConjugation z=star z := rfl

@[simp] theorem secondConjugation_involutive (z : Second) :
    secondConjugation (secondConjugation z)=z := star_star z

@[simp] theorem secondConjugation_dB : secondConjugation dBSecond=dBSecond :=
  secondConjugation.commutes dBFirst

def sigma2 : K ≃ₐ[First] K where
  toFun z := ⟨secondConjugation z.re,secondConjugation z.im⟩
  invFun z := ⟨secondConjugation z.re,secondConjugation z.im⟩
  left_inv z := by apply QuadraticAlgebra.ext <;> exact secondConjugation_involutive _
  right_inv z := by apply QuadraticAlgebra.ext <;> exact secondConjugation_involutive _
  map_add' z w := by apply QuadraticAlgebra.ext <;> simp
  map_mul' z w := by
    apply QuadraticAlgebra.ext <;>
      simp only [QuadraticAlgebra.re_mul,QuadraticAlgebra.im_mul,
        map_add,map_mul,map_zero,secondConjugation_dB]
  commutes' c := by
    rw [IsScalarTower.algebraMap_apply First Second K]
    apply QuadraticAlgebra.ext
    · exact secondConjugation.commutes c
    · simp

def sigma3 : K ≃ₐ[First] K :=
  { starRingAut with
    commutes' := by
      intro c
      rw [IsScalarTower.algebraMap_apply First Second K]
      apply QuadraticAlgebra.ext <;> simp }

@[simp] theorem sigma3_apply (z : K) : sigma3 z=star z := rfl

@[simp] theorem sigma2_first (r : First) : sigma2 (algebraMap First K r)=algebraMap First K r :=
  sigma2.commutes r

@[simp] theorem sigma3_first (r : First) : sigma3 (algebraMap First K r)=algebraMap First K r :=
  sigma3.commutes r

@[simp] theorem sigma2_W : sigma2 W=W := by
  rw [W,IsScalarTower.algebraMap_apply Base First K,sigma2_first]

@[simp] theorem sigma3_W : sigma3 W=W := by
  rw [W,IsScalarTower.algebraMap_apply Base First K,sigma3_first]

@[simp] theorem sigma2_s1 : sigma2 s1=s1 := sigma2_first _
@[simp] theorem sigma3_s1 : sigma3 s1=s1 := sigma3_first _

@[simp] theorem sigma2_s2 : sigma2 s2= -s2 := by
  apply QuadraticAlgebra.ext <;> simp [sigma2,s2,QuadraticAlgebra.omega]

@[simp] theorem sigma2_s3 : sigma2 s3=s3 := by
  apply QuadraticAlgebra.ext <;> simp [sigma2,s3,QuadraticAlgebra.omega]

@[simp] theorem sigma3_s2 : sigma3 s2=s2 := by
  apply QuadraticAlgebra.ext <;> simp [s2]

@[simp] theorem sigma3_s3 : sigma3 s3= -s3 := by
  apply QuadraticAlgebra.ext <;> simp [s3,QuadraticAlgebra.omega]

theorem sigma2_involutive (z : K) : sigma2 (sigma2 z)=z := by
  apply QuadraticAlgebra.ext <;> exact secondConjugation_involutive _

theorem sigma3_involutive (z : K) : sigma3 (sigma3 z)=z := star_star z

theorem sigma2_sigma3_commute (z : K) : sigma2 (sigma3 z)=sigma3 (sigma2 z) := by
  apply QuadraticAlgebra.ext <;> simp [sigma2]

end
end Z2Z4Rank6.SecondFunctionField
