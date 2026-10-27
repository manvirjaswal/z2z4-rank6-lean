module

public import Z2Z4Rank6.SecondFunctionFieldAutomorphisms
public import Mathlib.FieldTheory.Galois.Basic

@[expose] public section

/-!
# The full degree-eight Galois group of the second base

The three quadratic generators have three commuting sign
automorphisms. Their eight products exhaust the automorphism
group, so Q(G2)/Q(W) is Galois with group (Z/2)^3.
-/
namespace Z2Z4Rank6.SecondFunctionField
noncomputable section

def firstConjugation : First ≃ₐ[Base] First :=
  { starRingAut with
    commutes' := by intro c; apply QuadraticAlgebra.ext <;> simp }

@[simp] theorem firstConjugation_apply (z : First) : firstConjugation z = star z := rfl
@[simp] theorem firstConjugation_involutive (z : First) :
    firstConjugation (firstConjugation z) = z := star_star z
@[simp] theorem firstConjugation_dA : firstConjugation dAFirst = dAFirst :=
  firstConjugation.commutes dA

def firstLift : Second ≃ₐ[Base] Second where
  toFun z := ⟨firstConjugation z.re, firstConjugation z.im⟩
  invFun z := ⟨firstConjugation z.re, firstConjugation z.im⟩
  left_inv z := by apply QuadraticAlgebra.ext <;> exact firstConjugation_involutive _
  right_inv z := by apply QuadraticAlgebra.ext <;> exact firstConjugation_involutive _
  map_add' z w := by apply QuadraticAlgebra.ext <;> simp
  map_mul' z w := by
    apply QuadraticAlgebra.ext <;>
      simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul,
        map_add, map_mul, map_zero, firstConjugation_dA]
  commutes' c := by
    rw [IsScalarTower.algebraMap_apply Base First Second]
    apply QuadraticAlgebra.ext
    · exact firstConjugation.commutes c
    · simp

@[simp] theorem firstLift_involutive (z : Second) : firstLift (firstLift z) = z := by
  apply QuadraticAlgebra.ext <;> exact firstConjugation_involutive _

@[simp] theorem firstLift_dB : firstLift dBSecond = dBSecond := by
  change firstLift (algebraMap First Second (algebraMap Base First dB)) = _
  rw [←IsScalarTower.algebraMap_apply Base First Second]
  exact firstLift.commutes dB

def sigma1 : K ≃ₐ[Base] K where
  toFun z := ⟨firstLift z.re, firstLift z.im⟩
  invFun z := ⟨firstLift z.re, firstLift z.im⟩
  left_inv z := by apply QuadraticAlgebra.ext <;> exact firstLift_involutive _
  right_inv z := by apply QuadraticAlgebra.ext <;> exact firstLift_involutive _
  map_add' z w := by apply QuadraticAlgebra.ext <;> simp
  map_mul' z w := by
    apply QuadraticAlgebra.ext <;>
      simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul,
        map_add, map_mul, map_zero, firstLift_dB]
  commutes' c := by
    rw [IsScalarTower.algebraMap_apply Base Second K]
    apply QuadraticAlgebra.ext
    · exact firstLift.commutes c
    · simp

def sigma2Base : K ≃ₐ[Base] K := sigma2.restrictScalars Base
def sigma3Base : K ≃ₐ[Base] K := sigma3.restrictScalars Base

@[simp] theorem sigma2Base_apply (z : K) : sigma2Base z = sigma2 z := rfl
@[simp] theorem sigma3Base_apply (z : K) : sigma3Base z = sigma3 z := rfl
@[simp] theorem sigma1_base (c : Base) : sigma1 (algebraMap Base K c) = algebraMap Base K c :=
  sigma1.commutes c
@[simp] theorem sigma2_base (c : Base) : sigma2 (algebraMap Base K c) = algebraMap Base K c :=
  sigma2Base.commutes c
@[simp] theorem sigma3_base (c : Base) : sigma3 (algebraMap Base K c) = algebraMap Base K c :=
  sigma3Base.commutes c

@[simp] theorem sigma1_W : sigma1 W = W := sigma1.commutes RatFunc.X

@[simp] theorem sigma1_s1 : sigma1 s1 = -s1 := by
  rw [s1, IsScalarTower.algebraMap_apply First Second K]
  apply QuadraticAlgebra.ext
  · apply QuadraticAlgebra.ext <;> simp [sigma1, firstLift, QuadraticAlgebra.omega]
  · apply QuadraticAlgebra.ext <;> simp [sigma1, firstLift]

@[simp] theorem sigma1_s2 : sigma1 s2 = s2 := by
  apply QuadraticAlgebra.ext <;> simp [sigma1, firstLift, s2, QuadraticAlgebra.omega]
  all_goals rfl

@[simp] theorem sigma1_s3 : sigma1 s3 = s3 := by
  apply QuadraticAlgebra.ext
  · change firstLift 0 = 0
    exact map_zero firstLift
  · change firstLift 1 = 1
    exact map_one firstLift

theorem sigma1_involutive (z : K) : sigma1 (sigma1 z) = z := by
  apply QuadraticAlgebra.ext <;> exact firstLift_involutive _

theorem sigma1_sigma2_commute (z : K) : sigma1 (sigma2 z) = sigma2 (sigma1 z) := by
  apply QuadraticAlgebra.ext <;>
    apply QuadraticAlgebra.ext <;> simp [sigma1, sigma2, firstLift, secondConjugation]

theorem sigma1_sigma3_commute (z : K) : sigma1 (sigma3 z) = sigma3 (sigma1 z) := by
  apply QuadraticAlgebra.ext <;> simp [sigma1]

private theorem zero_of_neg_eq {F : Type*} [Field F] [CharZero F] {z : F}
    (h : -z = z) : z = 0 := by
  have h2 : (2 : F)*z = 0 := by linear_combination -h
  exact (mul_eq_zero.mp h2).resolve_left (by norm_num)

/-- The common fixed field of the three signs is the
embedded rational-function base field. -/
theorem fixed_iff_in_base (z : K) :
    (sigma1 z = z ∧ sigma2 z = z ∧ sigma3 z = z) ↔
      ∃ b : Base, algebraMap Base K b = z := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    have h3im : z.im = 0 := by
      have h := congrArg QuadraticAlgebra.im h3
      change -z.im = z.im at h
      exact zero_of_neg_eq h
    have h2im : z.re.im = 0 := by
      have h := congrArg (fun w : K => w.re.im) h2
      change -z.re.im = z.re.im at h
      exact zero_of_neg_eq h
    have h1im : z.re.re.im = 0 := by
      have h := congrArg (fun w : K => w.re.re.im) h1
      change -z.re.re.im = z.re.re.im at h
      exact zero_of_neg_eq h
    refine ⟨z.re.re.re, ?_⟩
    rw [IsScalarTower.algebraMap_apply Base Second K,
      IsScalarTower.algebraMap_apply Base First Second]
    apply QuadraticAlgebra.ext
    · apply QuadraticAlgebra.ext
      · apply QuadraticAlgebra.ext
        · rfl
        · exact h1im.symm
      · exact h2im.symm
    · exact h3im.symm
  · rintro ⟨b, rfl⟩
    exact ⟨sigma1_base b, sigma2_base b, sigma3_base b⟩

theorem s1_ne_zero : s1 ≠ 0 := by
  intro h
  apply W_ne_zero
  simpa only [h, zero_pow (by decide : 2 ≠ 0)] using s1_sq.symm

theorem s2_ne_zero : s2 ≠ 0 := by
  intro h
  apply qA_W_ne_zero
  simpa only [h, zero_pow (by decide : 2 ≠ 0)] using s2_sq.symm

theorem s3_ne_zero : s3 ≠ 0 := by
  intro h
  apply qB_W_ne_zero
  simpa only [h, zero_pow (by decide : 2 ≠ 0)] using s3_sq.symm

instance finiteDimensional_full : FiniteDimensional Base K := Module.Finite.of_basis basis

def signAut (t : ZMod 2 × ZMod 2 × ZMod 2) : K ≃ₐ[Base] K :=
  (if t.1 = 0 then 1 else sigma1) *
    ((if t.2.1 = 0 then 1 else sigma2Base) * (if t.2.2 = 0 then 1 else sigma3Base))

theorem signAut000 : signAut (0,0,0) = 1 := by simp [signAut]
theorem signAut100 : signAut (1,0,0) = sigma1 := by simp [signAut]
theorem signAut010 : signAut (0,1,0) = sigma2Base := by simp [signAut]
theorem signAut001 : signAut (0,0,1) = sigma3Base := by simp [signAut]
theorem signAut110 : signAut (1,1,0) = sigma1*sigma2Base := by simp [signAut]
theorem signAut101 : signAut (1,0,1) = sigma1*sigma3Base := by simp [signAut]
theorem signAut011 : signAut (0,1,1) = sigma2Base*sigma3Base := by simp [signAut]
theorem signAut111 : signAut (1,1,1) = sigma1*(sigma2Base*sigma3Base) := by simp [signAut]

def signHom : Multiplicative (ZMod 2 × ZMod 2 × ZMod 2) →* (K ≃ₐ[Base] K) where
  toFun t := signAut t.toAdd
  map_one' := by simp [signAut]
  map_mul' g h := by
    rcases g with ⟨a, b, c⟩
    rcases h with ⟨d, e, f⟩
    change signAut ((a,b,c)+(d,e,f)) = signAut (a,b,c)*signAut (d,e,f)
    fin_cases a <;> fin_cases b <;> fin_cases c <;>
      fin_cases d <;> fin_cases e <;> fin_cases f <;>
      simp only [show (⟨0,by decide⟩ : Fin 2) = (0 : ZMod 2) by rfl,
        show (⟨1,by decide⟩ : Fin 2) = (1 : ZMod 2) by rfl,
        Prod.mk_add_mk, show (0 : ZMod 2)+0=0 by decide,
        show (0 : ZMod 2)+1=1 by decide, show (1 : ZMod 2)+0=1 by decide,
        show (1 : ZMod 2)+1=0 by decide,
        signAut000, signAut100, signAut010, signAut001,
        signAut110, signAut101, signAut011, signAut111] <;>
      apply AlgEquiv.ext <;> intro z <;>
      simp only [AlgEquiv.mul_apply, AlgEquiv.one_apply, sigma2Base_apply, sigma3Base_apply,
        sigma1_involutive, sigma2_involutive,
        sigma3_involutive, sigma1_sigma2_commute, sigma1_sigma3_commute, sigma2_sigma3_commute]

theorem signAut_s1 (t : ZMod 2 × ZMod 2 × ZMod 2) :
    signAut t s1 = if t.1 = 0 then s1 else -s1 := by
  have hs : star s1 = s1 := sigma3_s1
  rcases t with ⟨a,b,c⟩
  by_cases ha : a=0 <;> by_cases hb : b=0 <;> by_cases hc : c=0 <;>
    simp [signAut, ha, hb, hc, AlgEquiv.mul_apply, hs]

theorem signAut_s2 (t : ZMod 2 × ZMod 2 × ZMod 2) :
    signAut t s2 = if t.2.1 = 0 then s2 else -s2 := by
  have hs : star s2 = s2 := sigma3_s2
  rcases t with ⟨a,b,c⟩
  by_cases ha : a=0 <;> by_cases hb : b=0 <;> by_cases hc : c=0 <;>
    simp [signAut, ha, hb, hc, AlgEquiv.mul_apply, hs]

theorem signAut_s3 (t : ZMod 2 × ZMod 2 × ZMod 2) :
    signAut t s3 = if t.2.2 = 0 then s3 else -s3 := by
  have hs : star s3 = -s3 := sigma3_s3
  rcases t with ⟨a,b,c⟩
  by_cases ha : a=0 <;> by_cases hb : b=0 <;> by_cases hc : c=0 <;>
    simp [signAut, ha, hb, hc, AlgEquiv.mul_apply, hs]

theorem signHom_injective : Function.Injective signHom := by
  intro g h he
  rcases g with ⟨a,b,c⟩
  rcases h with ⟨d,e,f⟩
  change signAut (a,b,c) = signAut (d,e,f) at he
  change (a,b,c) = (d,e,f)
  have h1 := congrArg (fun u : K ≃ₐ[Base] K => u s1) he
  have h2 := congrArg (fun u : K ≃ₐ[Base] K => u s2) he
  have h3 := congrArg (fun u : K ≃ₐ[Base] K => u s3) he
  rw [signAut_s1, signAut_s1] at h1
  rw [signAut_s2, signAut_s2] at h2
  rw [signAut_s3, signAut_s3] at h3
  have hne1 : -s1 ≠ s1 := fun h => s1_ne_zero (zero_of_neg_eq h)
  have hne2 : -s2 ≠ s2 := fun h => s2_ne_zero (zero_of_neg_eq h)
  have hne3 : -s3 ≠ s3 := fun h => s3_ne_zero (zero_of_neg_eq h)
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    fin_cases d <;> fin_cases e <;> fin_cases f <;>
    simp only [show (⟨0,by decide⟩ : Fin 2) = (0 : ZMod 2) by rfl,
      show (⟨1,by decide⟩ : Fin 2) = (1 : ZMod 2) by rfl,
      ite_true, ite_eq_right (by decide : (1 : ZMod 2) ≠ 0)] at h1 h2 h3 <;>
    first | rfl | exact (hne1 h1).elim | exact (hne1 h1.symm).elim |
      exact (hne2 h2).elim | exact (hne2 h2.symm).elim |
      exact (hne3 h3).elim | exact (hne3 h3.symm).elim

theorem card_automorphisms : Fintype.card (K ≃ₐ[Base] K) = 8 := by
  have hu := AlgEquiv.card_le (F := Base) (K := K)
  have hl := Fintype.card_le_of_injective signHom signHom_injective
  have h8 : Fintype.card (Multiplicative (ZMod 2 × ZMod 2 × ZMod 2)) = 8 := by decide
  rw [finrank_eq_eight] at hu
  rw [h8] at hl
  exact le_antisymm hu hl

instance isGalois_full : IsGalois Base K := by
  apply IsGalois.of_card_aut_eq_finrank
  rw [Nat.card_eq_fintype_card, card_automorphisms, finrank_eq_eight]

def galoisEquivElementaryEight :
    (K ≃ₐ[Base] K) ≃* Multiplicative (ZMod 2 × ZMod 2 × ZMod 2) :=
  (MulEquiv.ofBijective signHom
    ((Fintype.bijective_iff_injective_and_card signHom).mpr
      ⟨signHom_injective, by rw [card_automorphisms]; decide⟩)).symm

end
end Z2Z4Rank6.SecondFunctionField
