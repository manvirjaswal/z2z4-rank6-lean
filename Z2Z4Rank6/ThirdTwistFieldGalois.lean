import Z2Z4Rank6.ThirdTwistFieldAutomorphisms
import Z2Z4Rank6.ThirdTwistFieldCoordinates
import Mathlib.FieldTheory.Galois.Basic

/-! The degree-eight Galois group of the third-twist base. -/
namespace Z2Z4Rank6.ThirdTwistField
noncomputable section

private theorem zero_of_neg_eq {F : Type*} [Field F] [CharZero F] {z : F}
    (h : -z=z) : z=0 := by
  have h2 : (2 : F)*z=0 := by linear_combination -h
  exact (mul_eq_zero.mp h2).resolve_left (by norm_num)

theorem u_ne_zero : u ≠ 0 :=
  (map_ne_zero (algebraMap FunctionField.K K)).mpr FunctionField.u_ne_zero

theorem v_ne_zero : v ≠ 0 :=
  (map_ne_zero (algebraMap FunctionField.K K)).mpr FunctionField.v_ne_zero

theorem w_ne_zero : w ≠ 0 := by
  intro hw
  have hr : w^2=algebraMap FunctionField.K K d3Old := by
    rw [w,sq,QuadraticAlgebra.omega_mul_omega_eq_algebraMap]
    simp only [map_zero,zero_mul,add_zero]
  have hz : algebraMap FunctionField.K K d3Old=0 := by
    rw [←hr,hw,zero_pow (by decide : 2≠0)]
  have hd : d3Old=0 := (algebraMap FunctionField.K K).injective
    (hz.trans (map_zero (algebraMap FunctionField.K K)).symm)
  apply d3Old_not_isSquare
  rw [hd]
  exact IsSquare.zero

instance finiteDimensional_full : FiniteDimensional Base K := Module.Finite.of_basis basis

def signAut (t : ZMod 2 × ZMod 2 × ZMod 2) : K ≃ₐ[Base] K :=
  (if t.1 = 0 then 1 else sigmaU) *
    ((if t.2.1 = 0 then 1 else sigmaV) * (if t.2.2 = 0 then 1 else sigmaW))

private theorem signAut000 : signAut (0,0,0) = 1 := by simp [signAut]
private theorem signAut100 : signAut (1,0,0) = sigmaU := by simp [signAut]
private theorem signAut010 : signAut (0,1,0) = sigmaV := by simp [signAut]
private theorem signAut001 : signAut (0,0,1) = sigmaW := by simp [signAut]
private theorem signAut110 : signAut (1,1,0) = sigmaU*sigmaV := by simp [signAut]
private theorem signAut101 : signAut (1,0,1) = sigmaU*sigmaW := by simp [signAut]
private theorem signAut011 : signAut (0,1,1) = sigmaV*sigmaW := by simp [signAut]
private theorem signAut111 : signAut (1,1,1) = sigmaU*(sigmaV*sigmaW) := by simp [signAut]

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
      simp only [AlgEquiv.mul_apply, AlgEquiv.one_apply, 
        sigmaU_involutive, sigmaV_involutive,
        sigmaW_involutive, sigmaU_sigmaV_commute, sigmaU_sigmaW_commute, sigmaV_sigmaW_commute]

theorem signAut_u (t : ZMod 2 × ZMod 2 × ZMod 2) :
    signAut t u = if t.1 = 0 then u else -u := by
  have hs : star u = u := sigmaW_u
  rcases t with ⟨a,b,c⟩
  by_cases ha : a=0 <;> by_cases hb : b=0 <;> by_cases hc : c=0 <;>
    simp [signAut, ha, hb, hc, AlgEquiv.mul_apply, hs]

theorem signAut_v (t : ZMod 2 × ZMod 2 × ZMod 2) :
    signAut t v = if t.2.1 = 0 then v else -v := by
  have hs : star v = v := sigmaW_v
  rcases t with ⟨a,b,c⟩
  by_cases ha : a=0 <;> by_cases hb : b=0 <;> by_cases hc : c=0 <;>
    simp [signAut, ha, hb, hc, AlgEquiv.mul_apply, hs]

theorem signAut_w (t : ZMod 2 × ZMod 2 × ZMod 2) :
    signAut t w = if t.2.2 = 0 then w else -w := by
  have hs : star w = -w := sigmaW_w
  rcases t with ⟨a,b,c⟩
  by_cases ha : a=0 <;> by_cases hb : b=0 <;> by_cases hc : c=0 <;>
    simp [signAut, ha, hb, hc, AlgEquiv.mul_apply, hs]

theorem signHom_injective : Function.Injective signHom := by
  intro g h he
  rcases g with ⟨a,b,c⟩
  rcases h with ⟨d,e,f⟩
  change signAut (a,b,c) = signAut (d,e,f) at he
  change (a,b,c) = (d,e,f)
  have h1 := congrArg (fun g : K ≃ₐ[Base] K => g u) he
  have h2 := congrArg (fun u : K ≃ₐ[Base] K => u v) he
  have h3 := congrArg (fun u : K ≃ₐ[Base] K => u w) he
  rw [signAut_u, signAut_u] at h1
  rw [signAut_v, signAut_v] at h2
  rw [signAut_w, signAut_w] at h3
  have hne1 : -u ≠ u := fun h => u_ne_zero (zero_of_neg_eq h)
  have hne2 : -v ≠ v := fun h => v_ne_zero (zero_of_neg_eq h)
  have hne3 : -w ≠ w := fun h => w_ne_zero (zero_of_neg_eq h)
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
end Z2Z4Rank6.ThirdTwistField
