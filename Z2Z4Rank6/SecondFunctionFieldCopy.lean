module

public import Z2Z4Rank6.SecondFunctionField
public import Z2Z4Rank6.QuadraticFieldLift

@[expose] public section

/-! A type copy with one field instance, explicitly equivalent to the
three-step quadratic field. This avoids exponential operator-instance
conversion while applying generic rational identities. -/
namespace Z2Z4Rank6.SecondFunctionFieldCopy
noncomputable section
@[irreducible] def K : Type := SecondFunctionField.K
@[irreducible] instance secondFunctionFieldCopyField : Field K := by unfold K; infer_instance
instance secondFunctionFieldCopyCharZero : CharZero K := by unfold K secondFunctionFieldCopyField; infer_instance

def ringEquiv : K ≃+* SecondFunctionField.K := by unfold K secondFunctionFieldCopyField; exact RingEquiv.refl _
def equiv : K ≃ₐ[ℚ] SecondFunctionField.K where
  __ := ringEquiv
  commutes' := ringEquiv.toRingHom.map_rat_algebraMap

@[irreducible] def W : K := equiv.symm SecondFunctionField.W
@[irreducible] def s1 : K := equiv.symm SecondFunctionField.s1
@[irreducible] def s2 : K := equiv.symm SecondFunctionField.s2
@[irreducible] def s3 : K := equiv.symm SecondFunctionField.s3

@[simp] theorem equiv_W : equiv W=SecondFunctionField.W := by unfold W; exact equiv.apply_symm_apply _
@[simp] theorem equiv_s1 : equiv s1=SecondFunctionField.s1 := by unfold s1; exact equiv.apply_symm_apply _
@[simp] theorem equiv_s2 : equiv s2=SecondFunctionField.s2 := by unfold s2; exact equiv.apply_symm_apply _
@[simp] theorem equiv_s3 : equiv s3=SecondFunctionField.s3 := by unfold s3; exact equiv.apply_symm_apply _

theorem s1_sq : s1^2=W := by
  apply equiv.injective
  rw [map_pow,equiv_s1,equiv_W]
  exact SecondFunctionField.s1_sq

theorem s2_sq : s2^2=SecondFamily.qA W := by
  apply equiv.injective
  rw [map_pow,equiv_s2]
  have hb := SecondFunctionField.map_beta equiv.toRingHom
  change equiv (SecondFamily.beta:K)=(SecondFamily.beta:SecondFunctionField.K) at hb
  rw [SecondFamily.qA,map_mul,map_sub,map_ofNat,hb,equiv_W]
  exact SecondFunctionField.s2_sq

private theorem map_qB {F L : Type*} [Field F] [Field L] (f : F→+*L) (z : F) :
    f (SecondFamily.qB z)=SecondFamily.qB (f z) := by
  simp [SecondFamily.qB,SecondFamily.beta,SecondFamily.gamma,map_ofNat]

theorem s3_sq : s3^2=SecondFamily.qB W := by
  unfold s3 W
  have hp := map_pow equiv.symm.toRingHom SecondFunctionField.s3 2
  change equiv.symm (SecondFunctionField.s3^2)=(equiv.symm SecondFunctionField.s3)^2 at hp
  have hq := map_qB equiv.symm.toRingHom SecondFunctionField.W
  change equiv.symm (SecondFamily.qB SecondFunctionField.W)=
    SecondFamily.qB (equiv.symm SecondFunctionField.W) at hq
  exact hp.symm.trans ((congrArg equiv.symm SecondFunctionField.s3_sq).trans hq)

theorem W_transcendental : Transcendental ℚ W := by
  intro h
  apply SecondFunctionField.W_transcendental
  have he := h.algHom equiv.toAlgHom
  change IsAlgebraic ℚ (equiv W) at he
  rwa [equiv_W] at he

theorem field_adjoin_coordinates_eq_top : IntermediateField.adjoin ℚ
    ({W,s1,s2,s3}:Set K)=⊤ := by
  let S := IntermediateField.adjoin ℚ ({W,s1,s2,s3}:Set K)
  have hle : IntermediateField.adjoin ℚ
      ({SecondFunctionField.W,SecondFunctionField.s1,SecondFunctionField.s2,
        SecondFunctionField.s3}:Set SecondFunctionField.K)≤S.comap equiv.symm.toAlgHom := by
    apply IntermediateField.adjoin_le_iff.mpr
    intro z hz
    change equiv.symm z∈S
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hz
    rcases hz with rfl|rfl|rfl|rfl
    · have hc : equiv.symm SecondFunctionField.W=W := by unfold W; rfl
      rw [hc]
      exact IntermediateField.subset_adjoin _ _ (by simp)
    · have hc : equiv.symm SecondFunctionField.s1=s1 := by unfold s1; rfl
      rw [hc]
      exact IntermediateField.subset_adjoin _ _ (by simp)
    · have hc : equiv.symm SecondFunctionField.s2=s2 := by unfold s2; rfl
      rw [hc]
      exact IntermediateField.subset_adjoin _ _ (by simp)
    · have hc : equiv.symm SecondFunctionField.s3=s3 := by unfold s3; rfl
      rw [hc]
      exact IntermediateField.subset_adjoin _ _ (by simp)
  rw [SecondFunctionField.field_adjoin_coordinates_eq_top] at hle
  apply top_unique
  intro z _
  have hz := hle (show equiv z∈(⊤:IntermediateField ℚ SecondFunctionField.K) from Set.mem_univ _)
  change equiv.symm (equiv z)∈S at hz
  simpa only [AlgEquiv.symm_apply_apply] using hz
end
end Z2Z4Rank6.SecondFunctionFieldCopy
