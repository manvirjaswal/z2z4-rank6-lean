module

public import Z2Z4Rank6.GFunctionField
public import Z2Z4Rank6.QuadraticFieldLift

@[expose] public section

/-! An explicit coherent type copy of the existing quadratic G field. Its
opaque Field instance keeps generic coordinate identities from expanding the
quadratic-algebra representation during operator-instance conversion. -/
namespace Z2Z4Rank6.GFunctionFieldCopy
noncomputable section
@[irreducible] def K : Type := GFunctionField.K
@[irreducible] instance gFunctionFieldCopyField : Field K := by unfold K; infer_instance
instance gFunctionFieldCopyCharZero : CharZero K := by unfold K gFunctionFieldCopyField; infer_instance

def ringEquiv : K ≃+* GFunctionField.K := by unfold K gFunctionFieldCopyField; exact RingEquiv.refl _
def equiv : K ≃ₐ[ℚ] GFunctionField.K where
  __ := ringEquiv
  commutes' := ringEquiv.toRingHom.map_rat_algebraMap

@[irreducible] def m : K := equiv.symm GFunctionField.m
@[irreducible] def eta : K := equiv.symm GFunctionField.eta
@[simp] theorem equiv_m : equiv m=GFunctionField.m := by unfold m; exact equiv.apply_symm_apply _
@[simp] theorem equiv_eta : equiv eta=GFunctionField.eta := by unfold eta; exact equiv.apply_symm_apply _

theorem map_h {R S : Type*} [CommRing R] [CommRing S] (f : R→+*S) (t : R) :
    f (GFunctionField.h t)=GFunctionField.h (f t) := by simp [GFunctionField.h,map_ofNat]

theorem eta_sq : eta^2=GFunctionField.h m := by
  apply equiv.injective
  rw [map_pow,equiv_eta]
  have hh := map_h equiv.toRingHom m
  change equiv (GFunctionField.h m)=GFunctionField.h (equiv m) at hh
  rw [hh,equiv_m]
  exact GFunctionField.eta_sq

theorem m_transcendental : Transcendental ℚ m := by
  intro h
  apply GFunctionField.m_transcendental
  have he := h.algHom equiv.toAlgHom
  change IsAlgebraic ℚ (equiv m) at he
  rwa [equiv_m] at he

theorem field_adjoin_coordinates_eq_top : IntermediateField.adjoin ℚ ({m,eta}:Set K)=⊤ := by
  let S := IntermediateField.adjoin ℚ ({m,eta}:Set K)
  have hle : IntermediateField.adjoin ℚ
      ({GFunctionField.m,GFunctionField.eta}:Set GFunctionField.K)≤S.comap equiv.symm.toAlgHom := by
    apply IntermediateField.adjoin_le_iff.mpr
    intro z hz
    change equiv.symm z∈S
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hz
    rcases hz with rfl|rfl
    · have hc : equiv.symm GFunctionField.m=m := by unfold m; rfl
      rw [hc]
      exact IntermediateField.subset_adjoin _ _ (by simp)
    · have hc : equiv.symm GFunctionField.eta=eta := by unfold eta; rfl
      rw [hc]
      exact IntermediateField.subset_adjoin _ _ (by simp)
  rw [GFunctionField.field_adjoin_coordinates_eq_top] at hle
  apply top_unique
  intro z _
  have hz := hle (show equiv z∈(⊤:IntermediateField ℚ GFunctionField.K) from Set.mem_univ _)
  change equiv.symm (equiv z)∈S at hz
  simpa only [AlgEquiv.symm_apply_apply] using hz
end
end Z2Z4Rank6.GFunctionFieldCopy
