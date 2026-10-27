import Z2Z4Rank6.GFunctionFieldCopy
import Z2Z4Rank6.GFunctionFieldLocal
import Z2Z4Rank6.GBaseFunctionFieldCoordinates
import Z2Z4Rank6.LaurentConstantSquares
import Mathlib.FieldTheory.AlgebraicClosure

/-! Explicit JG cubic coordinates generate the G quartic field.
Source: Jaswal Proposition 7.2(a), DOI 10.5281/zenodo.23437117. -/
namespace Z2Z4Rank6.GBaseFunctionFieldIso
noncomputable section
abbrev K := GFunctionFieldCopy.K
abbrev m : K := GFunctionFieldCopy.m
abbrev eta : K := GFunctionFieldCopy.eta

private theorem gM_mem {L : Type*} [Field L] [Algebra ℚ L]
    (S : IntermediateField ℚ L) (x y : L) (hx : x∈S) (hy : y∈S) : gQuarticM x y∈S := by
  let xs : S := ⟨x,hx⟩
  let ys : S := ⟨y,hy⟩
  exact (map_gQuarticM S.toSubfield.subtype xs ys) ▸ (gQuarticM xs ys).property
private theorem gEta_mem {L : Type*} [Field L] [Algebra ℚ L]
    (S : IntermediateField ℚ L) (x y : L) (hx : x∈S) (hy : y∈S) : gQuarticEta x y∈S := by
  let xs : S := ⟨x,hx⟩
  let ys : S := ⟨y,hy⟩
  exact (map_gQuarticEta S.toSubfield.subtype xs ys) ▸ (gQuarticEta xs ys).property

theorem quartic_equation : eta^2=gQuartic m := GFunctionFieldCopy.eta_sq

theorem m_sub_base_ne_zero : m-57≠0 := by
  intro h
  apply GFunctionFieldCopy.m_transcendental
  change IsAlgebraic ℚ m
  rw [sub_eq_zero.mp h]
  exact isAlgebraic_natCast 57

theorem leading_nonsquare : ¬IsSquare (gQuarticA:K) := by
  change ¬IsSquare (99:K)
  simpa only [Rat.cast_ofNat] using
    (not_isSquare_ratCast_of_laurent_embedding
      (GFunctionFieldLocal.embedding.comp GFunctionFieldCopy.equiv.toRingHom)
      (99:ℚ) (by norm_num))

theorem forward_den_ne_zero : pointedInverseDen gQuarticA gQuarticQ
    (pointedForwardX gQuarticD gQuarticQ (m-57) eta)≠0 :=
  pointed_inverse_den_ne_zero _ _ _ gQuartic_q_ne_zero leading_nonsquare

@[irreducible] def x : K := gQuarticRecoverX m eta
@[irreducible] def y : K := gQuarticRecoverY m eta
theorem x_formula : gQuarticRecoverX m eta=x := by unfold x; rfl
theorem y_formula : gQuarticRecoverY m eta=y := by unfold y; rfl

theorem equation_factor : y^2=(x+5734)*(x-1666)*(x-4067) := by
  have he := gQuartic_forward_equation m eta m_sub_base_ne_zero quartic_equation
  rw [x_formula,y_formula] at he
  exact he

theorem equation : y^2=x^3+x^2-26097400*x+38851416548 := by
  rw [equation_factor,gJacobian_cubic_factor]

theorem m_recover : gQuarticM x y=m := by
  have he := gQuartic_forward_inverse_M m eta forward_den_ne_zero
  rw [x_formula,y_formula] at he
  exact he

theorem eta_recover : gQuarticEta x y=eta := by
  have he := gQuartic_forward_inverse_Eta m eta m_sub_base_ne_zero forward_den_ne_zero
  rw [x_formula,y_formula] at he
  exact he

theorem x_transcendental : Transcendental ℚ x := by
  intro hx
  have hy2 : IsAlgebraic ℚ (y^2) := by
    rw [equation_factor]
    exact ((hx.add (isAlgebraic_natCast 5734)).mul
      (hx.sub (isAlgebraic_natCast 1666))).mul (hx.sub (isAlgebraic_natCast 4067))
  have hy : IsAlgebraic ℚ y := hy2.of_pow (by decide : 0<(2:ℕ))
  let S := algebraicClosure ℚ K
  have hxS : x∈S := mem_algebraicClosure_iff.mpr hx
  have hyS : y∈S := mem_algebraicClosure_iff.mpr hy
  have hmS := gM_mem S x y hxS hyS
  rw [m_recover] at hmS
  exact GFunctionFieldCopy.m_transcendental (mem_algebraicClosure_iff.mp hmS)

theorem field_adjoin_coordinates_eq_top : IntermediateField.adjoin ℚ ({x,y}:Set K)=⊤ := by
  let S := IntermediateField.adjoin ℚ ({x,y}:Set K)
  have hxS : x∈S := IntermediateField.subset_adjoin _ _ (by simp)
  have hyS : y∈S := IntermediateField.subset_adjoin _ _ (by simp)
  have hmS := gM_mem S x y hxS hyS
  have heS := gEta_mem S x y hxS hyS
  rw [m_recover] at hmS
  rw [eta_recover] at heS
  have hle : IntermediateField.adjoin ℚ ({m,eta}:Set K)≤S := by
    apply IntermediateField.adjoin_le_iff.mpr
    intro z hz
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hz
    rcases hz with rfl|rfl
    · exact hmS
    · exact heS
  rw [GFunctionFieldCopy.field_adjoin_coordinates_eq_top] at hle
  exact top_unique hle
end
end Z2Z4Rank6.GBaseFunctionFieldIso
