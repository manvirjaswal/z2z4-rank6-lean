module

public import Z2Z4Rank6.TwoDescent
public import Mathlib.FieldTheory.Finiteness

@[expose] public section

/-! Generic F₂ subspaces coming from additive descent images.
An additive subgroup of an F₂ vector space is closed under its two scalars. -/
namespace Z2Z4Rank6.SelmerClassSpace
noncomputable section

variable {G V : Type*} [AddCommGroup G] [AddCommGroup V] [Module (ZMod 2) V]

/-- The image of an additive map into an F₂ module, as an F₂ submodule. -/
def rangeSpace (κ : G→+V) : Submodule (ZMod 2) V where
  carrier := κ.range
  zero_mem' := κ.range.zero_mem
  add_mem' := κ.range.add_mem
  smul_mem' c x hx := by
    have hc : c=0 ∨ c=1 := (by decide +kernel : ∀c : ZMod 2,c=0 ∨ c=1) c
    rcases hc with hc | hc
    · rw [hc,zero_smul]
      exact κ.range.zero_mem
    · rw [hc,one_smul]
      exact hx

/-- Equality with an image proves that the class set is a subspace. -/
theorem coe_span_eq_of_range (S : Set V) (κ : G→+V)
    (hS : S=(κ.range : Set V)) :
    (Submodule.span (ZMod 2) S : Set V)=S := by
  rw [hS]
  change (Submodule.span (ZMod 2) (rangeSpace κ : Set V) : Set V)=(rangeSpace κ : Set V)
  rw [Submodule.span_eq]

/-- A finite class set equal to a descent image and of size 2^n has
an F₂ span of dimension n. -/
theorem finrank_span_eq_of_range (S : Set V) (κ : G→+V)
    (hS : S=(κ.range : Set V)) (hfinite : S.Finite) (n : ℕ) (hcard : S.ncard=2^n) :
    Module.finrank (ZMod 2) (Submodule.span (ZMod 2) S)=n := by
  have hclosed := coe_span_eq_of_range S κ hS
  have hf : (Submodule.span (ZMod 2) S : Set V).Finite := by
    rw [hclosed]
    exact hfinite
  let : Fintype (Submodule.span (ZMod 2) S) := hf.fintype
  have hc : Fintype.card (Submodule.span (ZMod 2) S)=2^n := by
    rw [←Nat.card_eq_fintype_card]
    change (Submodule.span (ZMod 2) S : Set V).ncard=2^n
    rw [hclosed]
    exact hcard
  have hp : 2^Module.finrank (ZMod 2) (Submodule.span (ZMod 2) S)=2^n := by
    have he := Module.card_eq_pow_finrank (K:=ZMod 2)
      (V:=Submodule.span (ZMod 2) S)
    rw [ZMod.card] at he
    exact he.symm.trans hc
  exact le_antisymm
    ((Nat.pow_le_pow_iff_right (by decide : 1<(2:ℕ))).mp hp.le)
    ((Nat.pow_le_pow_iff_right (by decide : 1<(2:ℕ))).mp hp.ge)

end
end Z2Z4Rank6.SelmerClassSpace
