import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.LinearAlgebra.FreeModule.ModN
import Mathlib.Tactic

/-! # The rank-one consequence of a two-class Kummer image

Finite generation is a standard input. Torsion-freeness and a bound on the
quotient by doubling imply that a nontrivial group is infinite cyclic.
-/

namespace Common.Elliptic

open scoped DirectSum

noncomputable section

private theorem zero_of_finiteOrder {G : Type*} [AddCommGroup G] [IsAddTorsionFree G]
    (P : G) (h : IsOfFinAddOrder P) : P = 0 := by
  by_contra he
  exact not_isOfFinAddOrder_of_isAddTorsionFree he h

theorem exists_free_equiv_of_torsionFree (G : Type*) [AddCommGroup G] [AddGroup.FG G]
    [IsAddTorsionFree G] : ∃ n : ℕ, Nonempty (G ≃+ (Fin n →₀ ℤ)) := by
  classical
  obtain ⟨n, ι, hι, p, hp, e, ⟨f⟩⟩ := AddCommGroup.equiv_free_prod_directSum_zmod G
  let := hι
  have : ∀ i : ι, NeZero (p i ^ e i) := fun i => ⟨pow_ne_zero _ (hp i).ne_zero⟩
  let T := ⨁ i : ι, ZMod (p i ^ e i)
  have : Finite T := Finite.of_equiv _ DFinsupp.equivFunOnFintype.symm
  let j : T →+ G := f.symm.toAddMonoidHom.comp (AddMonoidHom.inr (Fin n →₀ ℤ) T)
  have hz : ∀ t : T, t = 0 := by
    intro t
    have ht := isOfFinAddOrder_of_finite t
    have hj : IsOfFinAddOrder (j t) := isOfFinAddOrder_iff_nsmul_eq_zero.mpr
      ⟨addOrderOf t, ht.addOrderOf_pos, by rw [← map_nsmul, addOrderOf_nsmul_eq_zero, map_zero]⟩
    have hg := zero_of_finiteOrder (j t) hj
    have he := congrArg (fun g => (f g).2) hg
    simpa [j] using he
  have hT : Subsingleton T := ⟨fun x y => by rw [hz x, hz y]⟩
  let fstMap : G →+ (Fin n →₀ ℤ) :=
    (AddMonoidHom.fst (Fin n →₀ ℤ) T).comp f.toAddMonoidHom
  have hinj : Function.Injective fstMap := by
    intro x y hxy
    apply f.injective
    exact Prod.ext hxy (Subsingleton.elim _ _)
  have hsurj : Function.Surjective fstMap := by
    intro v
    exact ⟨f.symm (v, 0), by simp [fstMap]⟩
  exact ⟨n, ⟨AddEquiv.ofBijective fstMap ⟨hinj, hsurj⟩⟩⟩

abbrev DoublingQuotient (G : Type*) [AddCommGroup G] :=
  G ⧸ (nsmulAddMonoidHom 2 : G →+ G).range

private def coordinateModTwo (n : ℕ) : (Fin n →₀ ℤ) →+ (Fin n → ZMod 2) where
  toFun v := fun i => (v i : ZMod 2)
  map_zero' := by ext; simp
  map_add' x y := by ext; simp

private theorem coordinateModTwo_surjective (n : ℕ) :
    Function.Surjective (coordinateModTwo n) := by
  intro a
  let v : Fin n →₀ ℤ := Finsupp.equivFunOnFinite.symm (fun i => (a i).val)
  refine ⟨v, ?_⟩
  ext i
  simp [v, coordinateModTwo]

theorem free_dimension_le_one_of_doubling_card (G : Type*) [AddCommGroup G]
    [Finite (DoublingQuotient G)] (hcard : Nat.card (DoublingQuotient G) ≤ 2)
    {n : ℕ} (e : G ≃+ (Fin n →₀ ℤ)) : n ≤ 1 := by
  let f := (coordinateModTwo n).comp e.toAddMonoidHom
  let q : DoublingQuotient G →+ (Fin n → ZMod 2) :=
    QuotientAddGroup.lift _ f (by
      rintro _ ⟨x, rfl⟩
      ext i
      norm_num [f, coordinateModTwo]
      exact Or.inl (by decide))
  have hs : Function.Surjective q := by
    intro a
    obtain ⟨v, hv⟩ := coordinateModTwo_surjective n a
    refine ⟨(e.symm v : DoublingQuotient G), ?_⟩
    simpa [q, f] using hv
  have hn : 2 ^ n ≤ 2 := by
    calc
      2 ^ n = Nat.card (Fin n → ZMod 2) := by simp [Nat.card_eq_fintype_card, ZMod.card]
      _ ≤ Nat.card (DoublingQuotient G) := Nat.card_le_card_of_surjective q hs
      _ ≤ 2 := hcard
  by_contra h
  have h2 : 2 ≤ n := by omega
  have hp := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) h2
  norm_num at hp
  omega

/-- The group conclusion used by Proposition 9.2, after its own Kummer arithmetic. -/
theorem nonempty_equiv_int_of_doubling_card (G : Type*) [AddCommGroup G] [AddGroup.FG G]
    [IsAddTorsionFree G] [Nontrivial G] [Finite (DoublingQuotient G)]
    (hcard : Nat.card (DoublingQuotient G) ≤ 2) : Nonempty (G ≃+ ℤ) := by
  obtain ⟨n, ⟨e⟩⟩ := exists_free_equiv_of_torsionFree G
  have hn := free_dimension_le_one_of_doubling_card G hcard e
  have hn0 : n ≠ 0 := by
    intro he
    subst n
    have : Subsingleton G := e.toEquiv.subsingleton
    exact not_subsingleton G this
  have hn1 : n = 1 := by omega
  subst n
  let oneCoordinate : (Fin 1 →₀ ℤ) ≃+ ℤ :=
    { toFun := fun v => v 0
      invFun := fun z => Finsupp.single 0 z
      left_inv := by intro v; apply Finsupp.ext; intro i; fin_cases i; simp
      right_inv := by intro z; simp
      map_add' := by intro x y; rfl }
  exact ⟨e.trans oneCoordinate⟩

end

end Common.Elliptic
