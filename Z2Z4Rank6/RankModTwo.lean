module

public import Common.Elliptic.RankOne
public import Mathlib.LinearAlgebra.Dimension.Localization
public import Mathlib.LinearAlgebra.Dimension.Torsion.Finite

@[expose] public section

/-!
# Rank bounds from the quotient by doubling

For any finitely generated abelian group containing full two-torsion,
`|G/2G| ≤ 2^(r+2)` implies integral module rank at most r. The finite
part contributes at least four classes, independently of its higher torsion.
-/

namespace Z2Z4Rank6.RankModTwo

open scoped DirectSum

noncomputable section

abbrev DoublingQuotient (G : Type) [AddCommGroup G] :=
  G ⧸ (nsmulAddMonoidHom 2 : G →+ G).range

private theorem finite_rank_zero (T : Type) [AddCommGroup T] [Finite T] :
    Module.rank ℤ T=0 := by
  apply rank_eq_zero_iff.mpr
  intro t
  have ht := isOfFinAddOrder_of_finite t
  refine ⟨(addOrderOf t : ℤ), ?_, ?_⟩
  · exact_mod_cast ht.addOrderOf_pos.ne'
  · simpa only [natCast_zsmul] using addOrderOf_nsmul_eq_zero t

/-- A free finite factor gives exactly the integral rank. -/
theorem rank_eq_of_free_finite (G T : Type) [AddCommGroup G] [AddCommGroup T]
    [Finite T] {n : ℕ} (e : G ≃+ (Fin n →₀ ℤ) × T) :
    Module.rank ℤ G=n := by
  let f : G →+ (Fin n →₀ ℤ) := (AddMonoidHom.fst _ _).comp e.toAddMonoidHom
  have hs : Function.Surjective f := fun v => ⟨e.symm (v,0), by simp [f]⟩
  have hk : Finite f.toIntLinearMap.ker := by
    apply Finite.of_injective (fun x : f.toIntLinearMap.ker => (e x.val).2)
    intro x y hxy
    apply Subtype.ext
    apply e.injective
    apply Prod.ext
    · have hx : (e x.val).1=0 := x.property
      have hy : (e y.val).1=0 := y.property
      exact hx.trans hy.symm
    · exact hxy
  rw [LinearMap.rank_eq_of_surjective (f:=f.toIntLinearMap) hs,
    finite_rank_zero f.toIntLinearMap.ker, add_zero]
  simp

private def coordinateModTwo (n : ℕ) : (Fin n →₀ ℤ) →+ (Fin n → ZMod 2) where
  toFun v := fun i => (v i : ZMod 2)
  map_zero' := by ext; simp
  map_add' x y := by ext; simp

private theorem coordinateModTwo_surjective (n : ℕ) :
    Function.Surjective (coordinateModTwo n) := by
  intro a
  let v : Fin n →₀ ℤ := Finsupp.equivFunOnFinite.symm (fun i => (a i).val)
  exact ⟨v, by ext i; simp [v,coordinateModTwo]⟩

/-- Finite endomorphisms have equally large kernel and cokernel. -/
theorem card_doubling_quotient_eq_kernel (T : Type) [AddCommGroup T] [Finite T] :
    Nat.card (DoublingQuotient T) = Nat.card (nsmulAddMonoidHom 2 : T →+ T).ker := by
  rw [← AddSubgroup.index_eq_card, AddSubgroup.index_range]

private theorem finite_double (G : Type) [AddCommGroup G] [AddGroup.FG G] :
    Finite (DoublingQuotient G) := by
  have hf := AddSubgroup.finiteIndex_range_nsmulAddMonoidHom_of_fg G (by decide : 2≠0)
  exact AddSubgroup.finiteIndex_iff_finite_quotient.mp hf

/-- The quotient of a free-times-finite group has at least the
product of its free mod-two coordinates and the finite doubling quotient. -/
theorem card_doubling_lower (G T : Type) [AddCommGroup G] [AddCommGroup T]
    [AddGroup.FG G] [Finite T] {n : ℕ} (e : G ≃+ (Fin n →₀ ℤ) × T) :
    2^n * Nat.card (DoublingQuotient T) ≤ Nat.card (DoublingQuotient G) := by
  let : Finite (DoublingQuotient G) := finite_double G
  let f : G →+ (Fin n → ZMod 2) × DoublingQuotient T :=
    ((coordinateModTwo n).comp ((AddMonoidHom.fst _ _).comp e.toAddMonoidHom)).prod
      ((QuotientAddGroup.mk' _).comp ((AddMonoidHom.snd _ _).comp e.toAddMonoidHom))
  let q : DoublingQuotient G →+ (Fin n → ZMod 2) × DoublingQuotient T :=
    QuotientAddGroup.lift _ f (by
      rintro _ ⟨x,rfl⟩
      apply Prod.ext
      · ext i
        norm_num [f,coordinateModTwo]
        exact Or.inl (by decide)
      · change (((e (2 • x)).2 : T) : DoublingQuotient T)=0
        rw [map_nsmul,Prod.smul_snd]
        rw [QuotientAddGroup.eq_zero_iff]
        exact ⟨(e x).2,rfl⟩)
  have hs : Function.Surjective q := by
    rintro ⟨a,t⟩
    obtain ⟨v,hv⟩ := coordinateModTwo_surjective n a
    obtain ⟨s,hs⟩ := QuotientAddGroup.mk'_surjective
      (nsmulAddMonoidHom 2 : T →+ T).range t
    refine ⟨(e.symm (v,s) : DoublingQuotient G), ?_⟩
    change f (e.symm (v,s))=(a,t)
    apply Prod.ext
    · simpa [f] using hv
    · simpa [f] using hs
  have hc := Nat.card_le_card_of_surjective q hs
  simpa [Nat.card_prod,Nat.card_eq_fintype_card,ZMod.card] using hc

/-- Full two-torsion embeds in the finite factor of every free-times-finite
presentation, and therefore contributes at least four doubling classes. -/
theorem four_le_card_finite_double (G T : Type) [AddCommGroup G] [AddCommGroup T]
    [Finite T] {n : ℕ} (e : G ≃+ (Fin n →₀ ℤ) × T)
    (j : ZMod 2 × ZMod 2 →+ G) (hj : Function.Injective j) :
    4 ≤ Nat.card (DoublingQuotient T) := by
  have h2 (x : ZMod 2 × ZMod 2) : 2 • x=0 := by
    rw [nsmul_eq_mul, show ((2:ℕ):ZMod 2 × ZMod 2)=0 by decide, zero_mul]
  have hfst (x : ZMod 2 × ZMod 2) : (e (j x)).1=0 := by
    have hzero : 2 • (e (j x)).1=0 := by
      rw [← Prod.smul_fst, ← map_nsmul, ← map_nsmul, h2, map_zero, map_zero]
      rfl
    by_contra he
    apply not_isOfFinAddOrder_of_isAddTorsionFree he
    exact isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨2,by decide,hzero⟩
  let k : ZMod 2 × ZMod 2 → (nsmulAddMonoidHom 2 : T →+ T).ker := fun x =>
    ⟨(e (j x)).2, by
      change 2 • (e (j x)).2=0
      rw [← Prod.smul_snd, ← map_nsmul, ← map_nsmul, h2, map_zero, map_zero]
      rfl⟩
  have hk : Function.Injective k := by
    intro x y hxy
    apply hj
    apply e.injective
    apply Prod.ext
    · exact (hfst x).trans (hfst y).symm
    · exact congrArg Subtype.val hxy
  have hc := Nat.card_le_card_of_injective k hk
  rw [card_doubling_quotient_eq_kernel]
  simpa [Nat.card_eq_fintype_card,ZMod.card] using hc

/-- Finite generation, full rational two-torsion, and an
upper bound on the quotient by doubling imply an integral rank bound. -/
theorem rank_le_of_doubling_card (G : Type) [AddCommGroup G] [AddGroup.FG G]
    (j : ZMod 2 × ZMod 2 →+ G) (hj : Function.Injective j) (r : ℕ)
    (hcard : Nat.card (DoublingQuotient G) ≤ 2^(r+2)) :
    Module.rank ℤ G ≤ r := by
  classical
  obtain ⟨n,ι,hι,p,hp,e,⟨f⟩⟩ := AddCommGroup.equiv_free_prod_directSum_zmod G
  let := hι
  have : ∀ i : ι, NeZero (p i ^ e i) := fun i => ⟨pow_ne_zero _ (hp i).ne_zero⟩
  let T := ⨁ i : ι, ZMod (p i ^ e i)
  have : Finite T := Finite.of_equiv _ DFinsupp.equivFunOnFintype.symm
  have hfour := four_le_card_finite_double G T f j hj
  have hlower := card_doubling_lower G T f
  have hexp : 2^(n+2) ≤ 2^(r+2) := by
    calc
      2^(n+2) = 2^n*4 := by rw [pow_add]; norm_num
      _ ≤ 2^n*Nat.card (DoublingQuotient T) := Nat.mul_le_mul_left _ hfour
      _ ≤ Nat.card (DoublingQuotient G) := hlower
      _ ≤ 2^(r+2) := hcard
  have hn : n ≤ r := by
    have h := (Nat.pow_le_pow_iff_right (by decide : 1< (2:ℕ))).mp hexp
    omega
  rw [rank_eq_of_free_finite G T f]
  exact_mod_cast hn


/-- The exact kernel statement in two-descent identifies the quotient
by doubling with the image of the descent homomorphism. -/
def doublingQuotientEquivRange {G : Type} {H : Type*}
    [AddCommGroup G] [AddCommGroup H] (κ : G →+ H)
    (hker : ∀ P, κ P=0 ↔ ∃ Q, 2 • Q=P) : DoublingQuotient G ≃+ κ.range := by
  have he : (nsmulAddMonoidHom 2 : G →+ G).range = κ.ker := by
    ext P
    change (∃ Q, 2 • Q=P) ↔ κ P=0
    exact (hker P).symm
  exact (QuotientAddGroup.quotientAddEquivOfEq he).trans
    (QuotientAddGroup.quotientKerEquivRange κ)

/-- Image cardinality equals the quotient-by-doubling size. -/
theorem card_doubling_eq_range {G : Type} {H : Type*}
    [AddCommGroup G] [AddCommGroup H] (κ : G →+ H)
    (hker : ∀ P, κ P=0 ↔ ∃ Q, 2 • Q=P) :
    Nat.card (DoublingQuotient G)=Nat.card κ.range :=
  Nat.card_congr (doublingQuotientEquivRange κ hker).toEquiv

/-- a two-descent homomorphism with the proved doubling kernel and
at most `2^(r+2)` image classes gives rank at most r, once finite
generation and full two-torsion are supplied. -/
theorem rank_le_of_descent_image_card {G : Type} {H : Type*}
    [AddCommGroup G] [AddCommGroup H] [AddGroup.FG G]
    (κ : G →+ H) (hker : ∀ P, κ P=0 ↔ ∃ Q, 2 • Q=P)
    (j : ZMod 2 × ZMod 2 →+ G) (hj : Function.Injective j)
    (r : ℕ) (hcard : Nat.card κ.range ≤ 2^(r+2)) : Module.rank ℤ G ≤ r := by
  apply rank_le_of_doubling_card G j hj r
  rw [card_doubling_eq_range κ hker]
  exact hcard

end
end Z2Z4Rank6.RankModTwo
