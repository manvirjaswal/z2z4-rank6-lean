import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.Torsion
import Mathlib.GroupTheory.Coset.Card
import Mathlib.Tactic

/-!
# Finite abelian group certificates

Two torsion points, an explicit kernel certificate and the cardinality
of the group give an additive equivalence with a product of two cyclic
groups. The three-primary subgroup of Z/36 × Z/2 is cyclic, as proved by
injecting it into the first cyclic factor.
-/
namespace Common.FiniteAbelianCertificates
noncomputable section
variable {G : Type*} [AddCommGroup G]

def integerOrbit (P : G) : ℤ →+ G where
  toFun k := k • P
  map_zero' := zero_zsmul P
  map_add' k l := by simp only [add_zsmul]

def cyclicHom (m : ℕ) (P : G) (hP : m • P=0) : ZMod m →+ G :=
  ZMod.lift m ⟨integerOrbit P,by
    change (m : ℤ) • P=0
    simpa only [natCast_zsmul] using hP⟩

@[simp] theorem cyclicHom_natCast (m : ℕ) (P : G) (hP : m • P=0) (k : ℕ) :
    cyclicHom m P hP (k : ZMod m)=k • P := by
  unfold cyclicHom
  rw [←Int.cast_natCast k,ZMod.lift_coe]
  simp only [integerOrbit,natCast_zsmul,AddMonoidHom.coe_mk,ZeroHom.coe_mk]

theorem cyclicHom_val (m : ℕ) [NeZero m] (P : G) (hP : m • P=0) (z : ZMod m) :
    cyclicHom m P hP z=z.val • P := by
  conv_lhs => rw [←ZMod.natCast_zmod_val z]
  exact cyclicHom_natCast m P hP z.val

def productHom (m n : ℕ) (P Q : G) (hP : m • P=0) (hQ : n • Q=0) :
    (ZMod m × ZMod n) →+ G :=
  (cyclicHom m P hP).coprod (cyclicHom n Q hQ)

theorem productHom_injective (m n : ℕ) [NeZero m] [NeZero n]
    (P Q : G) (hP : m • P=0) (hQ : n • Q=0)
    (hker : ∀ a : Fin m, ∀ b : Fin n,
      a.val • P+b.val • Q=0 → a.val=0 ∧ b.val=0) :
    Function.Injective (productHom m n P Q hP hQ) := by
  apply (injective_iff_map_eq_zero _).mpr
  rintro ⟨u,v⟩ h
  change cyclicHom m P hP u+cyclicHom n Q hQ v=0 at h
  rw [cyclicHom_val,cyclicHom_val] at h
  obtain ⟨hu,hv⟩ := hker ⟨u.val,ZMod.val_lt u⟩ ⟨v.val,ZMod.val_lt v⟩ h
  exact Prod.ext ((ZMod.val_eq_zero u).mp hu) ((ZMod.val_eq_zero v).mp hv)

/-- A finite additive equivalence from the certified generators. -/
def productEquiv (m n : ℕ) [NeZero m] [NeZero n]
    (P Q : G) (hP : m • P=0) (hQ : n • Q=0)
    (hker : ∀ a : Fin m, ∀ b : Fin n,
      a.val • P+b.val • Q=0 → a.val=0 ∧ b.val=0)
    (hcard : Nat.card G=m*n) : (ZMod m × ZMod n) ≃+ G := by
  letI : Finite G := Nat.finite_of_card_ne_zero (by
    rw [hcard]
    exact mul_ne_zero (NeZero.ne m) (NeZero.ne n))
  exact AddEquiv.ofBijective (productHom m n P Q hP hQ)
    ((Nat.bijective_iff_injective_and_card _).mpr
      ⟨productHom_injective m n P Q hP hQ hker,by simp [hcard]⟩)

theorem three_primary_snd_zero (e : G ≃+ (ZMod 36 × ZMod 2))
    (g : AddCommGroup.primaryComponent G 3) : (e g.val).2=0 := by
  obtain ⟨k,hk⟩ := g.property
  have h := congrArg (fun x : G=>(e x).2) hk
  have hh : (3^k : ℕ) • (e g.val).2=0 := by
    rw [map_nsmul,map_zero] at h
    exact h
  have hm : (3^k : ℕ) • (e g.val).2=(e g.val).2 := by
    rw [nsmul_eq_mul,Nat.cast_pow]
    norm_num only [Nat.cast_ofNat]
    rw [show (3 : ZMod 2)=1 by decide +kernel,one_pow,one_mul]
  rwa [hm] at hh

/-- The three-primary subgroup is cyclic. -/
theorem three_primary_cyclic (e : G ≃+ (ZMod 36 × ZMod 2)) :
    IsAddCyclic (AddCommGroup.primaryComponent G 3) := by
  let f : AddCommGroup.primaryComponent G 3 →+ ZMod 36 :=
    (AddMonoidHom.fst (ZMod 36) (ZMod 2)).comp
      (e.toAddMonoidHom.comp (AddCommGroup.primaryComponent G 3).subtype)
  apply isAddCyclic_of_injective f
  intro x y h
  apply Subtype.ext
  apply e.injective
  apply Prod.ext
  · exact h
  · rw [three_primary_snd_zero e x,three_primary_snd_zero e y]

/-- If nine does not divide the order of a finite abelian group, its
three-primary subgroup has order dividing three and is cyclic. -/
theorem three_primary_cyclic_of_nine_not_dvd [Finite G] (hno : ¬9 ∣ Nat.card G) :
    IsAddCyclic (AddCommGroup.primaryComponent G 3) := by
  let S := AddCommGroup.primaryComponent G 3
  have hp : IsPGroup 3 (Multiplicative S) := by
    intro g
    obtain ⟨k,hk⟩ := (Multiplicative.toAdd g).property
    refine ⟨k,?_⟩
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    exact hk
  obtain ⟨k,hk⟩ := hp.exists_card_eq
  rw [Nat.card_congr Multiplicative.toAdd] at hk
  have hd : Nat.card S ∣ Nat.card G := AddSubgroup.card_dvd_of_injective S.subtype Subtype.val_injective
  rw [hk] at hd
  have hkle : k≤1 := by
    by_contra h
    have htwo : 2≤k := by omega
    apply hno
    have hpow : (3 : ℕ)^2 ∣ 3^k := pow_dvd_pow 3 htwo
    exact hpow.trans hd
  apply isAddCyclic_of_card_dvd_prime (p:=3)
  change Nat.card S ∣ 3
  rw [hk]
  interval_cases k <;> norm_num

end
end Common.FiniteAbelianCertificates
