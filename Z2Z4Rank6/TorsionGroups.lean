import Z2Z4Rank6.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.Coset.Card
import Mathlib.Tactic

/-!
# The group-theoretic step in the torsion criterion

The inclusion and finite-group elimination used in Lemma 6.1 of Manvir Jaswal,
"Infinitely many elliptic curves with torsion Z/2Z × Z/4Z and rank at least six",
DOI: 10.5281/zenodo.23437117. The classification is Mazur,
"Modular curves and the Eisenstein ideal", Publ. Math. IHÉS 47 (1977),
Theorem (8), p. 35 (equivalently III, Theorem 5.1).
-/

namespace Z2Z4Rank6

private def integerOrbit {G : Type*} [AddCommGroup G] (P : G) : ℤ →+ G where
  toFun n := n • P
  map_zero' := zero_zsmul P
  map_add' n m := by simp only [add_zsmul]

private def pointHom {G : Type*} [AddCommGroup G] (n : ℕ) (P : G) (hn : n • P = 0) :
    ZMod n →+ G :=
  ZMod.lift n ⟨integerOrbit P, by change (n : ℤ) • P = 0; simpa only [natCast_zsmul] using hn⟩

@[simp] private theorem pointHom_natCast {G : Type*} [AddCommGroup G]
    (n : ℕ) (P : G) (hn : n • P = 0) (k : ℕ) :
    pointHom n P hn (k : ZMod n) = k • P := by
  unfold pointHom
  rw [← Int.cast_natCast k]
  rw [ZMod.lift_coe]
  simp only [integerOrbit, natCast_zsmul, AddMonoidHom.coe_mk, ZeroHom.coe_mk]

private theorem pointHom_val {G : Type*} [AddCommGroup G]
    (n : ℕ) [NeZero n] (P : G) (hn : n • P = 0) (z : ZMod n) :
    pointHom n P hn z = z.val • P := by
  conv_lhs => rw [← ZMod.natCast_zmod_val z]
  exact pointHom_natCast n P hn z.val

theorem two_four_injective {G : Type*} [AddCommGroup G] (T Q : G)
    (hT : 2 • T = 0) (hQ : 4 • Q = 0) (hT0 : T ≠ 0) (hQ2 : 2 • Q ≠ 0)
    (hne : T ≠ 2 • Q) :
    ∃ f : (ZMod 2 × ZMod 4) →+ G, Function.Injective f := by
  let f := (pointHom 2 T hT).coprod (pointHom 4 Q hQ)
  refine ⟨f, (injective_iff_map_eq_zero f).mpr ?_⟩
  rintro ⟨u, v⟩ hker
  change pointHom 2 T hT u + pointHom 4 Q hQ v = 0 at hker
  rw [pointHom_val, pointHom_val] at hker
  have hu := ZMod.val_lt u
  have hv := ZMod.val_lt v
  interval_cases huval : u.val <;> interval_cases hvval : v.val
  all_goals simp only [zero_nsmul, one_nsmul, zero_add, add_zero] at hker
  all_goals try contradiction
  · exact Prod.ext (ZMod.val_eq_zero u |>.mp huval) (ZMod.val_eq_zero v |>.mp hvval)
  · exfalso
    apply hQ2
    simp only [hker, smul_zero]
  · exfalso
    apply hQ2
    have heq : Q = 4 • Q - 3 • Q := by abel
    have hzero : Q = 0 := by rw [heq, hQ, hker]; simp
    simp only [hzero, smul_zero]
  · exfalso
    apply hQ2
    have ht : T = -Q := eq_neg_of_add_eq_zero_left hker
    rw [ht] at hT
    simpa only [smul_neg, neg_eq_zero] using hT
  · exfalso
    apply hne
    have hnq : -((2 : ℕ) • Q) = (2 : ℕ) • Q := by
      apply neg_eq_iff_add_eq_zero.mpr
      simpa only [show (4 : ℕ) = 2 + 2 by decide, add_nsmul] using hQ
    exact (eq_neg_of_add_eq_zero_left hker).trans hnq
  · exfalso
    apply hQ2
    have h6 : 6 • Q = 0 := by
      calc
        6 • Q = 2 • (T + 3 • Q) - 2 • T := by abel
        _ = 0 := by rw [hker, hT]; simp
    calc
      2 • Q = 6 • Q - 4 • Q := by abel
      _ = 0 := by rw [h6, hQ]; simp

/-- The fifteen groups listed in Mazur's Theorem (8), p. 35. -/
def IsInMazurClass (G : Type*) [AddCommGroup G] : Prop :=
  (∃ n : ℕ, 1 ≤ n ∧ (n ≤ 10 ∨ n = 12) ∧ Nonempty (G ≃+ ZMod n)) ∨
  ∃ n : ℕ, 1 ≤ n ∧ n ≤ 4 ∧ Nonempty (G ≃+ (ZMod 2 × ZMod (2 * n)))

/-- Mazur's classification of rational torsion. -/
def MazurTorsionTheorem : Prop :=
  ∀ W : WeierstrassCurve ℚ, GoodCurve W →
    IsInMazurClass (AddCommGroup.torsion (RationalPoints W))

theorem two_four_equiv_of_mazur {G : Type*} [AddCommGroup G]
    (hclass : IsInMazurClass G)
    (f : (ZMod 2 × ZMod 4) →+ G) (hf : Function.Injective f)
    (hno8 : ¬∃ Q : G, addOrderOf Q = 8) : Nonempty (G ≃+ (ZMod 2 × ZMod 4)) := by
  rcases hclass with ⟨n, hn, hn', ⟨e⟩⟩ | ⟨n, hn, hn', ⟨e⟩⟩
  · have hi := e.injective.comp hf
    have hc := isAddCyclic_of_injective (e.toAddMonoidHom.comp f) hi
    let _ := hc
    have hh := coprime_card_of_isAddCyclic_prod (ZMod 2) (ZMod 4)
    norm_num [Nat.card_eq_fintype_card] at hh
  · have hd := AddSubgroup.card_dvd_of_injective (e.toAddMonoidHom.comp f) (e.injective.comp hf)
    norm_num [Nat.card_eq_fintype_card] at hd
    interval_cases n
    · norm_num at hd
    · exact ⟨e⟩
    · norm_num at hd
    · exfalso
      apply hno8
      refine ⟨e.symm (0, 1), ?_⟩
      rw [e.symm.addOrderOf_eq]
      rw [Prod.addOrderOf_mk, addOrderOf_zero, ZMod.addOrderOf_one]
      norm_num

end Z2Z4Rank6
