module

public import Z2Z4Rank6.SplitDescentImage
public import Mathlib.Tactic

@[expose] public section

/-!
# Full two-torsion on split rational Weierstrass curves

The two distinct roots give independent points of order two. This
elementary construction supplies the four torsion classes used in the
two-descent rank bounds; it uses no rational torsion classification theorem.
-/

namespace Z2Z4Rank6
noncomputable section

private def integerOrbitTwo {G : Type*} [AddCommGroup G] (P : G) : ℤ →+ G where
  toFun n := n • P
  map_zero' := zero_zsmul P
  map_add' n m := by simp only [add_zsmul]

private def orbitHomTwo {G : Type*} [AddCommGroup G] (P : G) (hp : 2 • P=0) : ZMod 2 →+ G :=
  ZMod.lift 2 ⟨integerOrbitTwo P,
    by change (2:ℤ) • P=0; simpa only [two_zsmul,two_nsmul] using hp⟩

private theorem orbitHomTwo_val {G : Type*} [AddCommGroup G] (P : G) (hp : 2 • P=0)
    (z : ZMod 2) : orbitHomTwo P hp z=z.val • P := by
  conv_lhs => rw [←ZMod.natCast_zmod_val z,←Int.cast_natCast z.val]
  rw [orbitHomTwo,ZMod.lift_coe]
  simp only [integerOrbitTwo,AddMonoidHom.coe_mk,ZeroHom.coe_mk,natCast_zsmul]

theorem two_two_injective {G : Type*} [AddCommGroup G] (T U : G)
    (hT : 2 • T=0) (hU : 2 • U=0) (hT0 : T≠0) (hU0 : U≠0) (hne : T≠U) :
    ∃ j : (ZMod 2 × ZMod 2) →+ G, Function.Injective j := by
  let j := (orbitHomTwo T hT).coprod (orbitHomTwo U hU)
  refine ⟨j,(injective_iff_map_eq_zero j).mpr ?_⟩
  rintro ⟨a,b⟩ h
  change orbitHomTwo T hT a+orbitHomTwo U hU b=0 at h
  rw [orbitHomTwo_val,orbitHomTwo_val] at h
  have ha := ZMod.val_lt a
  have hb := ZMod.val_lt b
  interval_cases hav : a.val <;> interval_cases hbv : b.val
  all_goals simp only [zero_nsmul,one_nsmul,zero_add,add_zero] at h
  · exact Prod.ext ((ZMod.val_eq_zero a).mp hav) ((ZMod.val_eq_zero b).mp hbv)
  · exact False.elim (hU0 h)
  · exact False.elim (hT0 h)
  · exfalso
    apply hne
    have hu : -U=U := neg_eq_iff_add_eq_zero.mpr (by simpa only [two_nsmul] using hU)
    exact (eq_neg_of_add_eq_zero_left h).trans hu

namespace SplitTwoTorsion

def curve (r2 r3 : ℚ) : WeierstrassCurve ℚ := splitWeierstrass 0 (-r2) (-r3)

variable (r2 r3 : ℚ) [(curve r2 r3).IsElliptic]

def first : RationalPoints (curve r2 r3) :=
  .mk ((splitWeierstrass_equation_iff r2 r3 0 0).mpr (by ring))

def second : RationalPoints (curve r2 r3) :=
  .mk ((splitWeierstrass_equation_iff r2 r3 (-r2) 0).mpr (by ring))

theorem first_double : (2:ℕ) • first r2 r3=0 := by
  rw [two_nsmul]
  apply WeierstrassCurve.Affine.Point.add_self_of_Y_eq
  norm_num [WeierstrassCurve.Affine.negY,curve,splitWeierstrass]

theorem second_double : (2:ℕ) • second r2 r3=0 := by
  rw [two_nsmul]
  apply WeierstrassCurve.Affine.Point.add_self_of_Y_eq
  norm_num [WeierstrassCurve.Affine.negY,curve,splitWeierstrass]

theorem inclusion (hr2 : r2≠0) :
    ∃ j : (ZMod 2 × ZMod 2) →+ RationalPoints (curve r2 r3), Function.Injective j := by
  apply two_two_injective (first r2 r3) (second r2 r3)
    (first_double r2 r3) (second_double r2 r3)
  · exact WeierstrassCurve.Affine.Point.some_ne_zero _
  · exact WeierstrassCurve.Affine.Point.some_ne_zero _
  · intro h
    have hx := (WeierstrassCurve.Affine.Point.some.inj h).1
    exact hr2 (neg_eq_zero.mp hx.symm)

end SplitTwoTorsion
end
end Z2Z4Rank6
