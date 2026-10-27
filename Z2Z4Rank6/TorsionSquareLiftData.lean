import Z2Z4Rank6.GusicTadicFactorization
import Z2Z4Rank6.SingularFibers
import Z2Z4Rank6.JInvariant
import Mathlib.FieldTheory.Separable

/-!
# Polynomial and rational-point data for the signed torsion covers

The first-family product polynomial is separable of degree twelve.
Signed square lifts and their parameter fibers are explicit. Source:
Jaswal, Theorem 1.2(c), DOI 10.5281/zenodo.23437117.
-/

namespace Z2Z4Rank6.TorsionHyperelliptic
open Polynomial
noncomputable section

def sign (ε : Bool) : ℚ := if ε then -1 else 1

theorem sign_ne_zero (ε : Bool) : sign ε≠0 := by cases ε <;> norm_num [sign]

def H (ε : Bool) : ℚ[X] :=
  C (sign ε)*q1 (Polynomial.X^2)*q2 (Polynomial.X^2)*a Polynomial.X*b Polynomial.X

def core : ℚ[X] :=
  (3*Polynomial.X^2+242)*(2*Polynomial.X^2+243)*
    (Polynomial.X^2-1)*(Polynomial.X^2-81)*(Polynomial.X^2-121)*(Polynomial.X^2-9801)

theorem H_factor (ε : Bool) : H ε=C (-1225*sign ε)*core := by
  unfold H core q1 q2 a b
  simp only [map_mul, map_neg, map_ofNat]
  ring

def bezoutA : ℚ[X] := Polynomial.C (1/5648880896406 : ℚ)*Polynomial.X^0+Polynomial.C (-108152401220003772425720248087/692187877206442088708962421957184000000000000 : ℚ)*Polynomial.X^2+Polynomial.C (-265760141842623366009429342682109/2261377794833446303812180232534120128000000000000 : ℚ)*Polynomial.X^4+Polynomial.C (250789275823216825343076282103/6784133384500338911436540697602360384000000000000 : ℚ)*Polynomial.X^6+Polynomial.C (62609303276223887127845617523/6784133384500338911436540697602360384000000000000 : ℚ)*Polynomial.X^8+Polynomial.C (-212993617540612306542017/188448149569453858651015019377843344000000000000 : ℚ)*Polynomial.X^10

def bezoutB : ℚ[X] := Polynomial.C (-77243026774494877033224271/871903820857839006990924864000000000000 : ℚ)*Polynomial.X^1+Polynomial.C (8702136848077910069776207277/276875150882576835483584968782873600000000000 : ℚ)*Polynomial.X^3+Polynomial.C (53169629146818078519143241349771/2713653353800135564574616279040944153600000000000 : ℚ)*Polynomial.X^5+Polynomial.C (-10700162413699088470154377871/2713653353800135564574616279040944153600000000000 : ℚ)*Polynomial.X^7+Polynomial.C (-2504522363913494582929605977/2713653353800135564574616279040944153600000000000 : ℚ)*Polynomial.X^9+Polynomial.C (212993617540612306542017/2261377794833446303812180232534120128000000000000 : ℚ)*Polynomial.X^11

/-- Exact rational Bezout identity, checked by polynomial arithmetic. -/
theorem core_bezout : bezoutA*core+bezoutB*derivative core=1 := by
  apply Polynomial.funext
  intro x
  norm_num [bezoutA,bezoutB,core,derivative_mul,derivative_pow]
  ring

theorem core_separable : core.Separable := ⟨bezoutA,bezoutB,core_bezout⟩

theorem H_separable (ε : Bool) : (H ε).Separable := by
  rw [H_factor]
  apply core_separable.unit_mul
  apply isUnit_C.mpr
  exact isUnit_iff_ne_zero.mpr (mul_ne_zero (by norm_num) (sign_ne_zero ε))

theorem H_squarefree (ε : Bool) : Squarefree (H ε) := (H_separable ε).squarefree

theorem H_natDegree (ε : Bool) : (H ε).natDegree=12 := by
  cases ε <;> unfold H sign q1 q2 a b <;> norm_num <;> compute_degree!

theorem H_degree (ε : Bool) : (H ε).degree=12 := by
  rw [degree_eq_natDegree (H_squarefree ε).ne_zero,H_natDegree]
  rfl

theorem eval_H (ε : Bool) (m : ℚ) :
    (H ε).eval m=sign ε*q1 (m^2)*q2 (m^2)*a m*b m := by
  simp [H,q1,q2,a,b]

/-- Every square-root fiber in a field has at most two possible values. -/
theorem finite_square_fiber {K : Type*} [Field K] (t : K) :
    {r : K | r^2=t}.Finite := by
  by_cases h : ∃ r : K,r^2=t
  · obtain ⟨r,hr⟩ := h
    apply (Set.toFinite ({r,-r} : Set K)).subset
    intro s hs
    have he : s^2=r^2 := hs.trans hr.symm
    simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using sq_eq_sq_iff_eq_or_eq_neg.mp he
  · have he : {r : K | r^2=t}=∅ := by ext r; simp only [Set.mem_ofPred_eq,Set.mem_empty_iff_false]; exact ⟨fun hr => h ⟨r,hr⟩,False.elim⟩
    rw [he]
    exact Set.finite_empty

@[ext] structure SquareLift (ε : Bool) where
  c : CPoint
  r : ℚ
  r_sq : r^2=sign ε*a c.m*b c.m

/-- The signed-lift parameter map has finite fibers. -/
theorem finite_lift_m_fiber (ε : Bool) (m : ℚ) :
    {P : SquareLift ε | P.c.m=m}.Finite := by
  let f : SquareLift ε → CPoint×ℚ := fun P => (P.c,P.r)
  have hsub : f '' {P : SquareLift ε | P.c.m=m} ⊆
      {c : CPoint | c.m=m} ×ˢ {r : ℚ | r^2=sign ε*a m*b m} := by
    rintro _ ⟨P,hP,rfl⟩
    change P.c.m=m at hP
    refine ⟨hP,?_⟩
    change P.r^2=sign ε*a m*b m
    simpa only [hP] using P.r_sq
  exact (((finite_CPoint_m_fiber m).prod
    (finite_square_fiber (sign ε*a m*b m))).subset hsub).of_finite_image (by
      intro P hP Q hQ h
      apply SquareLift.ext
      · exact congrArg Prod.fst h
      · exact congrArg Prod.snd h)

theorem C_u_ne_zero (c : CPoint) : c.u≠0 := by
  intro h
  have hh := c.u_sq
  rw [h] at hh
  nlinarith [sq_nonneg c.m]

theorem C_v_ne_zero (c : CPoint) : c.v≠0 := by
  intro h
  have hh := c.v_sq
  rw [h] at hh
  nlinarith [sq_nonneg c.m]

theorem C_ab_zero_iff_exceptional (c : CPoint) :
    a c.m*b c.m=0 ↔ c∈exceptionalPoints := by
  constructor
  · intro hab
    have hs : singularParameter c.m := by
      by_contra hn
      exact ((family_discriminant_factor_nonzero_iff c.m).mpr hn) (by rw [hab,zero_mul])
    exact (singularParameter_iff_exceptional c).mp hs
  · intro hc
    change exceptionalCPoint c at hc
    rcases hc with ⟨hm,_,_⟩ | ⟨hm,_,_⟩ <;> rcases hm with hm | hm <;>
      norm_num [a,b,hm]

theorem lift_r_zero_iff_exceptional (ε : Bool) (P : SquareLift ε) :
    P.r=0 ↔ P.c∈exceptionalPoints := by
  rw [←C_ab_zero_iff_exceptional]
  have he : P.r^2=sign ε*(a P.c.m*b P.c.m) := by rw [P.r_sq]; ring
  constructor
  · intro hr
    rw [hr,zero_pow (by decide)] at he
    exact (mul_eq_zero.mp he.symm).resolve_left (sign_ne_zero ε)
  · intro hab
    have hr : P.r^2=0 := by rw [he,hab,mul_zero]
    exact sq_eq_zero_iff.mp hr

end
end Z2Z4Rank6.TorsionHyperelliptic
