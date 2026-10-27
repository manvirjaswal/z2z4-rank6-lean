import Z2Z4Rank6.TwoDescent
import Z2Z4Rank6.Sections
import Z2Z4Rank6.Torsion
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

/-!
# The rank-three specialization

The lower-bound argument of Proposition 2.3 of Manvir Jaswal,
"Infinitely many elliptic curves with torsion Z/2Z × Z/4Z and rank at least six",
DOI: 10.5281/zenodo.23437117, using m=37/5 and the printed
two-descent representatives. Explicit square factors are checked below using rational arithmetic.
-/

namespace Z2Z4Rank6

def rankThreeParameter : ℚ := 37 / 5

theorem rankThree_factor_nonzero :
    a rankThreeParameter * b rankThreeParameter *
      (a rankThreeParameter ^ 2 - b rankThreeParameter ^ 2) ≠ 0 := by
  norm_num [rankThreeParameter, a, b]

instance rankThree_isElliptic : (X rankThreeParameter).IsElliptic :=
  E_good _ _ rankThree_factor_nonzero

def rankThreePoints : Fin 3 → RationalPoints (X rankThreeParameter) :=
  ![point1 rankThreeParameter, point2 rankThreeParameter, point3 rankThreeParameter]

def rankThreeTwo : RationalPoints (X rankThreeParameter) :=
  twoLeft _ _ rankThree_factor_nonzero

def rankThreeFour : RationalPoints (X rankThreeParameter) :=
  fourPoint _ _ rankThree_factor_nonzero

def rankThreeFivePoints : Fin 5 → RationalPoints (X rankThreeParameter) :=
  ![rankThreePoints 0, rankThreePoints 1, rankThreePoints 2, rankThreeTwo, rankThreeFour]

/-- The order here is P₁,P₂,P₃,(-a²,0),(ab,ab(a+b)), as in the proof. -/
def rankThreeRepresentatives : Fin 5 → ℚ × ℚ :=
  ![(-1, 5*7*37*79), (-2*3*19*229, 3*79*229), (-2*3*19, 3*7*37),
    (-1, 5*7*37*79*20233), (3*19*23*41*229, 3*5*37*41*79*229)]

private def rankThreeSquareFactors : Fin 5 → ℚ × ℚ :=
  ![(175891968/625, 289296/625), (577024/625, 753424/625),
    (8871744/625, 1253616/125), (198746352/625, 5/253503), (37632/625, 2352/125)]

private def rankThreeRawValues : Fin 5 → ℚ × ℚ :=
  let α := a rankThreeParameter
  let β := b rankThreeParameter
  ![(p1x rankThreeParameter, p1x rankThreeParameter + α^2),
    (p2x rankThreeParameter, p2x rankThreeParameter + α^2),
    (p3x rankThreeParameter, p3x rankThreeParameter + α^2),
    (-α^2, (α^2-β^2)/α^2), (α*β, α*β+α^2)]

private theorem rankThree_square_factors (i : Fin 5) :
    (rankThreeRawValues i).1 = (rankThreeRepresentatives i).1 * (rankThreeSquareFactors i).1^2 ∧
    (rankThreeRawValues i).2 = (rankThreeRepresentatives i).2 * (rankThreeSquareFactors i).2^2 := by
  fin_cases i <;> norm_num [rankThreeRawValues, rankThreeRepresentatives,
    rankThreeSquareFactors, rankThreeParameter, a, b, p1x, p2x, p3x]

noncomputable def rankThreeSquareclasses : Fin 5 → RatSquareClassAdd × RatSquareClassAdd :=
  fun i => (squareClass (rankThreeRepresentatives i).1, squareClass (rankThreeRepresentatives i).2)

private theorem rankThree_raw_squareclasses (i : Fin 5) :
    (squareClass (rankThreeRawValues i).1, squareClass (rankThreeRawValues i).2) =
      rankThreeSquareclasses i := by
  apply Prod.ext
  · apply squareClass_eq_of_factor _ _ (rankThreeSquareFactors i).1
    · fin_cases i <;> norm_num [rankThreeRawValues, rankThreeParameter, a, b, p1x, p2x, p3x]
    · fin_cases i <;> norm_num [rankThreeRepresentatives]
    · fin_cases i <;> norm_num [rankThreeSquareFactors]
    · exact (rankThree_square_factors i).1
  · apply squareClass_eq_of_factor _ _ (rankThreeSquareFactors i).2
    · fin_cases i <;> norm_num [rankThreeRawValues, rankThreeParameter, a, b, p1x, p2x, p3x]
    · fin_cases i <;> norm_num [rankThreeRepresentatives]
    · fin_cases i <;> norm_num [rankThreeSquareFactors]
    · exact (rankThree_square_factors i).2

/-- All ten printed nontrivial squareclass representatives, checked against
the exact coordinate formula including the special two-torsion value. -/
theorem rankThree_descent_coordinates (i : Fin 5) :
    completeDescentCoordinates (X rankThreeParameter) 0
      (-(a rankThreeParameter ^ 2)) (-(b rankThreeParameter ^ 2)) (rankThreeFivePoints i) =
        rankThreeSquareclasses i := by
  rw [← rankThree_raw_squareclasses i]
  fin_cases i <;> norm_num [rankThreeFivePoints, rankThreePoints, rankThreeTwo, rankThreeFour,
    point1, point2, point3, WeierstrassCurve.Affine.Point.mk, twoLeft, fourPoint,
    completeDescentCoordinates, rankThreeRawValues, rankThreeParameter, a, b, p1x, p2x, p3x]

local instance rankThree_fact_prime_two : Fact (Nat.Prime 2) := ⟨by decide⟩
local instance rankThree_fact_prime_23 : Fact (Nat.Prime 23) := ⟨by decide⟩
local instance rankThree_fact_prime_229 : Fact (Nat.Prime 229) := ⟨by norm_num⟩
set_option maxRecDepth 4096 in
local instance rankThree_fact_prime_20233 : Fact (Nat.Prime 20233) := ⟨by norm_num⟩

private theorem valuation_nat_zero_or_one {p n : ℕ} [Fact p.Prime]
    (hn : n ≠ 0) (hp2 : ¬p ^ 2 ∣ n) :
    padicValNat p n = if p ∣ n then 1 else 0 := by
  split_ifs with hdiv
  · have hlow : 1 ≤ padicValNat p n := by
      apply (padicValNat_dvd_iff_le hn).1
      simpa only [pow_one] using hdiv
    have hhigh : ¬2 ≤ padicValNat p n := by
      intro hh
      exact hp2 ((padicValNat_dvd_iff_le hn).2 hh)
    omega
  · exact padicValNat.eq_zero_of_not_dvd hdiv

/-- The sign and four distinguishing prime coordinates in the printed
elimination: sign in the first component, 20233 in the second, then 23,229,2
in the first. -/
noncomputable def rankThreeParity : (RatSquareClassAdd × RatSquareClassAdd) →+ (Fin 5 → ZMod 2) where
  toFun q := ![squareClassSign q.1, squareClassValuation 20233 q.2,
    squareClassValuation 23 q.1, squareClassValuation 229 q.1, squareClassValuation 2 q.1]
  map_zero' := by ext i; fin_cases i <;> simp
  map_add' q r := by ext i; fin_cases i <;> simp

def rankThreeParityVectors : Fin 5 → Fin 5 → ZMod 2 :=
  ![![1,0,0,0,0], ![1,0,0,1,1], ![1,0,0,0,1], ![1,1,0,0,0], ![0,0,1,1,0]]

theorem rankThree_parity_values (i : Fin 5) :
    rankThreeParity (rankThreeSquareclasses i) = rankThreeParityVectors i := by
  ext j
  fin_cases i <;> fin_cases j <;>
    simp only [rankThreeParity, rankThreeSquareclasses, rankThreeRepresentatives,
      rankThreeParityVectors, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  all_goals simp (disch := norm_num) only [squareClassValuation_apply, squareClassSign_apply]
  all_goals norm_num [padicValRat_def, padicValInt]
  all_goals try rw [valuation_nat_zero_or_one (by decide) (by decide)]
  all_goals norm_num

/-- The five nontrivial printed two-descent vectors are F₂-independent,
using the four printed distinguishing primes and the negative first entry
of the remaining P₁ vector. -/
theorem rankThree_squareclasses_independent : LinearIndependent (ZMod 2) rankThreeSquareclasses := by
  apply Fintype.linearIndependent_iff.mpr
  intro n hn
  have hm : ∑ i, n i • rankThreeParityVectors i = 0 := by
    have hh := congrArg rankThreeParity hn
    simpa only [map_sum, ZMod.map_smul, rankThree_parity_values, map_zero] using hh
  have h0 := congrFun hm 0
  have h1 := congrFun hm 1
  have h2 := congrFun hm 2
  have h3 := congrFun hm 3
  have h4 := congrFun hm 4
  norm_num [Fin.sum_univ_succ, rankThreeParityVectors] at h0 h1 h2 h3 h4
  intro i
  fin_cases i <;> simp_all

private def integralPointOrbit {G : Type*} [AddCommGroup G] (P : G) : ℤ →+ G where
  toFun n := n • P
  map_zero' := zero_zsmul P
  map_add' n m := by simp only [add_zsmul]

private def cyclicPointHom {G : Type*} [AddCommGroup G] (n : ℕ) (P : G) (hn : n • P = 0) :
    ZMod n →+ G :=
  ZMod.lift n ⟨integralPointOrbit P, by change (n : ℤ) • P = 0; simpa only [natCast_zsmul] using hn⟩

private theorem cyclicPointHom_val {G : Type*} [AddCommGroup G] (n : ℕ) [NeZero n]
    (P : G) (hn : n • P = 0) (z : ZMod n) : cyclicPointHom n P hn z = z.val • P := by
  conv_lhs => rw [← ZMod.natCast_zmod_val z]
  unfold cyclicPointHom
  rw [← Int.cast_natCast z.val, ZMod.lift_coe]
  simp only [integralPointOrbit, natCast_zsmul, AddMonoidHom.coe_mk, ZeroHom.coe_mk]

private theorem cyclic_two_four_injective {G : Type*} [AddCommGroup G] (T Q : G)
    (hT : 2 • T = 0) (hQ : 4 • Q = 0) (hT0 : T ≠ 0) (hQ2 : 2 • Q ≠ 0)
    (hne : T ≠ 2 • Q) :
    Function.Injective ((cyclicPointHom 2 T hT).coprod (cyclicPointHom 4 Q hQ)) := by
  apply (injective_iff_map_eq_zero _).mpr
  rintro ⟨u, v⟩ hker
  change cyclicPointHom 2 T hT u + cyclicPointHom 4 Q hQ v = 0 at hker
  rw [cyclicPointHom_val, cyclicPointHom_val] at hker
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

private theorem rankThree_two_double : (2 : ℕ) • rankThreeTwo = 0 := by
  have hh : (2 : ℕ) • twoLeft _ _ rankThree_factor_nonzero = 0 := by
    rw [two_nsmul, twoLeft_double]
  exact hh

private theorem rankThree_four_quadruple : (4 : ℕ) • rankThreeFour = 0 :=
  fourPoint_quadruple _ _ rankThree_factor_nonzero

private def rankThreeGenerators : (ZMod 2 × ZMod 4) →+ RationalPoints (X rankThreeParameter) :=
  (cyclicPointHom 2 rankThreeTwo rankThree_two_double).coprod
    (cyclicPointHom 4 rankThreeFour rankThree_four_quadruple)

private theorem rankThreeGenerators_apply (x : ZMod 2 × ZMod 4) :
    rankThreeGenerators x = x.1.val • rankThreeTwo + x.2.val • rankThreeFour := by
  simp only [rankThreeGenerators, AddMonoidHom.coprod_apply, cyclicPointHom_val]

private theorem rankThreeGenerators_injective : Function.Injective rankThreeGenerators := by
  apply cyclic_two_four_injective
  · exact twoLeft_ne_zero _ _ rankThree_factor_nonzero
  · have hh : (2 : ℕ) • fourPoint _ _ rankThree_factor_nonzero ≠ 0 := by
      rw [two_nsmul, fourPoint_double]
      exact twoZero_ne_zero _ _ rankThree_factor_nonzero
    exact hh
  · have hh : twoLeft _ _ rankThree_factor_nonzero ≠
        (2 : ℕ) • fourPoint _ _ rankThree_factor_nonzero := by
      rw [two_nsmul, fourPoint_double]
      exact twoLeft_ne_twoZero _ _ rankThree_factor_nonzero
    exact hh

private theorem rankThree_ab_not_square :
    ¬IsSquare (a rankThreeParameter * b rankThreeParameter) := by
  intro hs
  have hclass := squareClass_eq_zero_of_isSquare hs
  have hraw := congrArg Prod.fst (rankThree_raw_squareclasses (4 : Fin 5))
  change squareClass (a rankThreeParameter * b rankThreeParameter) = _ at hraw
  have hparity := congrFun (rankThree_parity_values (4 : Fin 5)) (2 : Fin 5)
  change squareClassValuation 23 (squareClass (rankThreeRepresentatives (4 : Fin 5)).1) = 1 at hparity
  have hval : squareClassValuation 23 (squareClass (a rankThreeParameter * b rankThreeParameter)) = 1 := by
    rw [hraw]
    exact hparity
  rw [hclass, map_zero] at hval
  norm_num at hval

theorem rankThree_torsion_exact (hMazur : MazurTorsionTheorem) :
    TorsionExact (X rankThreeParameter) := by
  apply E_torsion_exact hMazur _ _ rankThree_factor_nonzero rankThree_ab_not_square
  rintro ⟨r, hr⟩
  have hpos : 0 < a rankThreeParameter * b rankThreeParameter := by norm_num [rankThreeParameter, a, b]
  nlinarith [sq_nonneg r]

/-- The two displayed torsion points generate the entire rational torsion.
This proves the torsion-image span used in the printed two-descent argument. -/
theorem rankThree_torsion_generators (hMazur : MazurTorsionTheorem)
    (R : RationalPoints (X rankThreeParameter)) (hR : IsOfFinAddOrder R) :
    ∃ x : ZMod 2 × ZMod 4, R = x.1.val • rankThreeTwo + x.2.val • rankThreeFour := by
  let f := rankThreeGenerators.codRestrict
    (AddCommGroup.torsion (RationalPoints (X rankThreeParameter)))
    (fun x => rankThreeGenerators.isOfFinAddOrder (isOfFinAddOrder_of_finite x))
  have hf : Function.Injective f := by
    intro x y hxy
    exact rankThreeGenerators_injective (congrArg Subtype.val hxy)
  obtain ⟨e⟩ := rankThree_torsion_exact hMazur
  have he : Function.Surjective (e.toAddMonoidHom.comp f) :=
    Finite.surjective_of_injective (e.injective.comp hf)
  obtain ⟨x, hx⟩ := he (e ⟨R, hR⟩)
  have hfx := e.injective hx
  refine ⟨x, ?_⟩
  exact (congrArg Subtype.val hfx).symm.trans (rankThreeGenerators_apply x)

/-- Proposition 2.3, lower bound at m=37/5: the three printed specialized
sections are Z-linearly independent. The hypotheses are Mazur's classification and the complete
two-descent homomorphism theorem. -/
theorem rankThree_specialized_independent (hMazur : MazurTorsionTheorem)
    (hDescent : CompleteTwoDescentTheorem) : LinearIndependent ℤ rankThreePoints := by
  obtain ⟨κ, hκ, _hker⟩ := hDescent (X rankThreeParameter) 0
    (-(a rankThreeParameter ^ 2)) (-(b rankThreeParameter ^ 2)) rankThree_isElliptic
    (E_eq_splitWeierstrass _ _)
  have hvalues : ∀ i, κ (rankThreeFivePoints i) = rankThreeSquareclasses i :=
    fun i => (hκ _).trans (rankThree_descent_coordinates i)
  have hlin : LinearIndependent (ZMod 2) (fun i => κ (rankThreeFivePoints i)) := by
    simpa only [hvalues] using rankThree_squareclasses_independent
  have hdiv : ∀ a : Fin 3 → ℤ, IsOfFinAddOrder (∑ i, a i • rankThreePoints i) →
      ∀ j, (2 : ℤ) ∣ a j := by
    intro a ha j
    obtain ⟨x, hx⟩ := rankThree_torsion_generators hMazur (∑ i, a i • rankThreePoints i) ha
    have hr : ∑ i, (a i : ZMod 2) • κ (rankThreePoints i) =
        (x.1.val : ZMod 2) • κ rankThreeTwo + (x.2.val : ZMod 2) • κ rankThreeFour := by
      have hh := congrArg κ hx
      simpa only [map_sum, map_zsmul, map_add, map_nsmul,
        Int.cast_smul_eq_zsmul, Nat.cast_smul_eq_nsmul] using hh
    let c : Fin 5 → ZMod 2 :=
      ![(a 0 : ZMod 2), (a 1 : ZMod 2), (a 2 : ZMod 2), -(x.1.val : ZMod 2), -(x.2.val : ZMod 2)]
    have hz : ∑ i, c i • κ (rankThreeFivePoints i) = 0 := by
      calc
        _ = (∑ i, (a i : ZMod 2) • κ (rankThreePoints i)) -
            ((x.1.val : ZMod 2) • κ rankThreeTwo + (x.2.val : ZMod 2) • κ rankThreeFour) := by
          simp [c, Fin.sum_univ_succ, rankThreeFivePoints]
          match_scalars <;> simp [CharTwo.neg_eq]
        _ = 0 := sub_eq_zero.mpr hr
    have hc := (Fintype.linearIndependent_iff.mp hlin) c hz
    fin_cases j
    · exact (ZMod.intCast_zmod_eq_zero_iff_dvd (a 0) 2).mp (hc 0)
    · exact (ZMod.intCast_zmod_eq_zero_iff_dvd (a 1) 2).mp (hc 1)
    · exact (ZMod.intCast_zmod_eq_zero_iff_dvd (a 2) 2).mp (hc 2)
  apply Fintype.linearIndependent_iff.mpr
  intro n hn
  exact coefficients_zero_of_torsion_divisibility_at 2 (by decide) rankThreePoints hdiv n
    (hn ▸ IsOfFinAddOrder.zero)

/-- Transport of the checked specialization to any point group. This lemma
requires a specialization homomorphism with the three stated values;
it does not assert that such a homomorphism has been constructed. -/
theorem rankThree_independent_of_specialization {G : Type*} [AddCommGroup G]
    (hMazur : MazurTorsionTheorem) (hDescent : CompleteTwoDescentTheorem)
    (P : Fin 3 → G) (sp : G →+ RationalPoints (X rankThreeParameter))
    (hsp : ∀ i, sp (P i) = rankThreePoints i) : LinearIndependent ℤ P := by
  apply Fintype.linearIndependent_iff.mpr
  intro n hn
  apply (Fintype.linearIndependent_iff.mp (rankThree_specialized_independent hMazur hDescent)) n
  have hh := congrArg sp hn
  simpa only [map_sum, map_zsmul, map_zero, hsp] using hh

end Z2Z4Rank6
