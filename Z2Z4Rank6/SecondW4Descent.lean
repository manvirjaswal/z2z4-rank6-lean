module

public import Z2Z4Rank6.SecondW4Torsion

@[expose] public section

/-!
# The four printed complete-descent vectors at W=4

The two qA-twist sections and the two rational two-torsion points have
the exact squareclasses printed in the proof of Theorem 8.1(b). Their
independence implies independence of the two sections modulo the entire
rational torsion subgroup.
-/
namespace Z2Z4Rank6.SecondW4
noncomputable section
open SecondFamily

def qAPoints : Fin 2 → (twistedF (4 : ℚ) (qA 4)).toAffine.Point :=
  ![Q2twist 4, Q3twist 4]

def fourPoints : Fin 4 → (twistedF (4 : ℚ) (qA 4)).toAffine.Point :=
  ![Q2twist 4, Q3twist 4, twoZero, twoRoot]

def representatives : Fin 4 → ℚ × ℚ :=
  ![(3*23*79*2539, 3*29*2539), (3*2017*2339, 3*29*2017),
    (1, 29*2017*2339), (-29*2017*2339, 29*53*89)]

def rawCoordinates : Fin 4 → ℚ × ℚ :=
  ![(4752801896675/468802872747, 2650697569866176/468802872747),
    (4062862011392/468802872747, 2650007629980893/468802872747),
    (3301489/58018689, 881981589323167/156267624249),
    (-881981589323167/156267624249, 54717200/58018689)]

def squareFactors : Fin 4 → ℚ × ℚ :=
  ![(1015/1185921, 189736/1185921), (928/1185921, 212849/1185921),
    (1817/7617, 2539/395307), (2539/395307, 20/7617)]

def squareclasses (i : Fin 4) : RatSquareClassAdd × RatSquareClassAdd :=
  (squareClass (representatives i).1, squareClass (representatives i).2)

theorem actual_descent_coordinates (i : Fin 4) :
    completeDescentCoordinates (twistedF (4 : ℚ) (qA 4)) 0 e2 e3 (fourPoints i) =
      (squareClass (rawCoordinates i).1, squareClass (rawCoordinates i).2) := by
  fin_cases i <;>
    norm_num [completeDescentCoordinates, fourPoints, Q2twist, Q3twist, twoZero, twoRoot,
      WeierstrassCurve.Affine.Point.mk, x2, x3, e2, e3, lambda, beta, rawCoordinates]

theorem raw_square_factors (i : Fin 4) :
    (rawCoordinates i).1 = (representatives i).1 * (squareFactors i).1^2 ∧
    (rawCoordinates i).2 = (representatives i).2 * (squareFactors i).2^2 := by
  fin_cases i <;> norm_num [rawCoordinates, representatives, squareFactors]

theorem descent_coordinates (i : Fin 4) :
    completeDescentCoordinates (twistedF (4 : ℚ) (qA 4)) 0 e2 e3 (fourPoints i) = squareclasses i := by
  rw [actual_descent_coordinates]
  apply Prod.ext
  · apply squareClass_eq_of_factor _ _ (squareFactors i).1
    · fin_cases i <;> norm_num [rawCoordinates]
    · fin_cases i <;> norm_num [representatives]
    · fin_cases i <;> norm_num [squareFactors]
    · exact (raw_square_factors i).1
  · apply squareClass_eq_of_factor _ _ (squareFactors i).2
    · fin_cases i <;> norm_num [rawCoordinates]
    · fin_cases i <;> norm_num [representatives]
    · fin_cases i <;> norm_num [squareFactors]
    · exact (raw_square_factors i).2

local instance prime_three : Fact (Nat.Prime 3) := ⟨by decide⟩
local instance prime_twenty_three : Fact (Nat.Prime 23) := ⟨by decide⟩
local instance prime_fifty_three : Fact (Nat.Prime 53) := ⟨by decide⟩
local instance prime_two_thousand_seventeen : Fact (Nat.Prime 2017) := ⟨by norm_num⟩

def parity : (RatSquareClassAdd × RatSquareClassAdd) →+ (Fin 4 → ZMod 2) where
  toFun q := ![squareClassValuation 23 q.1, squareClassValuation 53 q.2,
    squareClassValuation 3 q.1, squareClassValuation 2017 q.2]
  map_zero' := by ext i; fin_cases i <;> simp
  map_add' q r := by ext i; fin_cases i <;> simp

def parityVectors : Fin 4 → Fin 4 → ZMod 2 :=
  ![![1,0,1,0], ![0,0,1,1], ![0,0,0,1], ![0,1,0,0]]

private theorem valuation_nat_zero_or_one {p n : ℕ} [Fact p.Prime]
    (hn : n ≠ 0) (hp2 : ¬p^2 ∣ n) :
    padicValNat p n = if p ∣ n then 1 else 0 := by
  split_ifs with hd
  · have hl : 1 ≤ padicValNat p n := by
      apply (padicValNat_dvd_iff_le hn).mp
      simpa only [pow_one] using hd
    have hu : ¬2 ≤ padicValNat p n := by
      intro h
      exact hp2 ((padicValNat_dvd_iff_le hn).mpr h)
    omega
  · exact padicValNat.eq_zero_of_not_dvd hd

theorem parity_values (i : Fin 4) : parity (squareclasses i) = parityVectors i := by
  ext j
  fin_cases i <;> fin_cases j <;>
    simp only [parity, squareclasses, representatives, parityVectors,
      AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  all_goals simp (disch := norm_num) only [squareClassValuation_apply]
  all_goals norm_num [padicValRat_def, padicValInt]
  all_goals try rw [valuation_nat_zero_or_one (by decide) (by decide)]
  all_goals norm_num

theorem squareclasses_independent : LinearIndependent (ZMod 2) squareclasses := by
  apply Fintype.linearIndependent_iff.mpr
  intro n hn
  have hm : ∑ i, n i • parityVectors i = 0 := by
    have h := congrArg parity hn
    simpa only [map_sum, ZMod.map_smul, parity_values, map_zero] using h
  have h0 := congrFun hm 0
  have h1 := congrFun hm 1
  have h2 := congrFun hm 2
  have h3 := congrFun hm 3
  norm_num [Fin.sum_univ_succ, parityVectors] at h0 h1 h2 h3
  intro i
  fin_cases i <;> simp_all

/-- Every torsion-valued integral relation between the two named qA
sections has zero coefficients. This is independence modulo torsion. -/
theorem qA_points_independent_mod_torsion
    (hOdd : OddPrimeTorsionIntegrality) (hReduction : GoodReductionHomomorphisms)
    (hDescent : CompleteTwoDescentTheorem) (n : Fin 2 → ℤ)
    (ht : IsOfFinAddOrder (∑ i, n i • qAPoints i)) : ∀ i, n i = 0 := by
  obtain ⟨κ, hκ, _⟩ := hDescent (twistedF (4 : ℚ) (qA 4)) 0 e2 e3
    inferInstance qA_split
  have hvalues : ∀ i, κ (fourPoints i) = squareclasses i :=
    fun i => (hκ _).trans (descent_coordinates i)
  have hlin : LinearIndependent (ZMod 2) (fun i => κ (fourPoints i)) := by
    simpa only [hvalues] using squareclasses_independent
  have hdiv : ∀ a : Fin 2 → ℤ, IsOfFinAddOrder (∑ i, a i • qAPoints i) →
      ∀ j, (2 : ℤ) ∣ a j := by
    intro a ha j
    obtain ⟨z, hz⟩ := qA_torsion_generators hOdd hReduction (∑ i, a i • qAPoints i) ha
    have hr : ∑ i, (a i : ZMod 2) • κ (qAPoints i) =
        (z.1.val : ZMod 2) • κ twoZero + (z.2.val : ZMod 2) • κ twoRoot := by
      have h := congrArg κ hz
      simpa only [map_sum, map_zsmul, map_add, map_nsmul,
        Int.cast_smul_eq_zsmul, Nat.cast_smul_eq_nsmul] using h
    let c : Fin 4 → ZMod 2 :=
      ![(a 0 : ZMod 2), (a 1 : ZMod 2), -(z.1.val : ZMod 2), -(z.2.val : ZMod 2)]
    have hc : ∑ i, c i • κ (fourPoints i) = 0 := by
      calc
        _ = (∑ i, (a i : ZMod 2) • κ (qAPoints i)) -
            ((z.1.val : ZMod 2) • κ twoZero + (z.2.val : ZMod 2) • κ twoRoot) := by
          simp [c, Fin.sum_univ_succ, fourPoints, qAPoints]
          match_scalars <;> simp [CharTwo.neg_eq]
        _ = 0 := sub_eq_zero.mpr hr
    have hzero := (Fintype.linearIndependent_iff.mp hlin) c hc
    fin_cases j
    · exact (ZMod.intCast_zmod_eq_zero_iff_dvd (a 0) 2).mp (hzero 0)
    · exact (ZMod.intCast_zmod_eq_zero_iff_dvd (a 1) 2).mp (hzero 1)
  exact coefficients_zero_of_torsion_divisibility_at 2 (by decide) qAPoints hdiv n ht

theorem qA_points_independent
    (hOdd : OddPrimeTorsionIntegrality) (hReduction : GoodReductionHomomorphisms)
    (hDescent : CompleteTwoDescentTheorem) : LinearIndependent ℤ qAPoints := by
  apply Fintype.linearIndependent_iff.mpr
  intro n hn
  exact qA_points_independent_mod_torsion hOdd hReduction hDescent n
    (hn ▸ IsOfFinAddOrder.zero)

end
end Z2Z4Rank6.SecondW4
