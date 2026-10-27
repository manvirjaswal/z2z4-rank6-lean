import Z2Z4Rank6.Residue
import Z2Z4Rank6.TorsionCongruence
import Mathlib.NumberTheory.Padics.RingHoms

/-!
# Rational residues and p-adic neighborhoods

The coordinate neighborhoods used in Proposition 6.2 of Manvir Jaswal,
"Infinitely many elliptic curves with torsion Z/2Z × Z/4Z and rank at least six",
DOI: 10.5281/zenodo.23437117.

Rational integrality and reduction are related to Mathlib's p-adic norm
and residue homomorphism. The valuation condition includes zero differences.
-/

namespace Z2Z4Rank6

open Topology

section Prime

variable {p : ℕ} [Fact p.Prime]

/-- Denominator integrality is equivalent to norm at most one in Q_p. -/
theorem integralAt_iff_padic_norm_le_one (q : ℚ) :
    IntegralAt p q ↔ ‖(q : ℚ_[p])‖ ≤ 1 := by
  constructor
  · intro hq
    apply Padic.norm_rat_le_one
    intro hdiv
    exact hq ((ZMod.natCast_eq_zero_iff q.den p).2 hdiv)
  · intro hq
    have hunit := PadicInt.isUnit_den q hq
    have hnorm : ‖(q.den : ℚ_[p])‖ = 1 := by
      simpa only [PadicInt.norm_def, PadicInt.coe_natCast] using
        (PadicInt.isUnit_iff.mp hunit)
    intro hzero
    have hdiv := (ZMod.natCast_eq_zero_iff q.den p).1 hzero
    have hlt := (Padic.norm_natCast_lt_one_iff (p := p) (n := q.den)).2 hdiv
    simp only [hnorm, lt_self_iff_false] at hlt

/-- The usual rational residue equals the residue of its integral p-adic cast. -/
theorem toZMod_ratCast (q : ℚ) (hq : IntegralAt p q) :
    PadicInt.toZMod (⟨(q : ℚ_[p]), (integralAt_iff_padic_norm_le_one q).1 hq⟩ : ℤ_[p]) =
      residue p q := by
  let z : ℤ_[p] := ⟨(q : ℚ_[p]), (integralAt_iff_padic_norm_le_one q).1 hq⟩
  have hmul : z * (q.den : ℤ_[p]) = (q.num : ℤ_[p]) := by
    apply Subtype.ext
    change (q : ℚ_[p]) * (q.den : ℚ_[p]) = (q.num : ℚ_[p])
    exact_mod_cast (Rat.mul_den_eq_num q)
  apply (eq_div_iff hq).2
  simpa only [map_mul, map_natCast, map_intCast] using
    congrArg PadicInt.toZMod hmul

/-- A p-adic perturbation of norm less than one preserves integrality and residue. -/
theorem residue_eq_of_padic_norm_sub_lt_one (q q₀ : ℚ) (hq₀ : IntegralAt p q₀)
    (hclose : ‖((q : ℚ_[p]) - (q₀ : ℚ_[p]))‖ < 1) :
    IntegralAt p q ∧ residue p q = residue p q₀ := by
  have hq₀norm := (integralAt_iff_padic_norm_le_one q₀).1 hq₀
  have hqnorm : ‖(q : ℚ_[p])‖ ≤ 1 := by
    calc
      _ = ‖((q : ℚ_[p]) - (q₀ : ℚ_[p])) + (q₀ : ℚ_[p])‖ := by rw [sub_add_cancel]
      _ ≤ max ‖((q : ℚ_[p]) - (q₀ : ℚ_[p]))‖ ‖(q₀ : ℚ_[p])‖ :=
        Padic.nonarchimedean _ _
      _ ≤ 1 := max_le hclose.le hq₀norm
  have hq := (integralAt_iff_padic_norm_le_one q).2 hqnorm
  refine ⟨hq, ?_⟩
  let z : ℤ_[p] := ⟨(q : ℚ_[p]), hqnorm⟩
  let z₀ : ℤ_[p] := ⟨(q₀ : ℚ_[p]), hq₀norm⟩
  have hzero : PadicInt.toZMod (z - z₀) = 0 := by
    rw [← RingHom.mem_ker, PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal,
      PadicInt.mem_nonunits]
    exact hclose
  rw [map_sub, sub_eq_zero] at hzero
  simpa only [z, z₀, toZMod_ratCast q hq, toZMod_ratCast q₀ hq₀] using hzero

/-- The norm ball giving equality of residues is open. -/
theorem isOpen_residueBall (q₀ : ℚ) :
    IsOpen {x : ℚ_[p] | ‖x - (q₀ : ℚ_[p])‖ < 1} :=
  isOpen_lt (continuous_norm.comp (continuous_id.sub continuous_const)) continuous_const

/-- The residue ball is a neighborhood of its rational center. -/
theorem residueBall_mem_nhds (q₀ : ℚ) :
    {x : ℚ_[p] | ‖x - (q₀ : ℚ_[p])‖ < 1} ∈ 𝓝 (q₀ : ℚ_[p]) :=
  (isOpen_residueBall (p := p) q₀).mem_nhds (by simp)

/-- A norm bound is the usual rational valuation bound, including zero. -/
theorem padic_norm_ratCast_le_zpow_iff (q : ℚ) (n : ℤ) :
    ‖(q : ℚ_[p])‖ ≤ (p : ℝ) ^ (-n) ↔ q = 0 ∨ n ≤ padicValRat p q := by
  have hp : 1 < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).one_lt
  by_cases hq : q = 0
  · simp only [hq, Rat.cast_zero, norm_zero, true_or, iff_true]
    exact (zpow_pos (by linarith : (0 : ℝ) < p) _).le
  · have hcast : (q : ℚ_[p]) ≠ 0 := by exact_mod_cast hq
    rw [Padic.norm_eq_zpow_neg_valuation hcast, Padic.valuation_ratCast,
      zpow_le_zpow_iff_right₀ hp]
    simp only [neg_le_neg_iff, hq, false_or]

end Prime

section Thirteen

local instance : Fact (Nat.Prime 13) := ⟨by decide⟩

/-- The 13² norm condition implies the paper's valuation condition. -/
theorem congruent13Sq_of_padic_norm_le (m : ℚ)
    (hclose : ‖((m : ℚ_[13]) - ((7401 : ℚ) / 2399 : ℚ_[13]))‖ ≤
      (13 : ℝ) ^ (-2 : ℤ)) : Congruent13Sq m := by
  have h := (padic_norm_ratCast_le_zpow_iff (p := 13)
    (m - (7401 : ℚ) / 2399) 2).1 (by norm_cast at hclose ⊢)
  rcases h with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · exact Or.inr h

/-- An open ball of radius 1/13 gives the required 13² congruence. -/
theorem congruent13Sq_of_padic_norm_lt (m : ℚ)
    (hclose : ‖((m : ℚ_[13]) - ((7401 : ℚ) / 2399 : ℚ_[13]))‖ <
      (13 : ℝ) ^ (-1 : ℤ)) : Congruent13Sq m := by
  apply congruent13Sq_of_padic_norm_le m
  exact (Padic.norm_lt_pow_iff_norm_le_pow_sub_one _ (-1)).1 hclose

/-- The 13² congruence neighborhood used for the torsion argument is open. -/
theorem isOpen_torsionBall :
    IsOpen {x : ℚ_[13] | ‖x - ((7401 : ℚ) / 2399 : ℚ_[13])‖ <
      (13 : ℝ) ^ (-1 : ℤ)} :=
  isOpen_lt (continuous_norm.comp (continuous_id.sub continuous_const)) continuous_const

/-- The 13² congruence neighborhood contains the base parameter. -/
theorem torsionBall_mem_nhds :
    {x : ℚ_[13] | ‖x - ((7401 : ℚ) / 2399 : ℚ_[13])‖ <
      (13 : ℝ) ^ (-1 : ℤ)} ∈ 𝓝 ((7401 : ℚ) / 2399 : ℚ_[13]) := by
  apply isOpen_torsionBall.mem_nhds
  simp only [sub_self, norm_zero, Set.mem_ofPred_eq]
  exact zpow_pos (by norm_num) _

end Thirteen

end Z2Z4Rank6
