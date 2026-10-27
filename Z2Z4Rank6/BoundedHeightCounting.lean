module

public import Z2Z4Rank6.CountingExponentTransport

@[expose] public section

/-!
# Bounded sets under comparable natural heights

The set-theoretic counting bridge for Jaswal Remark 6.3,
DOI 10.5281/zenodo.23437117. Positive-power height inequalities imply
bounded-set inclusions, finiteness and logarithmic-exponent
transport.
-/

namespace Z2Z4Rank6.BoundedHeightCounting
noncomputable section
open Filter

variable {α : Type*}

def boundedSet (h : α→ℕ) (H : ℕ) : Set α := {x | h x≤H}

def count (h : α→ℕ) (H : ℕ) : ℕ := (boundedSet h H).ncard

/-- Integer bound corresponding to c*n^d at most H. -/
def rootIndex (c : ℝ) (d H : ℕ) : ℕ :=
  powerHeightIndex ((1/c)^((d : ℝ)⁻¹)) ((d : ℝ)⁻¹) H

/-- Exact inversion of a positive power, including H=0 and n=0. -/
theorem le_rootIndex_iff {c : ℝ} {d : ℕ} (hc : 0<c) (hd : 0<d) (n H : ℕ) :
    n≤rootIndex c d H ↔ c*(n : ℝ)^d≤(H : ℝ) := by
  have hdR : 0<(d : ℝ) := by exact_mod_cast hd
  have hFactor : (1/c)^((d : ℝ)⁻¹)*(H : ℝ)^((d : ℝ)⁻¹)=
      ((H : ℝ)/c)^((d : ℝ)⁻¹) := by
    rw [one_div,div_eq_mul_inv,Real.mul_rpow (Nat.cast_nonneg H) (inv_nonneg.mpr hc.le)]
    exact mul_comm _ _
  unfold rootIndex powerHeightIndex
  rw [hFactor,Nat.le_floor_iff (Real.rpow_nonneg (div_nonneg (Nat.cast_nonneg H) hc.le) _),
    Real.le_rpow_inv_iff_of_pos (Nat.cast_nonneg n)
      (div_nonneg (Nat.cast_nonneg H) hc.le) hdR,Real.rpow_natCast,le_div_iff₀ hc]
  rw [mul_comm]

theorem lower_subset {h k : α→ℕ} {U : ℝ} {d : ℕ}
    (hU : 0<U) (hd : 0<d)
    (hUpper : ∀ x,(k x : ℝ)≤U*(h x : ℝ)^d) (H : ℕ) :
    boundedSet h (rootIndex U d H)⊆boundedSet k H := by
  intro x hx
  have hBound : U*(h x : ℝ)^d≤(H : ℝ) := (le_rootIndex_iff hU hd (h x) H).mp hx
  have hReal := (hUpper x).trans hBound
  exact_mod_cast hReal

theorem upper_subset {h k : α→ℕ} {L : ℝ} {d : ℕ}
    (hL : 0<L) (hd : 0<d)
    (hLower : ∀ x,L*(h x : ℝ)^d≤(k x : ℝ)) (H : ℕ) :
    boundedSet k H⊆boundedSet h (rootIndex L d H) := by
  intro x hx
  have hReal : (k x : ℝ)≤(H : ℝ) := by exact_mod_cast hx
  exact (le_rootIndex_iff hL hd (h x) H).mpr ((hLower x).trans hReal)

/-- Finiteness is transferred through the upper bounded-set inclusion. -/
theorem boundedSet_finite_of_power_lower {h k : α→ℕ} {L : ℝ} {d : ℕ}
    (hFinite : ∀ H,(boundedSet h H).Finite) (hL : 0<L) (hd : 0<d)
    (hLower : ∀ x,L*(h x : ℝ)^d≤(k x : ℝ)) (H : ℕ) :
    (boundedSet k H).Finite :=
  (hFinite (rootIndex L d H)).subset (upper_subset hL hd hLower H)

/-- Cardinal inequalities from the two power-height comparisons. -/
theorem count_bounds {h k : α→ℕ} {L U : ℝ} {d : ℕ}
    (hFinite : ∀ H,(boundedSet h H).Finite) (hL : 0<L) (hU : 0<U) (hd : 0<d)
    (hBounds : ∀ x,L*(h x : ℝ)^d≤(k x : ℝ) ∧ (k x : ℝ)≤U*(h x : ℝ)^d)
    (H : ℕ) :
    count h (rootIndex U d H)≤count k H ∧ count k H≤count h (rootIndex L d H) := by
  have hKFinite := boundedSet_finite_of_power_lower hFinite hL hd (fun x => (hBounds x).1) H
  exact ⟨Set.ncard_le_ncard (lower_subset hU hd (fun x => (hBounds x).2) H) hKFinite,
    Set.ncard_le_ncard (upper_subset hL hd (fun x => (hBounds x).1) H)
      (hFinite (rootIndex L d H))⟩

/-- Comparable positive-power natural heights have the same positive
logarithmic count exponent. Every bounded set for the new height is finite. -/
theorem counting_of_power_comparison {h k : α→ℕ} {a L U : ℝ} {d : ℕ}
    (hFinite : ∀ H,(boundedSet h H).Finite)
    (hCount : HasLogarithmicCountingExponent (count h) a) (ha : 0<a)
    (hL : 0<L) (hU : 0<U) (hd : 0<d)
    (hBounds : ∀ x,L*(h x : ℝ)^d≤(k x : ℝ) ∧ (k x : ℝ)≤U*(h x : ℝ)^d) :
    (∀ H,(boundedSet k H).Finite) ∧ HasLogarithmicCountingExponent (count k) a := by
  have hdR : 0<(d : ℝ) := by exact_mod_cast hd
  refine ⟨boundedSet_finite_of_power_lower hFinite hL hd (fun x => (hBounds x).1),?_⟩
  apply hCount.of_eventually_powerHeight_sandwich ha
    (Real.rpow_pos_of_pos (div_pos zero_lt_one hU) _)
    (inv_pos.mpr hdR) (Real.rpow_pos_of_pos (div_pos zero_lt_one hL) _) (inv_pos.mpr hdR)
  exact Eventually.of_forall (count_bounds hFinite hL hU hd hBounds)

/-- Bounded count restricted to a specified set of objects. -/
def restrictedCount (h : α→ℕ) (S : Set α) (H : ℕ) : ℕ :=
  (boundedSet h H∩S).ncard

/-- Deleting a finite exceptional set preserves the positive
logarithmic count exponent and finiteness of every bounded set. -/
theorem counting_on_cofinite_set {h : α→ℕ} {S : Set α} {a : ℝ}
    (hFinite : ∀ H,(boundedSet h H).Finite)
    (hCount : HasLogarithmicCountingExponent (count h) a) (ha : 0<a)
    (hExceptional : Sᶜ.Finite) :
    (∀ H,(boundedSet h H∩S).Finite) ∧
      HasLogarithmicCountingExponent (restrictedCount h S) a := by
  refine ⟨fun H => (hFinite H).inter_of_left S,?_⟩
  apply hCount.of_eventually_add_sandwich (C:=Sᶜ.ncard) ha
  apply Eventually.of_forall
  intro H
  refine ⟨Set.ncard_le_ncard Set.inter_subset_left (hFinite H),?_⟩
  simpa only [count,restrictedCount,Set.sdiff_compl] using
    Set.ncard_le_ncard_sdiff_add_ncard (boundedSet h H) Sᶜ hExceptional

end
end Z2Z4Rank6.BoundedHeightCounting
