import Z2Z4Rank6.CountingExponentTransport
import Mathlib.Data.Set.Card

/-!
# Removing finite exceptional sets from height counts

Elementary counting support for Jaswal Remark 6.3,
DOI 10.5281/zenodo.23437117.
A finite exceptional set changes each bounded count by at most its size,
so a positive logarithmic counting exponent is preserved.
-/
namespace Z2Z4Rank6.FiniteRemovalCounting
noncomputable section
open Filter

variable {α : Type*}

theorem ncard_sdiff_sandwich (S E : Set α) (hS : S.Finite) (hE : E.Finite) :
    (S\E).ncard≤S.ncard ∧ S.ncard≤(S\E).ncard+E.ncard :=
  ⟨Set.ncard_le_ncard Set.sdiff_subset hS,Set.ncard_le_ncard_sdiff_add_ncard S E hE⟩

/-- Removing a finite set preserves a positive exponent for any
sequence of finite bounded sets. -/
theorem counting_exponent_sdiff (S : ℕ→Set α) (hS : ∀ H,(S H).Finite)
    (E : Set α) (hE : E.Finite) (a : ℝ)
    (hexp : HasLogarithmicCountingExponent (fun H => (S H).ncard) a) (ha : 0<a) :
    HasLogarithmicCountingExponent (fun H => (S H\E).ncard) a := by
  apply hexp.of_eventually_add_sandwich (C:=E.ncard) ha
  exact Filter.Eventually.of_forall (fun H => ncard_sdiff_sandwich (S H) E (hS H) hE)

/-- The height-bounded set of a natural-valued height. -/
def heightSet (h : α→ℕ) (H : ℕ) : Set α := {x | h x≤H}

def count (h : α→ℕ) (H : ℕ) : ℕ := (heightSet h H).ncard

def countOutside (h : α→ℕ) (E : Set α) (H : ℕ) : ℕ := (heightSet h H\E).ncard

theorem heightSetOutside_finite (h : α→ℕ) (hfin : ∀ H,(heightSet h H).Finite)
    (E : Set α) (H : ℕ) : (heightSet h H\E).Finite := (hfin H).sdiff

/-- Finite-removal theorem for bounded-height counts. -/
theorem height_counting_exponent_outside (h : α→ℕ) (hfin : ∀ H,(heightSet h H).Finite)
    (E : Set α) (hE : E.Finite) (a : ℝ)
    (hexp : HasLogarithmicCountingExponent (count h) a) (ha : 0<a) :
    HasLogarithmicCountingExponent (countOutside h E) a :=
  counting_exponent_sdiff (heightSet h) hfin E hE a hexp ha

end
end Z2Z4Rank6.FiniteRemovalCounting
