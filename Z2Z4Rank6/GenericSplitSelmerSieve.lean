module

public import Z2Z4Rank6.ECFullSupportRefinement

@[expose] public section

/-!
# Generic finite local tests for split two-coverings

These necessary tests apply to arbitrary integral root differences r2,r3.
The locally soluble intersection of quadrics is normalized in Q_p,
then reduced to Z/p^k using Mathlib's p-adic integer residue map.
-/

namespace Z2Z4Rank6

/-- A normalized projective square-residue test for arbitrary split cubics. -/
def splitCoverResiduePossibleFor (M : ℕ) (r2 r3 : ℤ) (d : ECFullTriple) : Bool :=
  (squareResidues M).any (fun a =>
  (squareResidues M).any (fun b =>
  (squareResidues M).any (fun c =>
  (squareResidues M).any (fun t => decide
    ((a=1 ∨ b=1 ∨ c=1 ∨ t=1) ∧
      (d.2.1 : ZMod M)*b-(d.1 : ZMod M)*a=(r2 : ZMod M)*t ∧
      (d.2.2 : ZMod M)*c-(d.1 : ZMod M)*a=(r3 : ZMod M)*t)))))

/-- Every p-adic covering point passes the finite local test. -/
theorem splitCover_local_implies_residue_test_for {p : ℕ} [Fact p.Prime]
    (k : ℕ) (d : ECFullTriple) (r2 r3 : ℤ)
    (h : SplitCoverSoluble (d.1 : ℚ_[p]) (d.2.1 : ℚ_[p])
      (d.2.2 : ℚ_[p]) (r2 : ℚ_[p]) (r3 : ℚ_[p])) :
    splitCoverResiduePossibleFor (p^k) r2 r3 d = true := by
  obtain ⟨z,⟨i,hi⟩,h1,h2⟩ := splitCover_integral_normalization_general d r2 r3 h
  let q : Fin 4 → ZMod (p^k) := fun j => PadicInt.toZModPow k (z j)
  simp only [splitCoverResiduePossibleFor, List.any_eq_true, decide_eq_true_eq]
  refine ⟨(q 0)^2,square_mem_squareResidues _ _,
    (q 1)^2,square_mem_squareResidues _ _,
    (q 2)^2,square_mem_squareResidues _ _,
    (q 3)^2,square_mem_squareResidues _ _,?_,?_,?_⟩
  · have hq : q i = 1 := by simp [q,hi]
    fin_cases i <;> simp_all
  · have hm := congrArg (PadicInt.toZModPow k) h1
    simpa only [map_sub,map_mul,map_pow,map_intCast] using hm
  · have hm := congrArg (PadicInt.toZModPow k) h2
    simpa only [map_sub,map_mul,map_pow,map_intCast] using hm

/-- A failed finite local test is a proved obstruction to everywhere
local solubility of the corresponding split two-covering. -/
theorem splitCover_not_everywhere_of_residue_test_false {p : ℕ} [Fact p.Prime]
    (k : ℕ) (d : ECFullTriple) (r2 r3 : ℤ)
    (h : splitCoverResiduePossibleFor (p^k) r2 r3 d = false) :
    ¬ SplitCoverEverywhereLocallySoluble d r2 r3 := by
  intro hlocal
  have ht := splitCover_local_implies_residue_test_for k d r2 r3 (hlocal.2 p)
  rw [h] at ht
  contradiction

end Z2Z4Rank6
