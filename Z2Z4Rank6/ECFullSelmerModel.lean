module

public import Z2Z4Rank6.ECDescentLocal
public import Z2Z4Rank6.TwoDescent
public import Mathlib.Data.Int.Sqrt

@[expose] public section

/-!
# An explicit split two-Selmer model

The full two-descent homogeneous spaces for the split cubic with roots
`0,-r2,-r3`, following Silverman, *The Arithmetic of Elliptic Curves*, second
edition, Chapter X, Section 1, and Cremona, *Algorithms for Modular Elliptic
Curves*, Section 3.6. This file defines local-solubility conditions.
The concrete curve data are Jaswal, Lemma 4.1(b), DOI 10.5281/zenodo.23437117.
-/

namespace Z2Z4Rank6

abbrev ECFullTriple := ℤ × ℤ × ℤ

/-- The intersection of two quadrics representing a split full two-covering. -/
def SplitCoverSoluble {K : Type*} [CommRing K]
    (d1 d2 d3 r2 r3 : K) : Prop :=
  ∃ z : Fin 4 → K, (∃ i, z i ≠ 0) ∧
    d2*(z 1)^2-d1*(z 0)^2 = r2*(z 3)^2 ∧
    d3*(z 2)^2-d1*(z 0)^2 = r3*(z 3)^2

def SplitCoverEverywhereLocallySoluble (d : ECFullTriple) (r2 r3 : ℤ) : Prop :=
  SplitCoverSoluble (d.1 : ℝ) (d.2.1 : ℝ) (d.2.2 : ℝ) (r2 : ℝ) (r3 : ℝ) ∧
    ∀ (p : ℕ) [Fact p.Prime],
      SplitCoverSoluble (d.1 : ℚ_[p]) (d.2.1 : ℚ_[p]) (d.2.2 : ℚ_[p])
        (r2 : ℚ_[p]) (r3 : ℚ_[p])

/-- Canonical squarefree integer representatives of the full two-descent
classes: product a square and the associated intersection locally soluble. -/
def fullTwoSelmerTriples (r2 r3 : ℤ) : Set ECFullTriple :=
  {d | Squarefree d.1 ∧ Squarefree d.2.1 ∧ Squarefree d.2.2 ∧
    d.1 ∣ r2*r3 ∧ d.2.1 ∣ r2*(r2-r3) ∧ d.2.2 ∣ r3*(r2-r3) ∧
    IsSquare (d.1*d.2.1*d.2.2) ∧ SplitCoverEverywhereLocallySoluble d r2 r3}

/-- The same explicit classes in the rational squareclass vector space. -/
def fullTwoSelmerClasses (r2 r3 : ℤ) : Set (RatSquareClassAdd × RatSquareClassAdd) :=
  (fun d : ECFullTriple => (squareClass (d.1 : ℚ),squareClass (d.2.1 : ℚ))) ''
    fullTwoSelmerTriples r2 r3

def intSquareTest (z : ℤ) : Bool := decide (Int.sqrt z*Int.sqrt z = z)

theorem intSquareTest_iff (z : ℤ) : intSquareTest z = true ↔ IsSquare z := by
  rw [intSquareTest, decide_eq_true_eq]
  constructor
  · intro h
    exact ⟨Int.sqrt z,h.symm⟩
  · rintro ⟨r,hr⟩
    exact (Int.exists_mul_self z).1 ⟨r,hr.symm⟩

/-- The finite square residues used for kernel checking the local tests. -/
def squareResidues (M : ℕ) : List (ZMod M) :=
  ((List.range M).map (fun n : ℕ => (n : ZMod M)^2)).dedup

theorem square_mem_squareResidues (M : ℕ) [NeZero M] (z : ZMod M) :
    z^2 ∈ squareResidues M := by
  rw [squareResidues, List.mem_dedup]
  apply (List.mem_map (f := fun n : ℕ => (n : ZMod M)^2)).mpr
  refine ⟨z.val,List.mem_range.mpr (ZMod.val_lt z),?_⟩
  rw [ZMod.natCast_zmod_val]

/-- A normalized projective residue solution has one coordinate equal to 1.
Only its four square values need to be enumerated. -/
def splitCoverResiduePossible (M : ℕ) (d : ECFullTriple) : Bool :=
  (squareResidues M).any (fun a =>
  (squareResidues M).any (fun b =>
  (squareResidues M).any (fun c =>
  (squareResidues M).any (fun t => decide
    ((a=1 ∨ b=1 ∨ c=1 ∨ t=1) ∧
      (d.2.1 : ZMod M)*b-(d.1 : ZMod M)*a=729*t ∧
      (d.2.2 : ZMod M)*c-(d.1 : ZMod M)*a=484*t)))))

end Z2Z4Rank6
