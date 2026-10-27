module

public import Z2Z4Rank6.TwistSelmerDataNecessary
public import Z2Z4Rank6.FiniteKernelReconstruction
public import Z2Z4Rank6.SplitHighDifferenceObstruction

@[expose] public section

/-!
# Exhaustive free-bit decoding for the split-covering sieve

The finite list enumerates every F₂ free vector by a proved induction.
Combined with a matrix identity and canonical coefficient
reconstruction, it contains every locally soluble canonical covering.
Source application: Jaswal, Proposition 5.2, DOI 10.5281/zenodo.23437117.
-/

namespace Z2Z4Rank6.TwistSelmer

open scoped BigOperators
noncomputable section

def binaryVectors : (n : ℕ) → List (Fin n → ZMod 2)
  | 0 => [Fin.elim0]
  | n+1 => (binaryVectors n).flatMap (fun v => [Fin.cons 0 v,Fin.cons 1 v])

theorem mem_binaryVectors (n : ℕ) (v : Fin n → ZMod 2) : v∈binaryVectors n := by
  induction n with
  | zero =>
    have hv : v=Fin.elim0 := by funext i; exact Fin.elim0 i
    simp [binaryVectors,hv]
  | succ n ih =>
    have hhead : v 0=0 ∨ v 0=1 := (by decide +kernel : ∀ z : ZMod 2, z=0 ∨ z=1) (v 0)
    have htail := ih (Fin.tail v)
    apply List.mem_flatMap.mpr
    refine ⟨Fin.tail v,htail,?_⟩
    rcases hhead with h0 | h1
    · have hv : Fin.cons 0 (Fin.tail v)=v := by rw [←h0]; exact Fin.cons_self_tail v
      simp [hv]
    · have hv : Fin.cons 1 (Fin.tail v)=v := by rw [←h1]; exact Fin.cons_self_tail v
      simp [hv]

/-- The exact finite pool decoded from the certified free coordinates. -/
def decodedPool {s f : ℕ} (ps : Fin s → ℕ)
    (N : Matrix (Fin (BitDimension s)) (Fin f) (ZMod 2)) : List ECFullTriple :=
  (binaryVectors f).map (fun v => candidate ps (N.mulVec v))

theorem mem_decodedPool {s f : ℕ} (ps : Fin s → ℕ)
    (N : Matrix (Fin (BitDimension s)) (Fin f) (ZMod 2)) (v : Fin f → ZMod 2) :
    candidate ps (N.mulVec v)∈decodedPool ps N :=
  List.mem_map.mpr ⟨v,mem_binaryVectors f v,rfl⟩

/-- Canonical coverings with certified kernel constraints lie in the
exhaustive finite decoding pool. -/
theorem fullCover_mem_decodedPool {s f t : ℕ} (ps : Fin s → ℕ)
    (hinj : Function.Injective ps) (hprime : ∀ i, (ps i).Prime)
    (r2 r3 : ℤ) (hr3 : 0<r3) (hr23 : r3<r2) (k : ℕ)
    (hp : ∀ c, rootProduct r2 r3 c∣((∏ i, ps i : ℕ) : ℤ)^k)
    (M : Matrix (Fin t) (Fin (BitDimension s)) (ZMod 2))
    (N : Matrix (Fin (BitDimension s)) (Fin f) (ZMod 2))
    (P : Matrix (Fin f) (Fin (BitDimension s)) (ZMod 2))
    (L : Matrix (Fin (BitDimension s)) (Fin t) (ZMod 2))
    (hcert : (1 : Matrix (Fin (BitDimension s)) (Fin (BitDimension s)) (ZMod 2))=N*P+L*M)
    (hkernel : ∀ d∈fullTwoSelmerTriples r2 r3, M.mulVec (bitVector ps d)=0)
    (d : ECFullTriple) (hd : d∈fullTwoSelmerTriples r2 r3) : d∈decodedPool ps N := by
  have hs := coefficient_squarefree_of_mem d r2 r3 hd
  have hdiv := coefficient_support_bound ps d r2 r3 k hp hd
  have hpos := splitCover_second_pos_of_ordered_differences d r2 r3 hr3 hr23
    (hs 0).ne_zero (hs 1).ne_zero (hs 2).ne_zero hd.2.2.2.2.2.2.1 hd.2.2.2.2.2.2.2
  have hdec := candidate_bitVector ps hinj hprime d k hs hdiv hpos hd.2.2.2.2.2.2.1
  have hb := FiniteKernelReconstruction.kernel_reconstruction M N P L hcert
    (bitVector ps d) (hkernel d hd)
  rw [hb] at hdec
  exact hdec ▸ mem_decodedPool ps N (P.mulVec (bitVector ps d))

/-- A small Euler check equivalent to a quadratic-residue condition. -/
def squareBool (p : ℕ) (n : ℤ) : Bool := decide (modularParity p n=0)

theorem squareBool_iff (p : ℕ) [Fact p.Prime] (n : ℤ) :
    squareBool p n=true ↔ IsSquare (n : ZMod p) := by
  rw [squareBool,decide_eq_true_eq,modularParity_eq_zero_iff]

/-- The high-difference obstruction tests only a residue modulo p after the
proved p⁵ primitive divisibility argument. -/
def highDifferenceTest (p : ℕ) (S : ℤ) (d : ECFullTriple) : Bool :=
  if (p : ℤ)∣d.2.2 ∧ ¬(p : ℤ)∣d.2.1 then squareBool p (-d.2.1*S)
  else if (p : ℤ)∣d.2.1 ∧ ¬(p : ℤ)∣d.2.2 then squareBool p (d.2.2*S)
  else true

theorem highDifferenceTest_of_mem {p : ℕ} [Fact p.Prime] (S r2 r3 : ℤ)
    (hr : r3-r2=(p : ℤ)^4*S) (d : ECFullTriple)
    (hd : d∈fullTwoSelmerTriples r2 r3) : highDifferenceTest p S d=true := by
  unfold highDifferenceTest
  split_ifs with h3 h2
  · apply (squareBool_iff p _).mpr
    exact splitCover_high_difference_isSquare d r2 r3 S hd.1 hd.2.2.1 h3.1 h3.2 hr hd.2.2.2.2.2.2.2
  · apply (squareBool_iff p _).mpr
    exact splitCover_high_difference_swap_isSquare d r2 r3 S hd.1 hd.2.1 h2.1 h2.2 hr hd.2.2.2.2.2.2.2
  · rfl


end
end Z2Z4Rank6.TwistSelmer
