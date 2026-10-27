module

public import Z2Z4Rank6.ReductionCheckRank
public import Z2Z4Rank6.TorsionCongruence
public import Z2Z4Rank6.JInvariant

@[expose] public section

/-!
# The explicit family of desired fibers

The congruence set and its arithmetic properties from Proposition 6.2 of
M. Jaswal, *Infinitely many elliptic curves with torsion Z/2Z × Z/4Z and rank
at least six*, DOI 10.5281/zenodo.23437117.

Infinitude is proved separately by the compact-group construction. The arithmetic assertions below
use the theorems of Mazur and good reduction.
-/

namespace Z2Z4Rank6

/-- Exactly the set S in Proposition 6.2, with the zero-difference valuation
convention written explicitly. -/
def congruenceSet : Set CPoint :=
  {c | Congruent13Sq c.m ∧ SixPrimeCongruences c}

/-- Every point in S gives the exact torsion and six independent rational
points printed in Proposition 6.2. -/
theorem desiredCurve_of_mem_congruenceSet
    (hMazur : MazurTorsionTheorem) (hReduction : GoodReductionHomomorphisms)
    (c : CPoint) (hc : c ∈ congruenceSet) : DesiredCurve (X c.m) := by
  have hT := X_torsion_of_congruent13 hMazur c.m hc.1
  exact ⟨X_good_of_congruent13 c.m hc.1, hT,
    rankAtLeastSix_of_congruences hReduction c hc.2 hT⟩

/-- Once the printed congruence set is infinite, its finite j-fibers give the
main theorem. -/
theorem theorem11_of_infinite_congruenceSet
    (hMazur : MazurTorsionTheorem) (hReduction : GoodReductionHomomorphisms)
    (hS : congruenceSet.Infinite) : Theorem11 :=
  theorem11_of_infinite_desired_fibers congruenceSet hS
    (desiredCurve_of_mem_congruenceSet hMazur hReduction)

end Z2Z4Rank6
