import Z2Z4Rank6.LocalInfinitude
import Z2Z4Rank6.JDegree

/-!
# Infinitely many rational elliptic curves of torsion Z/2 × Z/4 and rank at least six

Theorem 1.1 of M. Jaswal, *Infinitely many elliptic curves with torsion
Z/2Z × Z/4Z and rank at least six*,
DOI 10.5281/zenodo.23437117.

The proof follows the paper's explicit congruence family and printed matrix.
The four hypotheses below are published theorems, stated with exact references.
-/

namespace Z2Z4Rank6

/-- Infinitely many rational elliptic curves have torsion subgroup
isomorphic to Z/2 × Z/4 and six integer-linearly independent rational points,
and infinitely many distinct rational j-invariants occur among them.

The hypotheses are Mazur's rational torsion classification, Silverman's
odd-prime torsion-integrality theorem, the good-reduction group-homomorphism
theorem, and the compact local elliptic-group topology theorem. -/
theorem theorem_1_1
    (hMazur : MazurTorsionTheorem)
    (hSilvermanVII34 : OddPrimeTorsionIntegrality)
    (hReduction : GoodReductionHomomorphisms)
    (hLocal : LocalEllipticTopology) : Theorem11 :=
  theorem11_of_infinite_congruenceSet hMazur hReduction
    (infinite_congruenceSet hSilvermanVII34 hLocal)

/-- Proposition 6.2: the exact printed congruence set is infinite, and every
one of its fibers has the required torsion and independent points. -/
theorem proposition_6_2
    (hMazur : MazurTorsionTheorem)
    (hSilvermanVII34 : OddPrimeTorsionIntegrality)
    (hReduction : GoodReductionHomomorphisms)
    (hLocal : LocalEllipticTopology) :
    congruenceSet.Infinite ∧ ∀ c ∈ congruenceSet, DesiredCurve (X c.m) :=
  ⟨infinite_congruenceSet hSilvermanVII34 hLocal,
    desiredCurve_of_mem_congruenceSet hMazur hReduction⟩

end Z2Z4Rank6
