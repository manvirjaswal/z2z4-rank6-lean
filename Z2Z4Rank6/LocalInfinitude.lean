module

public import Z2Z4Rank6.LocalProduct
public import Z2Z4Rank6.LocalNeighborhoods
public import Z2Z4Rank6.CongruenceSet

@[expose] public section

/-!
# Infinitude of the printed congruence set

Proposition 6.2 of M. Jaswal, *Infinitely many elliptic curves with torsion
Z/2Z × Z/4Z and rank at least six*,
DOI 10.5281/zenodo.23437117. We shrink the neighborhood at 13 by also
restricting u and v; the resulting infinite subset lies in exactly the
congruence set printed in the proposition.
-/

namespace Z2Z4Rank6

noncomputable section

open Set Filter Topology
open scoped Topology

local instance localInfinitudePadicDecidableEq (p : ℕ) [Fact p.Prime] :
    DecidableEq ℚ_[p] := Classical.decEq _

def localRadius (i : Fin 7) : ℝ := if i=0 then (13 : ℝ)^(-1 : ℤ) else 1

theorem localRadius_pos (i : Fin 7) : 0 < localRadius i := by
  unfold localRadius
  split
  · exact zpow_pos (by norm_num) _
  · norm_num

theorem localPrime_succ (i : Fin 6) : localPrime i.succ=ReductionData.primes i := by
  fin_cases i <;> rfl

theorem localRadius_succ (i : Fin 6) : localRadius i.succ=1 := by
  simp [localRadius]

/-- The rational EC-points whose local images lie in the chosen neighborhoods. -/
def localRationalSet (hLocal : LocalEllipticTopology) : Set (RationalPoints EC) :=
  {P | ∀ i : Fin 7,
    ecPointToLocal (localPrime i) P ∈
      localCurveNeighborhood hLocal (localPrime i) (localRadius i)}

theorem infinite_localRationalSet
    (hSilvermanVII34 : OddPrimeTorsionIntegrality) (hLocal : LocalEllipticTopology) :
    (localRationalSet hLocal).Infinite := by
  apply infinite_simultaneous_local_neighborhood hSilvermanVII34 hLocal
  intro i
  exact localCurveNeighborhood_mem_nhds hLocal (localPrime i) (localRadius i)
    (localRadius_pos i)

/-- On the regular rational chart, all seven local neighborhoods imply the
exact printed 13² and six-prime congruences. -/
theorem ecToCPoint_mem_congruenceSet (hLocal : LocalEllipticTopology)
    (P : RationalPoints EC) (hchart : ecQuarticChart P)
    (hP : P ∈ localRationalSet hLocal) : ecToCPoint P ∈ congruenceSet := by
  cases P with
  | zero => exact hchart.elim
  | some x y h =>
    change x+82 ≠ 0 at hchart
    constructor
    · have hb := localCurveNeighborhood_some_bounds hLocal (localPrime 0)
        (localRadius 0) x y h hchart (hP 0)
      apply congruent13Sq_of_padic_norm_lt
      norm_num [localPrime, localRadius] at hb ⊢
      exact hb.1
    · intro i
      have hb := localCurveNeighborhood_some_bounds hLocal (localPrime i.succ)
        (localRadius i.succ) x y h hchart (hP i.succ)
      have hb' :
          ‖((ecToCPoint (.some x y h)).m : ℚ_[ReductionData.primes i]) - (7401/2399)‖ < 1 ∧
          ‖((ecToCPoint (.some x y h)).u : ℚ_[ReductionData.primes i]) - (88235/2399)‖ < 1 ∧
          ‖((ecToCPoint (.some x y h)).v : ℚ_[ReductionData.primes i]) - (86835/2399)‖ < 1 := by
        exact hb
      have hm := residue_eq_of_padic_norm_sub_lt_one
        (ecToCPoint (.some x y h)).m baseC0.m (baseC0_integral i).1
        (by norm_num [baseC0]; exact hb'.1)
      have hu := residue_eq_of_padic_norm_sub_lt_one
        (ecToCPoint (.some x y h)).u baseC0.u (baseC0_integral i).2.1
        (by norm_num [baseC0]; exact hb'.2.1)
      have hv := residue_eq_of_padic_norm_sub_lt_one
        (ecToCPoint (.some x y h)).v baseC0.v (baseC0_integral i).2.2
        (by norm_num [baseC0]; exact hb'.2.2)
      exact ⟨hm.1,hu.1,hv.1,hm.2,hu.2,hv.2⟩

/-- The congruence set S in Proposition 6.2 is infinite. The hypotheses are Silverman's
torsion-integrality theorem and the standard local
topology theorem. -/
theorem infinite_congruenceSet
    (hSilvermanVII34 : OddPrimeTorsionIntegrality) (hLocal : LocalEllipticTopology) :
    congruenceSet.Infinite := by
  have hA := infinite_localRationalSet hSilvermanVII34 hLocal
  have hfinite : (localRationalSet hLocal \ {P | ecQuarticChart P}).Finite :=
    ecQuarticChart_complement_finite.subset (fun _ h => h.2)
  have hgood : (localRationalSet hLocal ∩ {P | ecQuarticChart P}).Infinite :=
    hA.inter_of_finite_sdiff hfinite
  have himage := hgood.image (ecToCPoint_injOn.mono inter_subset_right)
  apply himage.mono
  rintro _ ⟨P,⟨hP,hchart⟩,rfl⟩
  exact ecToCPoint_mem_congruenceSet hLocal P hchart hP

end

end Z2Z4Rank6
