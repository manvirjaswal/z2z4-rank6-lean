module

public import Z2Z4Rank6.LocalGroups

@[expose] public section

/-!
# Infinitely many rational points in simultaneous local neighborhoods

The finite product of compact groups in the proof of Proposition 6.2 of
M. Jaswal, *Infinitely many elliptic curves with torsion Z/2Z × Z/4Z and rank
at least six*, DOI 10.5281/zenodo.23437117.
-/

namespace Z2Z4Rank6

noncomputable section

open Set Filter Topology
open scoped Topology

local instance localProductPadicDecidableEq (p : ℕ) [Fact p.Prime] :
    DecidableEq ℚ_[p] := Classical.decEq _

/-- Every product of neighborhoods of the local images of c0 contains
infinitely many diagonally embedded rational points. The two hypotheses are published theorems. -/
theorem infinite_simultaneous_local_neighborhood
    (hSilvermanVII34 : OddPrimeTorsionIntegrality) (hLocal : LocalEllipticTopology)
    (U : (i : Fin 7) → Set (ECLocal (localPrime i)).toAffine.Point)
    (hU : ∀ i : Fin 7, letI := ecLocalTopology hLocal (localPrime i)
      U i ∈ 𝓝 (ecPointToLocal (localPrime i) ecC0)) :
    {P : RationalPoints EC | ∀ i, ecPointToLocal (localPrime i) P ∈ U i}.Infinite := by
  let (i : Fin 7) : TopologicalSpace (ECLocal (localPrime i)).toAffine.Point :=
    ecLocalTopology hLocal (localPrime i)
  let (i : Fin 7) : CompactSpace (ECLocal (localPrime i)).toAffine.Point :=
    ecLocalTopology_compact hLocal (localPrime i)
  let (i : Fin 7) : IsTopologicalAddGroup (ECLocal (localPrime i)).toAffine.Point :=
    ecLocalTopology_group hLocal (localPrime i)
  let : Infinite (RationalPoints EC) := ec_infinite hSilvermanVII34
  let Ω : Set LocalProduct := {g | ∀ i, g i ∈ U i}
  have hΩ : Ω ∈ 𝓝 (ecDiagonal ecC0) := by
    have hEach : ∀ i : Fin 7,
        {g : LocalProduct | g i ∈ U i} ∈ 𝓝 (ecDiagonal ecC0) := by
      intro i
      exact ((continuous_apply i).tendsto (ecDiagonal ecC0)).eventually (hU i)
    simpa only [Ω, Set.ofPred_forall] using Filter.iInter_mem.mpr hEach
  exact infinite_preimage_nhds_of_injective ecDiagonal ecDiagonal_injective ecC0 hΩ

end

end Z2Z4Rank6
