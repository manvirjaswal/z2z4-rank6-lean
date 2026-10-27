import Z2Z4Rank6.BaseCurve
import Z2Z4Rank6.LocalTopology
import Z2Z4Rank6.CompactRecurrence
import Z2Z4Rank6.ReductionData
import Mathlib.Topology.Algebra.Group.Compact

/-!
# The rational group inside the seven local groups

The compact-group construction in Proposition 6.2 of M. Jaswal,
*Infinitely many elliptic curves with torsion Z/2Z × Z/4Z and rank at least six*,
DOI 10.5281/zenodo.23437117. The embeddings use Mathlib's extension maps on
elliptic-curve point groups.
-/

namespace Z2Z4Rank6

noncomputable section

open scoped Topology
open Topology

local instance (p : ℕ) [Fact p.Prime] : DecidableEq ℚ_[p] := Classical.decEq _

/-- The seven primes used for torsion and independence. -/
def localPrime : Fin 7 → ℕ := Fin.cases 13 ReductionData.primes

instance localPrime_isPrime (i : Fin 7) : Fact (localPrime i).Prime := by
  constructor
  fin_cases i <;> decide

/-- The base curve over one of the local fields. -/
abbrev ECLocal (p : ℕ) [Fact p.Prime] : WeierstrassCurve ℚ_[p] :=
  EC.baseChange ℚ_[p]

instance ecLocal_isElliptic (p : ℕ) [Fact p.Prime] : (ECLocal p).IsElliptic := by
  exact inferInstanceAs (EC.map (algebraMap ℚ ℚ_[p])).IsElliptic

/-- The usual rational-to-local extension homomorphism. -/
noncomputable def ecPointToLocal (p : ℕ) [Fact p.Prime] :
    RationalPoints EC →+ (ECLocal p).toAffine.Point := by
  exact WeierstrassCurve.Affine.Point.map (W' := EC)
    (Algebra.ofId ℚ ℚ_[p] : ℚ →ₐ[ℚ] ℚ_[p])

theorem ecPointToLocal_injective (p : ℕ) [Fact p.Prime] :
    Function.Injective (ecPointToLocal p) := by
  exact WeierstrassCurve.Affine.Point.map_injective (W' := EC)
    (Algebra.ofId ℚ ℚ_[p] : ℚ →ₐ[ℚ] ℚ_[p])

/-- The standard local topology given by the published theorem. -/
@[instance_reducible]
def ecLocalTopology (hLocal : LocalEllipticTopology) (p : ℕ) [Fact p.Prime] :
    TopologicalSpace (ECLocal p).toAffine.Point :=
  Classical.choose (hLocal p (ECLocal p) inferInstance)

theorem ecLocalTopology_compact (hLocal : LocalEllipticTopology) (p : ℕ) [Fact p.Prime] :
    letI := ecLocalTopology hLocal p
    CompactSpace (ECLocal p).toAffine.Point :=
  (Classical.choose_spec (hLocal p (ECLocal p) inferInstance)).1

theorem ecLocalTopology_group (hLocal : LocalEllipticTopology) (p : ℕ) [Fact p.Prime] :
    letI := ecLocalTopology hLocal p
    IsTopologicalAddGroup (ECLocal p).toAffine.Point :=
  (Classical.choose_spec (hLocal p (ECLocal p) inferInstance)).2.1

theorem ecLocalTopology_chart (hLocal : LocalEllipticTopology) (p : ℕ) [Fact p.Prime] :
    letI := ecLocalTopology hLocal p
    IsOpenEmbedding (affinePointEmbedding (ECLocal p)) :=
  (Classical.choose_spec (hLocal p (ECLocal p) inferInstance)).2.2

/-- The product of the seven local elliptic point groups. -/
abbrev LocalProduct := (i : Fin 7) → (ECLocal (localPrime i)).toAffine.Point

/-- The diagonal embedding of the rational point group. -/
def ecDiagonal : RationalPoints EC →+ LocalProduct where
  toFun P i := ecPointToLocal (localPrime i) P
  map_zero' := by ext i; exact map_zero _
  map_add' P Q := by ext i; exact map_add _ P Q

theorem ecDiagonal_injective : Function.Injective ecDiagonal := by
  intro P Q h
  exact ecPointToLocal_injective (localPrime 0) (congrFun h 0)

end

end Z2Z4Rank6
