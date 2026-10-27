module

public import Z2Z4Rank6.Basic
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Homeomorph.Lemmas

@[expose] public section

/-!
# The local-topology hypothesis

The hypothesis is the usual compact topological group structure on
the points of an elliptic curve over a p-adic field, with its ordinary affine
coordinate chart.

References:
* J. S. Milne, *Elliptic Curves*, second edition, World Scientific, 2021,
  Chapter II, Section 4, proof of Theorem 4.1(a), p. 63. The topology there is
  induced by the quotient topology on the projective plane.
  https://jmilne.org/math/Books/EC2.pdf
* T. Fisher, *Elliptic Curves*, Cambridge Part III, Lent 2023, notes by
  L. Tomczak, proof of Lemma 9.8, p. 29: compactness and continuity of the
  group operations for an elliptic curve over a finite extension of Q_p.
  https://math.berkeley.edu/~ltomczak/notes/Lent2023/EC_Notes.pdf

The open-chart clause spells out the affine chart of the projective topology.
The statements are generic in the elliptic curve and prime.
-/

namespace Z2Z4Rank6

open Topology

/-- Ordinary affine solutions with their subspace topology from the coefficient field squared. -/
abbrev AffineEquationPoints {K : Type*} [Field K] (W : WeierstrassCurve K) :=
  {xy : K × K // W.toAffine.Equation xy.1 xy.2}

/-- The affine coordinate chart in Mathlib's elliptic point type. -/
def affinePointEmbedding {K : Type*} [Field K] (W : WeierstrassCurve K)
    [W.IsElliptic] (xy : AffineEquationPoints W) : W.toAffine.Point :=
  WeierstrassCurve.Affine.Point.mk xy.property

/-- The point group of this p-adic elliptic curve admits a compact
topological-group topology for which the ordinary affine chart is an open embedding. -/
def LocalEllipticTopologyAt {p : ℕ} [Fact p.Prime]
    (W : WeierstrassCurve ℚ_[p]) [W.IsElliptic] : Prop := by
  classical
  exact ∃ T : TopologicalSpace W.toAffine.Point,
    letI := T
    CompactSpace W.toAffine.Point ∧ IsTopologicalAddGroup W.toAffine.Point ∧
      IsOpenEmbedding (affinePointEmbedding W)

/-- The published local-topology theorem is available for every prime
and every elliptic Weierstrass equation over Q_p. -/
def LocalEllipticTopology : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve ℚ_[p]) (hW : W.IsElliptic),
    letI := hW
    LocalEllipticTopologyAt W

section AffineLocus

variable {K : Type*} [Field K] (W : WeierstrassCurve K) [W.IsElliptic]

/-- An affine point is different from the group identity at infinity. -/
theorem affinePointEmbedding_ne_zero (xy : AffineEquationPoints W) :
    affinePointEmbedding W xy ≠ 0 :=
  WeierstrassCurve.Affine.Point.some_ne_zero _

/-- The ordinary affine coordinate chart identifies precisely the nonidentity points. -/
theorem range_affinePointEmbedding :
    Set.range (affinePointEmbedding W) = {P : W.toAffine.Point | P ≠ 0} := by
  ext P
  constructor
  · rintro ⟨xy, rfl⟩
    exact affinePointEmbedding_ne_zero W xy
  · intro hP
    cases P with
    | zero => exact (hP rfl).elim
    | some x y h => exact ⟨⟨(x, y), h.1⟩, rfl⟩

end AffineLocus

section Chart

variable {K : Type*} [Field K] [TopologicalSpace K]
  (W : WeierstrassCurve K) [W.IsElliptic] [TopologicalSpace W.toAffine.Point]

/-- A supplied open chart gives a homeomorphism onto the affine locus. -/
noncomputable def affineChartHomeomorph
    (hchart : IsOpenEmbedding (affinePointEmbedding W)) :
    AffineEquationPoints W ≃ₜ Set.range (affinePointEmbedding W) :=
  hchart.isEmbedding.toHomeomorph

/-- Coordinates on the affine locus are continuous in the supplied topology. -/
theorem affine_coordinates_continuous
    (hchart : IsOpenEmbedding (affinePointEmbedding W)) :
    Continuous (fun P : Set.range (affinePointEmbedding W) =>
      ((affineChartHomeomorph W hchart).symm P).val) :=
  continuous_subtype_val.comp (affineChartHomeomorph W hchart).symm.continuous

/-- A coordinate neighborhood determines a neighborhood of the corresponding
point in the complete elliptic point group. -/
theorem affine_neighborhood
    (hchart : IsOpenEmbedding (affinePointEmbedding W))
    (xy : AffineEquationPoints W) {U : Set (K × K)}
    (hU : U ∈ 𝓝 xy.val) :
    affinePointEmbedding W '' (Subtype.val ⁻¹' U : Set (AffineEquationPoints W)) ∈
      𝓝 (affinePointEmbedding W xy) := by
  apply hchart.image_mem_nhds.mpr
  exact (continuous_subtype_val.tendsto xy).eventually hU

end Chart

end Z2Z4Rank6
