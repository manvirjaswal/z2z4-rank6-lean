module

public import Z2Z4Rank6.LocalGroups
public import Z2Z4Rank6.BaseLocalMaps
public import Z2Z4Rank6.BasePointMap
public import Z2Z4Rank6.PadicResidue

@[expose] public section

/-!
# Coordinate neighborhoods on the local base curve

The open neighborhoods used in Proposition 6.2 of M. Jaswal,
*Infinitely many elliptic curves with torsion Z/2Z × Z/4Z and rank at least six*,
DOI 10.5281/zenodo.23437117. The coordinate map is explicit;
the compact topology comes from `LocalEllipticTopology`.
-/

namespace Z2Z4Rank6

noncomputable section

open Topology
open scoped Topology

local instance (p : ℕ) [Fact p.Prime] : DecidableEq ℚ_[p] := Classical.decEq _

def localTripleBall (p : ℕ) [Fact p.Prime] (r : ℝ) : Set (ℚ_[p] × (ℚ_[p] × ℚ_[p])) :=
  {z | ‖z.1 - (7401/2399 : ℚ_[p])‖ < r ∧
    ‖z.2.1 - (88235/2399 : ℚ_[p])‖ < r ∧
    ‖z.2.2 - (86835/2399 : ℚ_[p])‖ < r}

theorem localTripleBall_isOpen (p : ℕ) [Fact p.Prime] (r : ℝ) :
    IsOpen (localTripleBall p r) := by
  have hM : Continuous (fun z : ℚ_[p] × (ℚ_[p] × ℚ_[p]) =>
      ‖z.1 - (7401/2399 : ℚ_[p])‖) := by fun_prop
  have hU : Continuous (fun z : ℚ_[p] × (ℚ_[p] × ℚ_[p]) =>
      ‖z.2.1 - (88235/2399 : ℚ_[p])‖) := by fun_prop
  have hV : Continuous (fun z : ℚ_[p] × (ℚ_[p] × ℚ_[p]) =>
      ‖z.2.2 - (86835/2399 : ℚ_[p])‖) := by fun_prop
  exact (isOpen_lt hM continuous_const).inter
    ((isOpen_lt hU continuous_const).inter (isOpen_lt hV continuous_const))

theorem localTripleBall_mem_nhds (p : ℕ) [Fact p.Prime] (r : ℝ) (hr : 0 < r) :
    localTripleBall p r ∈
      𝓝 ((7401/2399, (88235/2399, 86835/2399)) : ℚ_[p] × (ℚ_[p] × ℚ_[p])) := by
  apply (localTripleBall_isOpen p r).mem_nhds
  simpa only [localTripleBall, Set.mem_ofPred_eq, sub_self, norm_zero, and_self] using hr

theorem ecLocal_equation_iff (p : ℕ) [Fact p.Prime] (x y : ℚ_[p]) :
    (ECLocal p).toAffine.Equation x y ↔
      y^2 = x^3+x^2-137620*x-10504000 := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp [ECLocal, EC, WeierstrassCurve.baseChange, WeierstrassCurve.map]
  ring_nf

def ecLocalC0 (p : ℕ) [Fact p.Prime] : AffineEquationPoints (ECLocal p) :=
  ⟨ecCoordinatesC0, (ecLocal_equation_iff p _ _).mpr ecCoordinatesC0_equation⟩

theorem ecLocalC0_embedding (p : ℕ) [Fact p.Prime] :
    affinePointEmbedding (ECLocal p) (ecLocalC0 p) = ecPointToLocal p ecC0 := by
  simp only [affinePointEmbedding, ecLocalC0, ecPointToLocal, ecC0,
    WeierstrassCurve.Affine.Point.mk, WeierstrassCurve.Affine.Point.map]
  congr 1 <;> norm_num [ecCoordinatesC0]

/-- The affine coordinate preimage of a triple ball, viewed in the full local
elliptic point group via its open affine chart. -/
def localCurveNeighborhood (_hLocal : LocalEllipticTopology) (p : ℕ) [Fact p.Prime]
    (r : ℝ) : Set (ECLocal p).toAffine.Point :=
  affinePointEmbedding (ECLocal p) ''
    {xy : AffineEquationPoints (ECLocal p) | ecCoordinatesToC xy.val ∈ localTripleBall p r}

theorem localCurveNeighborhood_mem_nhds (hLocal : LocalEllipticTopology)
    (p : ℕ) [Fact p.Prime] (r : ℝ) (hr : 0 < r) :
    letI := ecLocalTopology hLocal p
    localCurveNeighborhood hLocal p r ∈ 𝓝 (ecPointToLocal p ecC0) := by
  let := ecLocalTopology hLocal p
  have hcoord : ecCoordinatesToC ⁻¹' localTripleBall p r ∈
      𝓝 (ecCoordinatesC0 (K := ℚ_[p])) := by
    apply ecCoordinatesToC_continuousAt_c0.preimage_mem_nhds
    rw [ecCoordinatesToC_c0]
    exact localTripleBall_mem_nhds p r hr
  have he := affine_neighborhood (ECLocal p) (ecLocalTopology_chart hLocal p)
    (ecLocalC0 p) hcoord
  rw [ecLocalC0_embedding] at he
  exact he

theorem localCurveNeighborhood_ne_zero (hLocal : LocalEllipticTopology)
    (p : ℕ) [Fact p.Prime] (r : ℝ) {P : (ECLocal p).toAffine.Point}
    (hP : P ∈ localCurveNeighborhood hLocal p r) : P ≠ 0 := by
  obtain ⟨xy, _, rfl⟩ := hP
  exact affinePointEmbedding_ne_zero (ECLocal p) xy

theorem localCurveNeighborhood_some_formula_bounds (hLocal : LocalEllipticTopology)
    (p : ℕ) [Fact p.Prime] (r : ℝ)
    (x y : ℚ) (h : EC.toAffine.Nonsingular x y)
    (hP : ecPointToLocal p (.some x y h) ∈ localCurveNeighborhood hLocal p r) :
    ecCoordinatesToC ((x : ℚ_[p]), (y : ℚ_[p])) ∈ localTripleBall p r := by
  obtain ⟨xy, hxy, he⟩ := hP
  have hc : xy.val = ((x : ℚ_[p]), (y : ℚ_[p])) := by
    change WeierstrassCurve.Affine.Point.some xy.val.1 xy.val.2 _ =
      WeierstrassCurve.Affine.Point.some (x : ℚ_[p]) (y : ℚ_[p]) _ at he
    exact Prod.ext (WeierstrassCurve.Affine.Point.some.inj he).1
      (WeierstrassCurve.Affine.Point.some.inj he).2
  change ecCoordinatesToC xy.val ∈ localTripleBall p r at hxy
  rw [hc] at hxy
  exact hxy

theorem localCurveNeighborhood_some_bounds (hLocal : LocalEllipticTopology)
    (p : ℕ) [Fact p.Prime] (r : ℝ)
    (x y : ℚ) (h : EC.toAffine.Nonsingular x y) (hx : x+82 ≠ 0)
    (hP : ecPointToLocal p (.some x y h) ∈ localCurveNeighborhood hLocal p r) :
    ‖((ecToCPoint (.some x y h)).m : ℚ_[p]) - (7401/2399 : ℚ_[p])‖ < r ∧
    ‖((ecToCPoint (.some x y h)).u : ℚ_[p]) - (88235/2399 : ℚ_[p])‖ < r ∧
    ‖((ecToCPoint (.some x y h)).v : ℚ_[p]) - (86835/2399 : ℚ_[p])‖ < r := by
  have hbounds := localCurveNeighborhood_some_formula_bounds hLocal p r x y h hP
  have he := map_ecToCPoint_some_coordinates (Rat.castHom ℚ_[p]) x y h hx
  change (((ecToCPoint (.some x y h)).m : ℚ_[p]),
    (((ecToCPoint (.some x y h)).u : ℚ_[p]), ((ecToCPoint (.some x y h)).v : ℚ_[p]))) =
      ecCoordinatesToC ((x : ℚ_[p]), (y : ℚ_[p])) at he
  rw [← he] at hbounds
  exact hbounds

end

end Z2Z4Rank6
