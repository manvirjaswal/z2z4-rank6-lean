module

public import Z2Z4Rank6.SecondG2LocalMaps
public import Z2Z4Rank6.SecondLocalInfinitude

@[expose] public section

/-!
# Simultaneous local neighborhoods for the second Jacobian

The product uses 3 and the six reduction primes 41,47,59,67,79,97 from
Remark 8.2, DOI 10.5281/zenodo.23437117. Compact recurrence is applied to
Mathlib's elliptic point groups and field-extension homomorphisms.
-/
namespace Z2Z4Rank6
noncomputable section
open Set Filter Topology
open scoped Topology

local instance secondProductPadicDecidableEq (p : ℕ) [Fact p.Prime] :
    DecidableEq ℚ_[p] := Classical.decEq _

def secondLocalPrime : Fin 7 → ℕ := Fin.cases 3 SecondReductionData.primes
instance secondLocalPrime_isPrime (i : Fin 7) : Fact (secondLocalPrime i).Prime := by
  constructor
  fin_cases i <;> decide

abbrev SecondJ2Local (p : ℕ) [Fact p.Prime] : WeierstrassCurve ℚ_[p] :=
  J2.baseChange ℚ_[p]
instance secondJ2Local_isElliptic (p : ℕ) [Fact p.Prime] : (SecondJ2Local p).IsElliptic :=
  inferInstanceAs (J2.map (algebraMap ℚ ℚ_[p])).IsElliptic

def secondJ2PointToLocal (p : ℕ) [Fact p.Prime] :
    RationalPoints J2 →+ (SecondJ2Local p).toAffine.Point :=
  WeierstrassCurve.Affine.Point.map (W':=J2)
    (Algebra.ofId ℚ ℚ_[p] : ℚ →ₐ[ℚ] ℚ_[p])

theorem secondJ2PointToLocal_injective (p : ℕ) [Fact p.Prime] :
    Function.Injective (secondJ2PointToLocal p) :=
  WeierstrassCurve.Affine.Point.map_injective (W':=J2)
    (Algebra.ofId ℚ ℚ_[p] : ℚ →ₐ[ℚ] ℚ_[p])

@[instance_reducible]
def secondJ2LocalTopology (hLocal : LocalEllipticTopology) (p : ℕ) [Fact p.Prime] :
    TopologicalSpace (SecondJ2Local p).toAffine.Point :=
  Classical.choose (hLocal p (SecondJ2Local p) inferInstance)

theorem secondJ2LocalTopology_compact (hLocal : LocalEllipticTopology) (p : ℕ) [Fact p.Prime] :
    let := secondJ2LocalTopology hLocal p
    CompactSpace (SecondJ2Local p).toAffine.Point :=
  (Classical.choose_spec (hLocal p (SecondJ2Local p) inferInstance)).1

theorem secondJ2LocalTopology_group (hLocal : LocalEllipticTopology) (p : ℕ) [Fact p.Prime] :
    let := secondJ2LocalTopology hLocal p
    IsTopologicalAddGroup (SecondJ2Local p).toAffine.Point :=
  (Classical.choose_spec (hLocal p (SecondJ2Local p) inferInstance)).2.1

theorem secondJ2LocalTopology_chart (hLocal : LocalEllipticTopology) (p : ℕ) [Fact p.Prime] :
    let := secondJ2LocalTopology hLocal p
    IsOpenEmbedding (affinePointEmbedding (SecondJ2Local p)) :=
  (Classical.choose_spec (hLocal p (SecondJ2Local p) inferInstance)).2.2

theorem secondJ2Local_equation_iff (p : ℕ) [Fact p.Prime] (x y : ℚ_[p]) :
    (SecondJ2Local p).toAffine.Equation x y ↔
      y^2=(x+102809641014)*(x-51068871386)*(x-51740769627) := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp [SecondJ2Local,J2,WeierstrassCurve.baseChange,WeierstrassCurve.map]
  ring_nf

def secondJ2LocalC0 (p : ℕ) [Fact p.Prime] : AffineEquationPoints (SecondJ2Local p) :=
  ⟨secondJacobianCoordinatesC0,(secondJ2Local_equation_iff p _ _).mpr secondCoordinatesC0_equation⟩

theorem secondJ2LocalC0_embedding (p : ℕ) [Fact p.Prime] :
    affinePointEmbedding (SecondJ2Local p) (secondJ2LocalC0 p)=
      secondJ2PointToLocal p secondJacobianC0 := by
  simp only [affinePointEmbedding,secondJ2LocalC0,secondJ2PointToLocal,secondJacobianC0,
    WeierstrassCurve.Affine.Point.mk,WeierstrassCurve.Affine.Point.map]
  congr 1 <;> norm_num [secondJacobianCoordinatesC0]

def secondAllCoordinatesNeighborhood (p : ℕ) [Fact p.Prime] (rt rc : ℝ) :
    Set (SecondJ2Local p).toAffine.Point :=
  affinePointEmbedding (SecondJ2Local p) '' {xy : AffineEquationPoints (SecondJ2Local p) |
    ‖secondQuarticTheta xy.val.1 xy.val.2-(857/140 : ℚ_[p])‖ < rt ∧
    ∀j : Fin 4, ‖secondG2Coordinates xy.val j-
      ((secondG2PointCoordinates SecondReductionData.basePoint j : ℚ) : ℚ_[p])‖ < rc}

theorem secondAllCoordinatesNeighborhood_mem_nhds (hLocal : LocalEllipticTopology)
    (p : ℕ) [Fact p.Prime] (rt rc : ℝ) (hrt : 0<rt) (hrc : 0<rc) :
    let := secondJ2LocalTopology hLocal p
    secondAllCoordinatesNeighborhood p rt rc ∈ 𝓝 (secondJ2PointToLocal p secondJacobianC0) := by
  let := secondJ2LocalTopology hLocal p
  have hball (x : ℚ_[p]) (r : ℝ) (hr : 0<r) : {y : ℚ_[p] | ‖y-x‖<r} ∈ 𝓝 x := by
    apply (isOpen_lt (continuous_norm.comp (continuous_id.sub continuous_const)) continuous_const).mem_nhds
    change ‖x-x‖<r
    simpa only [sub_self,norm_zero] using hr
  have ht : {z : ℚ_[p]×ℚ_[p] | ‖secondQuarticTheta z.1 z.2-(857/140 : ℚ_[p])‖<rt}
      ∈ 𝓝 secondJacobianCoordinatesC0 := by
    have hb : {t : ℚ_[p] | ‖t-(857/140 : ℚ_[p])‖<rt} ∈
        𝓝 (secondQuarticTheta (secondJacobianCoordinatesC0 (K:=ℚ_[p])).1
          (secondJacobianCoordinatesC0 (K:=ℚ_[p])).2) := by
      rw [secondCoordinatesC0_theta]
      exact hball _ rt hrt
    exact (secondQuarticTheta_continuousAt _ secondCoordinatesC0_denom_ne_zero).preimage_mem_nhds hb
  have hg (j : Fin 4) : {z : ℚ_[p]×ℚ_[p] | ‖secondG2Coordinates z j-
      ((secondG2PointCoordinates SecondReductionData.basePoint j : ℚ) : ℚ_[p])‖<rc}
      ∈ 𝓝 secondJacobianCoordinatesC0 := by
    have hb : {t : ℚ_[p] | ‖t-
        ((secondG2PointCoordinates SecondReductionData.basePoint j : ℚ) : ℚ_[p])‖<rc} ∈
        𝓝 (secondG2Coordinates (secondJacobianCoordinatesC0 (K:=ℚ_[p])) j) := by
      rw [secondG2Coordinates_c0]
      exact hball _ rc hrc
    exact (secondG2Coordinates_continuousAt_c0 j).preimage_mem_nhds hb
  have hc := Filter.inter_mem ht (Filter.iInter_mem.mpr hg)
  have he := affine_neighborhood (SecondJ2Local p) (secondJ2LocalTopology_chart hLocal p)
    (secondJ2LocalC0 p) hc
  rw [secondJ2LocalC0_embedding] at he
  simpa only [secondAllCoordinatesNeighborhood,Set.preimage_inter,Set.preimage_iInter,
    Set.preimage_ofPred_eq,Set.ofPred_and,Set.ofPred_forall] using he

theorem secondAllCoordinatesNeighborhood_some_bounds (p : ℕ) [Fact p.Prime]
    (rt rc : ℝ) (x y : ℚ) (h : J2.toAffine.Nonsingular x y)
    (hP : secondJ2PointToLocal p (.some x y h) ∈ secondAllCoordinatesNeighborhood p rt rc) :
    ‖((secondQuarticTheta x y : ℚ) : ℚ_[p])-(857/140 : ℚ_[p])‖ < rt ∧
    ∀j : Fin 4, ‖((secondG2Coordinates (x,y) j : ℚ) : ℚ_[p])-
      ((secondG2PointCoordinates SecondReductionData.basePoint j : ℚ) : ℚ_[p])‖ < rc := by
  obtain ⟨xy,hxy,he⟩ := hP
  have hc : xy.val=((x : ℚ_[p]),(y : ℚ_[p])) := by
    change WeierstrassCurve.Affine.Point.some xy.val.1 xy.val.2 _=
      WeierstrassCurve.Affine.Point.some (x : ℚ_[p]) (y : ℚ_[p]) _ at he
    exact Prod.ext (WeierstrassCurve.Affine.Point.some.inj he).1
      (WeierstrassCurve.Affine.Point.some.inj he).2
  change ‖secondQuarticTheta xy.val.1 xy.val.2-(857/140 : ℚ_[p])‖<rt ∧
    ∀j : Fin 4, ‖secondG2Coordinates xy.val j-
      ((secondG2PointCoordinates SecondReductionData.basePoint j : ℚ) : ℚ_[p])‖<rc at hxy
  rw [hc] at hxy
  constructor
  · have hm := map_secondQuarticTheta (Rat.castHom ℚ_[p]) x y
    change ((secondQuarticTheta x y : ℚ) : ℚ_[p])=
      secondQuarticTheta (x : ℚ_[p]) (y : ℚ_[p]) at hm
    rw [←hm] at hxy
    exact hxy.1
  · intro j
    have hm := map_secondG2Coordinates (Rat.castHom ℚ_[p]) (x,y) j
    change ((secondG2Coordinates (x,y) j : ℚ) : ℚ_[p])=
      secondG2Coordinates ((x : ℚ_[p]),(y : ℚ_[p])) j at hm
    have hj := hxy.2 j
    rw [←hm] at hj
    exact hj

abbrev SecondLocalProduct := (i : Fin 7) → (SecondJ2Local (secondLocalPrime i)).toAffine.Point

def secondJ2Diagonal : RationalPoints J2 →+ SecondLocalProduct where
  toFun P i := secondJ2PointToLocal (secondLocalPrime i) P
  map_zero' := by ext i; exact map_zero _
  map_add' P Q := by ext i; exact map_add _ P Q

theorem secondJ2Diagonal_injective : Function.Injective secondJ2Diagonal := by
  intro P Q h
  exact secondJ2PointToLocal_injective (secondLocalPrime 0) (congrFun h 0)

theorem second_infinite_simultaneous_local_neighborhood
    (hSilvermanVII34 : OddPrimeTorsionIntegrality) (hLocal : LocalEllipticTopology)
    (U : (i : Fin 7) → Set (SecondJ2Local (secondLocalPrime i)).toAffine.Point)
    (hU : ∀i : Fin 7, letI := secondJ2LocalTopology hLocal (secondLocalPrime i)
      U i ∈ 𝓝 (secondJ2PointToLocal (secondLocalPrime i) secondJacobianC0)) :
    {P : RationalPoints J2 | ∀i,secondJ2PointToLocal (secondLocalPrime i) P ∈ U i}.Infinite := by
  let (i : Fin 7) : TopologicalSpace (SecondJ2Local (secondLocalPrime i)).toAffine.Point :=
    secondJ2LocalTopology hLocal (secondLocalPrime i)
  let (i : Fin 7) : CompactSpace (SecondJ2Local (secondLocalPrime i)).toAffine.Point :=
    secondJ2LocalTopology_compact hLocal (secondLocalPrime i)
  let (i : Fin 7) : IsTopologicalAddGroup (SecondJ2Local (secondLocalPrime i)).toAffine.Point :=
    secondJ2LocalTopology_group hLocal (secondLocalPrime i)
  let : Infinite (RationalPoints J2) := secondJacobian_infinite hSilvermanVII34
  let Ω : Set SecondLocalProduct := {g | ∀i,g i ∈ U i}
  have hΩ : Ω ∈ 𝓝 (secondJ2Diagonal secondJacobianC0) := by
    have hEach : ∀i : Fin 7,{g : SecondLocalProduct | g i ∈ U i} ∈ 𝓝 (secondJ2Diagonal secondJacobianC0) := by
      intro i
      exact ((continuous_apply i).tendsto (secondJ2Diagonal secondJacobianC0)).eventually (hU i)
    simpa only [Ω,Set.ofPred_forall] using Filter.iInter_mem.mpr hEach
  exact infinite_preimage_nhds_of_injective secondJ2Diagonal secondJ2Diagonal_injective secondJacobianC0 hΩ

end
end Z2Z4Rank6
