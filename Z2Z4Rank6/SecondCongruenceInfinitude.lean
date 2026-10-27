import Z2Z4Rank6.SecondLocalProduct
import Z2Z4Rank6.SecondCongruenceSections
import Z2Z4Rank6.PadicResidue

/-!
# Infinitely many second-family points satisfying seven local conditions

The theta-neighborhood of Remark 8.2 and the six-prime coordinate
congruences hold simultaneously on an infinite set of G2 rational
points. The hypotheses are the torsion-integrality and local-topology theorems. The proof follows
the compact-group congruence method.
-/
namespace Z2Z4Rank6
noncomputable section
open Set Filter Topology
open scoped Topology

local instance secondCongruencePadicDecidableEq (p : ℕ) [Fact p.Prime] :
    DecidableEq ℚ_[p] := Classical.decEq _

def secondThetaRadius (i : Fin 7) : ℝ := if i=0 then (3 : ℝ)^(-5 : ℤ) else 1

theorem secondThetaRadius_pos (i : Fin 7) : 0<secondThetaRadius i := by
  unfold secondThetaRadius
  split
  · exact zpow_pos (by norm_num) _
  · norm_num

theorem secondLocalPrime_succ (i : Fin 6) :
    secondLocalPrime i.succ=SecondReductionData.primes i := by
  fin_cases i <;> rfl

theorem secondThetaRadius_succ (i : Fin 6) : secondThetaRadius i.succ=1 := by
  simp [secondThetaRadius]

def secondLocalRationalSet : Set (RationalPoints J2) :=
  {P | ∀i : Fin 7,secondJ2PointToLocal (secondLocalPrime i) P ∈
    secondAllCoordinatesNeighborhood (secondLocalPrime i) (secondThetaRadius i) 1}

theorem infinite_secondLocalRationalSet
    (hSilvermanVII34 : OddPrimeTorsionIntegrality) (hLocal : LocalEllipticTopology) :
    secondLocalRationalSet.Infinite := by
  apply second_infinite_simultaneous_local_neighborhood hSilvermanVII34 hLocal
  intro i
  exact secondAllCoordinatesNeighborhood_mem_nhds hLocal (secondLocalPrime i)
    (secondThetaRadius i) 1 (secondThetaRadius_pos i) (by norm_num)

theorem secondLocalToG2_coordinates (x y : ℚ) (h : J2.toAffine.Nonsingular x y)
    (hchart : secondJacobianQuarticChart (.some x y h)) :
    secondG2Coordinates (x,y)=secondG2PointCoordinates (secondLocalToG2 (.some x y h)) := by
  rw [secondLocalToG2,dite_eq_left hchart]
  rfl

theorem secondCongruentAt_of_coordinate_bounds (i : Fin 6) (P : SecondFamily.G2Point ℚ)
    (hb : ∀j : Fin 4,‖((secondG2PointCoordinates P j : ℚ) : ℚ_[SecondReductionData.primes i])-
      ((secondG2PointCoordinates SecondReductionData.basePoint j : ℚ) :
        ℚ_[SecondReductionData.primes i])‖<1) : SecondCongruentAt i P := by
  have h0 := residue_eq_of_padic_norm_sub_lt_one P.W SecondReductionData.basePoint.W
    (second_base_coordinates_integral i).1 (hb 0)
  have h1 := residue_eq_of_padic_norm_sub_lt_one P.s1 SecondReductionData.basePoint.s1
    (second_base_coordinates_integral i).2.1 (hb 1)
  have h2 := residue_eq_of_padic_norm_sub_lt_one P.s2 SecondReductionData.basePoint.s2
    (second_base_coordinates_integral i).2.2.1 (hb 2)
  have h3 := residue_eq_of_padic_norm_sub_lt_one P.s3 SecondReductionData.basePoint.s3
    (second_base_coordinates_integral i).2.2.2 (hb 3)
  exact ⟨h0.1,h1.1,h2.1,h3.1,h0.2,h1.2,h2.2,h3.2⟩

theorem secondLocalToG2_mem_congruenceSet (P : RationalPoints J2)
    (hchart : secondJacobianQuarticChart P) (hP : P ∈ secondLocalRationalSet) :
    secondLocalToG2 P ∈ SecondCongruenceSet := by
  cases P with
  | zero => exact hchart.elim
  | some x y h =>
    intro i
    have hb := secondAllCoordinatesNeighborhood_some_bounds (secondLocalPrime i.succ)
      (secondThetaRadius i.succ) 1 x y h (hP i.succ)
    have hb' : ∀j : Fin 4,‖((secondG2Coordinates (x,y) j : ℚ) : ℚ_[SecondReductionData.primes i])-
        ((secondG2PointCoordinates SecondReductionData.basePoint j : ℚ) :
          ℚ_[SecondReductionData.primes i])‖<1 := hb.2
    rw [secondLocalToG2_coordinates x y h hchart] at hb'
    exact secondCongruentAt_of_coordinate_bounds i _ hb'

theorem secondLocalToG2_mem_thetaSet (P : RationalPoints J2)
    (hchart : secondJacobianQuarticChart P) (hP : P ∈ secondLocalRationalSet) :
    secondLocalToG2 P ∈ secondThetaNeighborhoodSet := by
  cases P with
  | zero => exact hchart.elim
  | some x y h =>
    have hb := secondAllCoordinatesNeighborhood_some_bounds (secondLocalPrime 0)
      (secondThetaRadius 0) 1 x y h (hP 0)
    have hb' : ‖((secondQuarticTheta x y : ℚ) : ℚ_[3])-(857/140 : ℚ_[3])‖<
        (3 : ℝ)^(-5 : ℤ) := hb.1
    exact secondLocalToG2_mem_neighborhood x y h hchart (secondThetaNear3_of_padic_bound _ hb')

/-- The printed torsion neighborhood and all six coordinate congruences. -/
def secondCongruenceThetaSet : Set (SecondFamily.G2Point ℚ) :=
  secondThetaNeighborhoodSet ∩ SecondCongruenceSet

theorem infinite_secondCongruenceThetaSet
    (hSilvermanVII34 : OddPrimeTorsionIntegrality) (hLocal : LocalEllipticTopology) :
    secondCongruenceThetaSet.Infinite := by
  have hA := infinite_secondLocalRationalSet hSilvermanVII34 hLocal
  have hf : (secondLocalRationalSet \ {P | secondJacobianQuarticChart P}).Finite :=
    secondJacobianQuarticChart_complement_finite.subset (fun _ h => h.2)
  have hg : (secondLocalRationalSet ∩ {P | secondJacobianQuarticChart P}).Infinite :=
    hA.inter_of_finite_sdiff hf
  have him := hg.image (secondLocalToG2_injOn.mono inter_subset_right)
  apply him.mono
  rintro _ ⟨P,⟨hP,hchart⟩,rfl⟩
  exact ⟨secondLocalToG2_mem_thetaSet P hchart hP,
    secondLocalToG2_mem_congruenceSet P hchart hP⟩

end
end Z2Z4Rank6
