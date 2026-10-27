module

public import Z2Z4Rank6.SecondJacobianBasic
public import Mathlib.LinearAlgebra.Dimension.Constructions

@[expose] public section

/-! Four printed complete-descent values and their independence on
J_G2, Jaswal Theorem 8.1(a), DOI 10.5281/zenodo.23437117. -/
namespace Z2Z4Rank6
set_option maxRecDepth 4096

def secondJacobianRepresentatives : Fin 4 → ℚ×ℚ :=
  ![(2,-2),(197,7*23*197),(2*197*233,-2*197*233),(29*197*233,-29*197*233)]
def secondJacobianRawValues : Fin 4 → ℚ×ℚ :=
  ![(153606507912,-272004488),(800494729925/4,184980680325/4),
    (144360113832,-9518398568),(153878512400,-671898241/153878512400)]
def secondJacobianCoordinateFactors : Fin 4 → ℚ×ℚ :=
  ![(277134,11662),(63745/2,2415/2),(1254,322),(340,25921/452583860)]
noncomputable def secondJacobianPairClass(q:ℚ×ℚ):RatSquareClassAdd×RatSquareClassAdd :=
  (squareClass q.1,squareClass q.2)
noncomputable def secondJacobianBasis : Fin 4 → RatSquareClassAdd×RatSquareClassAdd :=
  fun i=>secondJacobianPairClass (secondJacobianRepresentatives i)

theorem secondJacobian_eq_split :
    J2=splitWeierstrass (-102809641014) 51068871386 51740769627 := by
  ext <;> norm_num [J2,splitWeierstrass]

theorem secondJacobian_coordinate_factors(i:Fin 4):
    (secondJacobianRawValues i).1=(secondJacobianRepresentatives i).1*(secondJacobianCoordinateFactors i).1^2 ∧
    (secondJacobianRawValues i).2=(secondJacobianRepresentatives i).2*(secondJacobianCoordinateFactors i).2^2 := by
  fin_cases i <;> norm_num [secondJacobianRawValues,secondJacobianRepresentatives,secondJacobianCoordinateFactors]

private theorem secondJacobian_raw_squareclasses(i:Fin 4):
    secondJacobianPairClass (secondJacobianRawValues i)=secondJacobianBasis i := by
  apply Prod.ext
  · apply squareClass_eq_of_factor _ _ (secondJacobianCoordinateFactors i).1
    · fin_cases i <;> norm_num [secondJacobianRawValues]
    · fin_cases i <;> norm_num [secondJacobianRepresentatives]
    · fin_cases i <;> norm_num [secondJacobianCoordinateFactors]
    · exact (secondJacobian_coordinate_factors i).1
  · apply squareClass_eq_of_factor _ _ (secondJacobianCoordinateFactors i).2
    · fin_cases i <;> norm_num [secondJacobianRawValues]
    · fin_cases i <;> norm_num [secondJacobianRepresentatives]
    · fin_cases i <;> norm_num [secondJacobianCoordinateFactors]
    · exact (secondJacobian_coordinate_factors i).2

theorem secondJacobian_descent_coordinates(i:Fin 4):
    completeDescentCoordinates J2 (-102809641014) 51068871386 51740769627
      (secondJacobianFourPoints i)=secondJacobianBasis i := by
  rw [←secondJacobian_raw_squareclasses i]
  fin_cases i <;> norm_num [secondJacobianFourPoints,secondJacobianP1,secondJacobianP2,
    secondJacobianFour,secondJacobianTwo,WeierstrassCurve.Affine.Point.mk,
    completeDescentCoordinates,secondJacobianRawValues,secondJacobianPairClass]

private theorem valuation_nat_zero_or_one {p n : ℕ} [Fact p.Prime]
    (hn : n ≠ 0) (hp2 : ¬p ^ 2 ∣ n) :
    padicValNat p n = if p ∣ n then 1 else 0 := by
  split_ifs with hdiv
  · have hlow : 1 ≤ padicValNat p n := by
      apply (padicValNat_dvd_iff_le hn).1
      simpa only [pow_one] using hdiv
    have hhigh : ¬2 ≤ padicValNat p n := by
      intro hh
      exact hp2 ((padicValNat_dvd_iff_le hn).2 hh)
    omega
  · exact padicValNat.eq_zero_of_not_dvd hdiv

local instance secondJacobianDescentPrimeTwo : Fact (Nat.Prime 2) := ⟨by decide⟩
local instance secondJacobianDescentPrimeSeven : Fact (Nat.Prime 7) := ⟨by decide⟩
local instance secondJacobianDescentPrimeTwentyNine : Fact (Nat.Prime 29) := ⟨by decide⟩
local instance secondJacobianDescentPrime233 : Fact (Nat.Prime 233) := ⟨by norm_num⟩

noncomputable def secondJacobianParity : (RatSquareClassAdd×RatSquareClassAdd) →+ (Fin 4 → ZMod 2) where
  toFun q := ![squareClassValuation 29 q.1,squareClassValuation 7 q.2,
    squareClassValuation 233 q.1,squareClassValuation 2 q.1]
  map_zero' := by ext i;fin_cases i <;> simp
  map_add' q r := by ext i;fin_cases i <;> simp

def secondJacobianParityVectors : Fin 4 → Fin 4 → ZMod 2 :=
  ![![0,0,0,1],![0,1,0,0],![0,0,1,1],![1,0,1,0]]

theorem secondJacobian_parity_values(i:Fin 4):
    secondJacobianParity (secondJacobianBasis i)=secondJacobianParityVectors i := by
  ext j
  fin_cases i <;> fin_cases j <;>
    simp only [secondJacobianParity,secondJacobianBasis,secondJacobianPairClass,
      secondJacobianRepresentatives,secondJacobianParityVectors,AddMonoidHom.coe_mk,ZeroHom.coe_mk]
  all_goals norm_num
  all_goals rw [squareClassValuation_apply _ _ (by norm_num)]
  all_goals norm_num [padicValRat_def,padicValInt]
  all_goals try rw [valuation_nat_zero_or_one (by decide) (by decide)]
  all_goals norm_num

theorem secondJacobian_basis_independent : LinearIndependent (ZMod 2) secondJacobianBasis := by
  apply Fintype.linearIndependent_iff.mpr
  intro n hn
  have hm:∑i,n i • secondJacobianParityVectors i=0 := by
    have hh:=congrArg secondJacobianParity hn
    simpa only [map_sum,ZMod.map_smul,secondJacobian_parity_values,map_zero] using hh
  have h0:=congrFun hm 0
  have h1:=congrFun hm 1
  have h2:=congrFun hm 2
  have h3:=congrFun hm 3
  norm_num [Fin.sum_univ_succ,secondJacobianParityVectors] at h0 h1 h2 h3
  intro i
  fin_cases i <;> simp_all

end Z2Z4Rank6
