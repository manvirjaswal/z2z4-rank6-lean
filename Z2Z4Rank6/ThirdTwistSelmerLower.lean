import Z2Z4Rank6.ThirdTwistRankPoint
import Z2Z4Rank6.SplitTwoTorsion

/-! Independent rational descent classes on the four third-twist fibers. -/
namespace Z2Z4Rank6.ThirdTwist
noncomputable section
open scoped BigOperators

local instance prime263 : Fact (Nat.Prime 263) := ⟨by norm_num⟩
local instance prime83 : Fact (Nat.Prime 83) := ⟨by norm_num⟩
local instance prime47 : Fact (Nat.Prime 47) := ⟨by norm_num⟩

def differenceRepresentative : Fin 4→ℚ := ![2691846570,207402551886,207402551886,24484641853630]
def differenceSquareFactor : Fin 4→ℚ := ![20,4,4,20]
def detectingPrime : Fin 4→ℕ := ![263,83,83,47]

instance detectingPrime_prime (k : Fin 4) : Fact (detectingPrime k).Prime := by
  constructor
  fin_cases k <;> norm_num [detectingPrime]

local instance split_curve_elliptic (k : Fin 4) :
    (SplitTwoTorsion.curve (r2 k:ℚ) (r3 k:ℚ)).IsElliptic := by
  change (curve k).IsElliptic
  infer_instance

def torsionPoints (k : Fin 4) : Fin 2→RationalPoints (curve k) :=
  ![SplitTwoTorsion.first (r2 k:ℚ) (r3 k:ℚ),
    SplitTwoTorsion.second (r2 k:ℚ) (r3 k:ℚ)]

def torsionRepresentatives (k : Fin 4) : Fin 2→ℚ×ℚ :=
  ![(1,D k),(-(D k),differenceRepresentative k)]

def torsionRawValues (k : Fin 4) : Fin 2→ℚ×ℚ :=
  ![((r3 k:ℚ)/(r2 k:ℚ),(r2 k:ℚ)),
    (-(r2 k:ℚ),((r2 k:ℚ)-(r3 k:ℚ))/(r2 k:ℚ))]

def torsionSquareFactors (k : Fin 4) : Fin 2→ℚ×ℚ :=
  ![((B k:ℚ)/(A k:ℚ),(A k:ℚ)),
    ((A k:ℚ),differenceSquareFactor k/(A k:ℚ))]

def torsionClasses (k : Fin 4) (i : Fin 2) : RatSquareClassAdd×RatSquareClassAdd :=
  (squareClass (torsionRepresentatives k i).1,squareClass (torsionRepresentatives k i).2)

theorem torsion_square_factors (k : Fin 4) (i : Fin 2) :
    (torsionRawValues k i).1=(torsionRepresentatives k i).1*(torsionSquareFactors k i).1^2 ∧
    (torsionRawValues k i).2=(torsionRepresentatives k i).2*(torsionSquareFactors k i).2^2 := by
  fin_cases k <;> fin_cases i <;> norm_num [torsionRawValues,torsionRepresentatives,
    torsionSquareFactors,differenceRepresentative,differenceSquareFactor,r2,r3,D,A,B]

theorem torsion_raw_classes (k : Fin 4) (i : Fin 2) :
    (squareClass (torsionRawValues k i).1,squareClass (torsionRawValues k i).2)=
      torsionClasses k i := by
  apply Prod.ext
  · apply squareClass_eq_of_factor _ _ (torsionSquareFactors k i).1
    · fin_cases k <;> fin_cases i <;> norm_num [torsionRawValues,r2,r3,D,A,B]
    · fin_cases k <;> fin_cases i <;> norm_num [torsionRepresentatives,D,differenceRepresentative]
    · fin_cases k <;> fin_cases i <;> norm_num [torsionSquareFactors,A,B,differenceSquareFactor]
    · exact (torsion_square_factors k i).1
  · apply squareClass_eq_of_factor _ _ (torsionSquareFactors k i).2
    · fin_cases k <;> fin_cases i <;> norm_num [torsionRawValues,r2,r3,D,A,B]
    · fin_cases k <;> fin_cases i <;> norm_num [torsionRepresentatives,D,differenceRepresentative]
    · fin_cases k <;> fin_cases i <;> norm_num [torsionSquareFactors,A,B,differenceSquareFactor]
    · exact (torsion_square_factors k i).2

theorem torsion_descent_coordinates (k : Fin 4) (i : Fin 2) :
    completeDescentCoordinates (curve k) 0 (-(r2 k:ℚ)) (-(r3 k:ℚ)) (torsionPoints k i)=
      torsionClasses k i := by
  rw [←torsion_raw_classes k i]
  fin_cases k <;> fin_cases i <;>
    norm_num [torsionPoints,SplitTwoTorsion.first,SplitTwoTorsion.second,
      WeierstrassCurve.Affine.Point.mk,completeDescentCoordinates,torsionRawValues,r2,r3,D,A,B]

private theorem valuation_nat_zero_or_one {p n : ℕ} [Fact p.Prime]
    (hn : n≠0) (hp2 : ¬p^2∣n) : padicValNat p n=if p∣n then 1 else 0 := by
  split_ifs with hdiv
  · have hlo : 1≤padicValNat p n := by
      apply (padicValNat_dvd_iff_le hn).mp
      simpa only [pow_one] using hdiv
    have hhi : ¬2≤padicValNat p n := fun h => hp2 ((padicValNat_dvd_iff_le hn).mpr h)
    omega
  · exact padicValNat.eq_zero_of_not_dvd hdiv

def torsionParity (k : Fin 4) : (RatSquareClassAdd×RatSquareClassAdd)→+(Fin 2→ZMod 2) where
  toFun q := ![squareClassSign q.1,squareClassValuation (detectingPrime k) q.2]
  map_zero' := by ext i; fin_cases i <;> simp
  map_add' q r := by ext i; fin_cases i <;> simp

theorem torsion_parity_values (k : Fin 4) (i : Fin 2) :
    torsionParity k (torsionClasses k i)=![![0,1],![1,0]] i := by
  ext j
  fin_cases k <;> fin_cases i <;> fin_cases j <;>
    simp only [torsionParity,torsionClasses,torsionRepresentatives,D,differenceRepresentative,
      detectingPrime,AddMonoidHom.coe_mk,ZeroHom.coe_mk]
  all_goals simp (disch:=norm_num) only [squareClassValuation_apply,squareClassSign_apply]
  all_goals norm_num [padicValRat_def,padicValInt]
  all_goals try rw [valuation_nat_zero_or_one (by decide) (by decide)]
  all_goals norm_num

theorem torsion_classes_independent (k : Fin 4) : LinearIndependent (ZMod 2) (torsionClasses k) := by
  apply Fintype.linearIndependent_iff.mpr
  intro c hc
  have hh := congrArg (torsionParity k) hc
  simp only [map_sum,ZMod.map_smul,torsion_parity_values,map_zero] at hh
  have h0 := congrFun hh 0
  have h1 := congrFun hh 1
  norm_num [Fin.sum_univ_succ] at h0 h1
  intro i
  fin_cases i
  · exact h1
  · exact h0

def threePoints : Fin 3→RationalPoints (curve 0) :=
  ![normalizedPoint,torsionPoints 0 0,torsionPoints 0 1]
def threeRepresentatives : Fin 3→ℚ×ℚ :=
  ![(2896609,27854202841),torsionRepresentatives 0 0,torsionRepresentatives 0 1]
def threeClasses (i : Fin 3) : RatSquareClassAdd×RatSquareClassAdd :=
  (squareClass (threeRepresentatives i).1,squareClass (threeRepresentatives i).2)

theorem normalizedPoint_descent_coordinates :
    completeDescentCoordinates (curve 0) 0 (-(r2 0:ℚ)) (-(r3 0:ℚ)) normalizedPoint=threeClasses 0 := by
  have hx : squareClass (2130125485931716:ℚ)=squareClass (2896609:ℚ) :=
    squareClass_eq_of_factor _ _ 27118 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hy : squareClass (3125937913831225:ℚ)=squareClass (27854202841:ℚ) :=
    squareClass_eq_of_factor _ _ 335 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [completeDescentCoordinates,normalizedPoint,WeierstrassCurve.Affine.Point.mk,
    threeClasses,threeRepresentatives,r2,r3,D,A,B,hx,hy]

theorem three_descent_coordinates (i : Fin 3) :
    completeDescentCoordinates (curve 0) 0 (-(r2 0:ℚ)) (-(r3 0:ℚ)) (threePoints i)=threeClasses i := by
  fin_cases i
  · exact normalizedPoint_descent_coordinates
  · exact torsion_descent_coordinates 0 0
  · exact torsion_descent_coordinates 0 1

local instance prime31 : Fact (Nat.Prime 31) := ⟨by norm_num⟩
def threeParity : (RatSquareClassAdd×RatSquareClassAdd)→+(Fin 3→ZMod 2) where
  toFun q := ![squareClassSign q.1,squareClassValuation 263 q.2,squareClassValuation 31 q.1]
  map_zero' := by ext i; fin_cases i <;> simp
  map_add' q r := by ext i; fin_cases i <;> simp

theorem three_parity_values (i : Fin 3) :
    threeParity (threeClasses i)=![![0,0,1],![0,1,0],![1,0,0]] i := by
  ext j
  fin_cases i <;> fin_cases j <;>
    simp only [threeParity,threeClasses,threeRepresentatives,torsionRepresentatives,D,
      differenceRepresentative,AddMonoidHom.coe_mk,ZeroHom.coe_mk]
  all_goals simp (disch:=norm_num) only [squareClassValuation_apply,squareClassSign_apply]
  all_goals norm_num [padicValRat_def,padicValInt]
  all_goals try rw [valuation_nat_zero_or_one (by decide) (by decide)]
  all_goals norm_num

theorem three_classes_independent : LinearIndependent (ZMod 2) threeClasses := by
  apply Fintype.linearIndependent_iff.mpr
  intro c hc
  have hh := congrArg threeParity hc
  simp only [map_sum,ZMod.map_smul,three_parity_values,map_zero] at hh
  have h0 := congrFun hh 0
  have h1 := congrFun hh 1
  have h2 := congrFun hh 2
  norm_num [Fin.sum_univ_succ] at h0 h1 h2
  intro i
  fin_cases i
  · exact h2
  · exact h1
  · exact h0


end
end Z2Z4Rank6.ThirdTwist
