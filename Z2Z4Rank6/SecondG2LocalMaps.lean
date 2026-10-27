module

public import Z2Z4Rank6.SecondLocalMaps
public import Z2Z4Rank6.SecondReductionRational

@[expose] public section

/-!
# The four continuous G2 coordinates at the second-family center

These are the rational maps used in the seven-place congruence argument of
Remark 8.2 in M. Jaswal, DOI 10.5281/zenodo.23437117. Their naturality and
continuity are checked directly.
-/
namespace Z2Z4Rank6

section Field
variable {K : Type*} [Field K]

def secondG2Coordinates (z : K × K) : Fin 4 → K :=
  let t := secondQuarticTheta z.1 z.2
  let e := secondQuarticEta z.1 z.2
  ![(SecondFamily.thetaS1 t)^2, SecondFamily.thetaS1 t,
    SecondFamily.thetaS2 t, (58/1185921)*e/(t^2-29)]

def secondG2PointCoordinates (P : SecondFamily.G2Point K) : Fin 4 → K :=
  ![P.W,P.s1,P.s2,P.s3]

theorem secondG2Coordinates_to_point (x y : ℚ) (h : J2.toAffine.Nonsingular x y)
    (hchart : secondJacobianQuarticChart (.some x y h)) :
    secondG2Coordinates (x,y) =
      secondG2PointCoordinates (secondQuarticToG2
        (secondJacobianToQuartic ⟨.some x y h,hchart⟩)) := rfl

variable [CharZero K]

theorem secondCoordinatesC0_theta_denom :
    (secondQuarticTheta (secondJacobianCoordinatesC0 (K:=K)).1
      (secondJacobianCoordinatesC0 (K:=K)).2)^2-29 ≠ 0 := by
  rw [secondCoordinatesC0_theta]
  norm_num

theorem secondG2Coordinates_c0 (j : Fin 4) :
    secondG2Coordinates (secondJacobianCoordinatesC0 (K:=K)) j =
      ((secondG2PointCoordinates SecondReductionData.basePoint j : ℚ) : K) := by
  fin_cases j <;>
    norm_num [secondG2Coordinates,secondCoordinatesC0_theta,secondCoordinatesC0_eta,
      secondG2PointCoordinates,SecondReductionData.basePoint,SecondReductionData.baseW,
      SecondReductionData.baseS1,SecondReductionData.baseS2,SecondReductionData.baseS3,
      SecondFamily.thetaS1,SecondFamily.thetaS2]

end Field

section Naturality
variable {K L : Type*} [Field K] [Field L] (f : K →+* L)

theorem map_secondG2Coordinates (z : K × K) (j : Fin 4) :
    f (secondG2Coordinates z j) = secondG2Coordinates (f z.1,f z.2) j := by
  fin_cases j <;>
    simp [secondG2Coordinates,SecondFamily.thetaS1,SecondFamily.thetaS2,
      map_secondQuarticTheta,map_secondQuarticEta,map_ofNat]

end Naturality

section Continuity
variable {K : Type*} [Field K] [CharZero K] [TopologicalSpace K]
  [IsTopologicalRing K] [ContinuousInv₀ K]

theorem secondG2Coordinates_continuousAt_c0 (j : Fin 4) :
    ContinuousAt (fun z : K × K => secondG2Coordinates z j) secondJacobianCoordinatesC0 := by
  have ht := secondQuarticTheta_continuousAt (K:=K) _ secondCoordinatesC0_denom_ne_zero
  have he := secondQuarticEta_continuousAt (K:=K) _ secondCoordinatesC0_denom_ne_zero
  have hd := secondCoordinatesC0_theta_denom (K:=K)
  fin_cases j <;>
    dsimp only [secondG2Coordinates,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two,Matrix.cons_val_three,SecondFamily.thetaS1,SecondFamily.thetaS2] <;>
    fun_prop (disch:=exact hd)

end Continuity
end Z2Z4Rank6
