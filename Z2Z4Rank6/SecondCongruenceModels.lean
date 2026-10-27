module

public import Z2Z4Rank6.SecondCongruenceSections

@[expose] public section
namespace Z2Z4Rank6
open SecondFamily
theorem second_regular_of_congruent (i:Fin 6) (P:G2Point ℚ) (h:SecondCongruentAt i P) :
    P.W≠0 ∧ qA P.W≠0 ∧ qB P.W≠0 := by
  have hu2 : residue (SecondReductionData.primes i) SecondReductionData.basePoint.s2≠0 := by
    fin_cases i <;> decide +kernel
  have hu3 : residue (SecondReductionData.primes i) SecondReductionData.basePoint.s3≠0 := by
    fin_cases i <;> decide +kernel
  have hs2 : P.s2≠0 := ne_zero_of_residue_ne_zero (by rwa [h.2.2.2.2.2.2.1])
  have hs3 : P.s3≠0 := ne_zero_of_residue_ne_zero (by rwa [h.2.2.2.2.2.2.2])
  exact ⟨ne_of_gt P.rational_W_pos,by rw [←P.s2_sq]; exact pow_ne_zero 2 hs2,
    by rw [←P.s3_sq]; exact pow_ne_zero 2 hs3⟩

theorem second_elliptic_of_congruent (i:Fin 6) (P:G2Point ℚ) (h:SecondCongruentAt i P) :
    (F P.W).IsElliptic := by
  have havoid : residue (SecondReductionData.primes i) SecondReductionData.basePoint.W≠
      residue (SecondReductionData.primes i) (1:ℚ) ∧
    residue (SecondReductionData.primes i) SecondReductionData.basePoint.W≠
      residue (SecondReductionData.primes i) ((lambda:ℚ)^2) := by
    fin_cases i <;> decide +kernel
  apply P.rational_elliptic_iff.mpr
  constructor
  · intro he
    have hh:=h.2.2.2.2.1
    rw [he] at hh
    exact havoid.1 hh.symm
  · intro he
    have hh:=h.2.2.2.2.1
    rw [he] at hh
    exact havoid.2 hh.symm

/-- The constant printed scaling applied to every rational fiber. -/
def secondScaledCurve (W:ℚ) : WeierstrassCurve ℚ :=
  PointScaling.curve (SecondReductionData.scale^2*U W)
    (SecondReductionData.scale^4*(V W)^2)

theorem secondF_eq_long (W:ℚ) : F W=PointScaling.curve (U W) ((V W)^2) := by
  ext <;> simp [F,twistedF,PointScaling.curve]

def secondFiberScaling (W:ℚ) : RationalPoints (F W) ≃+ RationalPoints (secondScaledCurve W) :=
  (PointScaling.pointCongr (secondF_eq_long W)).trans
    (PointScaling.scaleEquiv (U W) ((V W)^2) SecondReductionData.scale (by norm_num [SecondReductionData.scale]))

theorem secondScaledCurve_discriminant (W:ℚ) :
    (secondScaledCurve W).Δ=SecondReductionData.scale^12*(F W).Δ := by
  simp only [secondScaledCurve,PointScaling.curve,F,twistedF,WeierstrassCurve.Δ,
    WeierstrassCurve.b₂,WeierstrassCurve.b₄,WeierstrassCurve.b₆,WeierstrassCurve.b₈]
  ring

theorem secondScaledCurve_elliptic (W:ℚ) [(F W).IsElliptic] :
    (secondScaledCurve W).IsElliptic := by
  constructor
  rw [isUnit_iff_ne_zero,secondScaledCurve_discriminant]
  exact mul_ne_zero (pow_ne_zero 12 (by norm_num [SecondReductionData.scale]))
    (F W).isUnit_Δ.ne_zero

set_option maxHeartbeats 10000 in
theorem second_model_congruences (i:Fin 6) (P:G2Point ℚ) (h:SecondCongruentAt i P) :
    ResidueCongruent (SecondReductionData.primes i)
      (SecondReductionData.scale^2*U P.W)
      (SecondReductionData.scale^2*U SecondReductionData.baseW) ∧
    ResidueCongruent (SecondReductionData.primes i)
      (SecondReductionData.scale^4*(V P.W)^2)
      (SecondReductionData.scale^4*(V SecondReductionData.baseW)^2) := by
  obtain ⟨hW,hs1,hs2,hs3⟩:=second_coordinate_congruences i P h
  change ResidueCongruent _ P.W SecondReductionData.baseW at hW
  constructor <;> dsimp only [U,V] <;> second_residue_arith i


end Z2Z4Rank6
