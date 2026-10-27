import Z2Z4Rank6.ThirdTwistPairRankQuadratic

/-! Applying quadratic coordinate descent twice to a radical tower. -/
namespace Z2Z4Rank6.ThirdTwistPairRank.Biquadratic
noncomputable section
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {F : Type*} [Field F] [CharZero F] [DecidableEq F]
variable (d e A B : F) [hd : Fact (¬IsSquare d)]
local notation "R" => QuadraticAlgebra F d 0
variable (he : ¬IsSquare (algebraMap F R e))

abbrev firstEmbedding : F →+* R := algebraMap F R

def innerData (t : F) : Quadratic.Data F := ⟨d,hd.out,t*A,t^2*B⟩
def outerData (he : ¬IsSquare (algebraMap F R e)) : Quadratic.Data R :=
  ⟨algebraMap F R e,he,algebraMap F R A,algebraMap F R B⟩

def baseTwist (t : F) : WeierstrassCurve F := PointScaling.curve (t*A) (t^2*B)

omit [CharZero F] in
omit [DecidableEq F] in
theorem inner_twist_false (t : F) :
    Quadratic.twistCurve (innerData d A B t) false=baseTwist A B t := by
  ext1 <;> simp [Quadratic.twistCurve,Quadratic.twistD,innerData,baseTwist,PointScaling.curve]

omit [CharZero F] in
omit [DecidableEq F] in
theorem inner_twist_true (t : F) :
    Quadratic.twistCurve (innerData d A B t) true=baseTwist A B (d*t) := by
  ext1 <;> simp [Quadratic.twistCurve,Quadratic.twistD,innerData,baseTwist,
    PointScaling.curve] <;> ring

omit [CharZero F] in
omit [DecidableEq F] in
theorem outer_twist_false (he : ¬IsSquare (algebraMap F R e)) :
    Quadratic.twistCurve (outerData d e A B he) false=
      Quadratic.model (innerData d A B 1) := by
  ext1 <;> simp [Quadratic.twistCurve,Quadratic.twistD,outerData,
    Quadratic.model,Quadratic.K,innerData,PointScaling.curve]

omit [CharZero F] [DecidableEq F] in
theorem outer_twist_true (he : ¬IsSquare (algebraMap F R e)) :
    Quadratic.twistCurve (outerData d e A B he) true=
      Quadratic.model (innerData d A B e) := by
  change PointScaling.curve ((algebraMap F R e)*(algebraMap F R A))
    ((algebraMap F R e)^2*(algebraMap F R B))=
    PointScaling.curve (algebraMap F R (e*A)) (algebraMap F R (e^2*B))
  rw [map_mul,map_mul,map_pow]

/-- Four-term rank decomposition over a two-radical tower. -/
theorem rank_four (he : ¬IsSquare (algebraMap F R e)) :
    Module.rank ℤ (Quadratic.model (outerData d e A B he)).toAffine.Point=
      (Module.rank ℤ (baseTwist A B 1).toAffine.Point+
        Module.rank ℤ (baseTwist A B d).toAffine.Point)+
      (Module.rank ℤ (baseTwist A B e).toAffine.Point+
        Module.rank ℤ (baseTwist A B (d*e)).toAffine.Point) := by
  have h0 := Quadratic.pointGroup_rank_twist_decomposition (outerData d e A B he)
  have h1 := Quadratic.pointGroup_rank_twist_decomposition (innerData d A B 1)
  have h2 := Quadratic.pointGroup_rank_twist_decomposition (innerData d A B e)
  have hc0 := (PointScaling.pointCongr (outer_twist_false d e A B he)).toIntLinearEquiv.rank_eq
  have hc1 := (PointScaling.pointCongr (outer_twist_true d e A B he)).toIntLinearEquiv.rank_eq
  have h := h0.trans (congrArg₂ (·+·) (hc0.trans h1) (hc1.trans h2))
  have c00 := (PointScaling.pointCongr (inner_twist_false d A B 1)).toIntLinearEquiv.rank_eq
  have c01 := (PointScaling.pointCongr (inner_twist_true d A B 1)).toIntLinearEquiv.rank_eq
  have he1 : baseTwist A B (d*1)=baseTwist A B d := congrArg (baseTwist A B) (mul_one d)
  have c01 := c01.trans (PointScaling.pointCongr he1).toIntLinearEquiv.rank_eq
  have c10 := (PointScaling.pointCongr (inner_twist_false d A B e)).toIntLinearEquiv.rank_eq
  have c11 := (PointScaling.pointCongr (inner_twist_true d A B e)).toIntLinearEquiv.rank_eq
  have hc := congrArg₂ (·+·) (congrArg₂ (·+·) c00 c01) (congrArg₂ (·+·) c10 c11)
  exact h.trans hc

end
end Z2Z4Rank6.ThirdTwistPairRank.Biquadratic
