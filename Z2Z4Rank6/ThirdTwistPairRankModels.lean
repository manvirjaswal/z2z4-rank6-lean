module

public import Z2Z4Rank6.ThirdTwistPairRankBiquadratic
public import Z2Z4Rank6.ThirdTwistRanksModels

@[expose] public section

/-! Model identities for the two degree-four third-twist towers. -/
namespace Z2Z4Rank6.ThirdTwistPairRank
noncomputable section
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 500000

abbrev Base := ThirdTwistField.Base
abbrev A := FunctionField.TwistCharacters.A
abbrev B := FunctionField.TwistCharacters.B

def d (ε : Bool) : Base := if ε then FunctionField.d2 else FunctionField.d1

theorem d_nonsquare (ε : Bool) : ¬IsSquare (d ε) := by
  cases ε
  · exact FunctionField.d1_not_isSquare
  · exact FunctionField.d2_not_isSquare
instance d_nonsquare_fact (ε : Bool) : Fact (¬IsSquare (d ε)) := ⟨d_nonsquare ε⟩
abbrev First (ε : Bool) := QuadraticAlgebra Base (d ε) 0

theorem third_nonsquare (ε : Bool) :
    ¬IsSquare (algebraMap Base (First ε) ThirdTwistField.d3) := by
  cases ε
  · exact ThirdTwistField.d3First_not_isSquare
  · exact ThirdTwistField.d3PairTwoFirst_not_isSquare

def data (ε : Bool) : Quadratic.Data (First ε) :=
  Biquadratic.outerData (d ε) ThirdTwistField.d3 A B (third_nonsquare ε)

abbrev model (ε : Bool) := Quadratic.model (data ε)

theorem model_false : model false=X ThirdTwistField.PairOne.m := by
  change PointScaling.curve
    (algebraMap FunctionField.First ThirdTwistField.PairOne (algebraMap Base FunctionField.First A))
    (algebraMap FunctionField.First ThirdTwistField.PairOne (algebraMap Base FunctionField.First B))=_
  rw [←IsScalarTower.algebraMap_apply Base FunctionField.First ThirdTwistField.PairOne,
    ←IsScalarTower.algebraMap_apply Base FunctionField.First ThirdTwistField.PairOne]
  ext1 <;> simp [A,B,FunctionField.TwistCharacters.A,FunctionField.TwistCharacters.B,
    PointScaling.curve,X,E,a,b,ThirdTwistField.PairOne.m,map_ofNat]

theorem model_true : model true=X ThirdTwistField.PairTwo.m := by
  change PointScaling.curve
    (algebraMap ThirdTwistField.PairTwoFirst ThirdTwistField.PairTwo
      (algebraMap Base ThirdTwistField.PairTwoFirst A))
    (algebraMap ThirdTwistField.PairTwoFirst ThirdTwistField.PairTwo
      (algebraMap Base ThirdTwistField.PairTwoFirst B))=_
  rw [←IsScalarTower.algebraMap_apply Base ThirdTwistField.PairTwoFirst ThirdTwistField.PairTwo,
    ←IsScalarTower.algebraMap_apply Base ThirdTwistField.PairTwoFirst ThirdTwistField.PairTwo]
  ext1 <;> simp [A,B,FunctionField.TwistCharacters.A,FunctionField.TwistCharacters.B,
    PointScaling.curve,X,E,a,b,ThirdTwistField.PairTwo.m,map_ofNat]

def oldCharacter (ε : Bool) : Bool×Bool := if ε then (false,true) else (true,false)
def thirdIndex (ε : Bool) : Fin 4 := if ε then 2 else 1

theorem trivial_model : Biquadratic.baseTwist A B (1 : Base)=RationalFunctionFamily.curve := by
  ext <;> simp [Biquadratic.baseTwist,A,B,FunctionField.TwistCharacters.A,
    FunctionField.TwistCharacters.B,PointScaling.curve,RationalFunctionFamily.curve,
    RationalFunctionFamily.parameter,X,E]

theorem old_model (ε : Bool) : Biquadratic.baseTwist A B (d ε)=
    FunctionField.TwistCharacters.twistCurve (oldCharacter ε) := by
  cases ε <;> rfl

theorem third_model : Biquadratic.baseTwist A B ThirdTwistField.d3=
    GusicTadic.genericModel (ThirdTwist.twistPolynomial 0) := by
  have he := ThirdTwistField.twistCurve_last_true (false,false)
  simpa [ThirdTwistField.thirdIndex,ThirdTwistField.TwistCharacters.twistCurve,
    ThirdTwistField.TwistCharacters.twistD,FunctionField.TwistCharacters.twistD,
    Biquadratic.baseTwist,ThirdTwistField.TwistCharacters.A,
    ThirdTwistField.TwistCharacters.B,A,B,
    FunctionField.TwistCharacters.A,FunctionField.TwistCharacters.B] using he

theorem mixed_model (ε : Bool) : Biquadratic.baseTwist A B (d ε*ThirdTwistField.d3)=
    GusicTadic.genericModel (ThirdTwist.twistPolynomial (thirdIndex ε)) := by
  cases ε
  · have he := ThirdTwistField.twistCurve_last_true (true,false)
    simpa [thirdIndex,d,ThirdTwistField.thirdIndex,ThirdTwistField.TwistCharacters.twistCurve,
      ThirdTwistField.TwistCharacters.twistD,FunctionField.TwistCharacters.twistD,
      Biquadratic.baseTwist,ThirdTwistField.TwistCharacters.A,
      ThirdTwistField.TwistCharacters.B,A,B,
      FunctionField.TwistCharacters.A,FunctionField.TwistCharacters.B] using he
  · have he := ThirdTwistField.twistCurve_last_true (false,true)
    simpa [thirdIndex,d,ThirdTwistField.thirdIndex,ThirdTwistField.TwistCharacters.twistCurve,
      ThirdTwistField.TwistCharacters.twistD,FunctionField.TwistCharacters.twistD,
      Biquadratic.baseTwist,ThirdTwistField.TwistCharacters.A,
      ThirdTwistField.TwistCharacters.B,A,B,
      FunctionField.TwistCharacters.A,FunctionField.TwistCharacters.B] using he

theorem rank_decomposition (ε : Bool) :
    Module.rank ℤ (model ε).toAffine.Point=
      (Module.rank ℤ RationalFunctionFamily.curve.toAffine.Point+
        Module.rank ℤ (FunctionField.TwistCharacters.twistCurve (oldCharacter ε)).toAffine.Point)+
      (Module.rank ℤ (GusicTadic.genericModel (ThirdTwist.twistPolynomial 0)).toAffine.Point+
        Module.rank ℤ (GusicTadic.genericModel
          (ThirdTwist.twistPolynomial (thirdIndex ε))).toAffine.Point) := by
  have he := Biquadratic.rank_four (d ε) ThirdTwistField.d3 A B
    (third_nonsquare ε)
  have h0 := (PointScaling.pointCongr trivial_model).toIntLinearEquiv.rank_eq
  have h1 := (PointScaling.pointCongr (old_model ε)).toIntLinearEquiv.rank_eq
  have h2 := (PointScaling.pointCongr third_model).toIntLinearEquiv.rank_eq
  have h3 := (PointScaling.pointCongr (mixed_model ε)).toIntLinearEquiv.rank_eq
  exact he.trans (congrArg₂ (·+·) (congrArg₂ (·+·) h0 h1) (congrArg₂ (·+·) h2 h3))

end
end Z2Z4Rank6.ThirdTwistPairRank
