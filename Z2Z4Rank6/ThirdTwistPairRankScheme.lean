module

public import Z2Z4Rank6.ThirdTwistPairRank
public import Z2Z4Rank6.ThirdTwistPairGeometryFunctionField
public import Z2Z4Rank6.FieldPointEquivalence

@[expose] public section

/-! Rank 5 on each smooth proper genus-one pair base's generic stalk. -/
namespace Z2Z4Rank6.ThirdTwistPairRank
noncomputable section
open AlgebraicGeometry ThirdTwistPairGeometry.FunctionField
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

instance pairOneGenericElliptic : (X ThirdTwistField.PairOne.m).IsElliptic := by
  have he : RationalFunctionFamily.curve.map (algebraMap Base ThirdTwistField.PairOne)=
      X ThirdTwistField.PairOne.m := by
    ext <;> simp [RationalFunctionFamily.curve,RationalFunctionFamily.parameter,
      X,E,a,b,ThirdTwistField.PairOne.m,map_ofNat]
  rw [←he]
  infer_instance

instance pairTwoGenericElliptic : (X ThirdTwistField.PairTwo.m).IsElliptic := by
  have he : RationalFunctionFamily.curve.map (algebraMap Base ThirdTwistField.PairTwo)=
      X ThirdTwistField.PairTwo.m := by
    ext <;> simp [RationalFunctionFamily.curve,RationalFunctionFamily.parameter,
      X,E,a,b,ThirdTwistField.PairTwo.m,map_ofNat]
  rw [←he]
  infer_instance

theorem pairOne_scheme_curve_image (h : QuadricIntersectionModel.CFSTheorem28ii) :
    (X (coordinateM h false)).map (pairOneEquiv h).toRingHom=X ThirdTwistField.PairOne.m := by
  ext <;> simp [X,E,a,b,map_ofNat]

theorem pairTwo_scheme_curve_image (h : QuadricIntersectionModel.CFSTheorem28ii) :
    (X (coordinateM h true)).map (pairTwoEquiv h).toRingHom=X ThirdTwistField.PairTwo.m := by
  ext <;> simp [X,E,a,b,map_ofNat]

instance schemeGenericElliptic (h : QuadricIntersectionModel.CFSTheorem28ii) (ε : Bool) :
    (X (coordinateM h ε)).IsElliptic := by
  constructor
  rw [isUnit_iff_ne_zero]
  intro hz
  cases ε
  · apply (X ThirdTwistField.PairOne.m).isUnit_Δ.ne_zero
    rw [←pairOne_scheme_curve_image h,WeierstrassCurve.map_Δ,hz,map_zero]
  · apply (X ThirdTwistField.PairTwo.m).isUnit_Δ.ne_zero
    rw [←pairTwo_scheme_curve_image h,WeierstrassCurve.map_Δ,hz,map_zero]

def pairOneSchemePointEquiv (h : QuadricIntersectionModel.CFSTheorem28ii) :
    (X (coordinateM h false)).toAffine.Point ≃+ (X ThirdTwistField.PairOne.m).toAffine.Point :=
  (FieldPointEquivalence.equiv (pairOneEquiv h).toRingEquiv (X (coordinateM h false))).trans
    (PointScaling.pointCongr (pairOne_scheme_curve_image h))

def pairTwoSchemePointEquiv (h : QuadricIntersectionModel.CFSTheorem28ii) :
    (X (coordinateM h true)).toAffine.Point ≃+ (X ThirdTwistField.PairTwo.m).toAffine.Point :=
  (FieldPointEquivalence.equiv (pairTwoEquiv h).toRingEquiv (X (coordinateM h true))).trans
    (PointScaling.pointCongr (pairTwo_scheme_curve_image h))

/-- Exact ordinary elliptic-curve rank on the function field of each
of the two printed smooth proper genus-one intersections in P3. -/
theorem scheme_pointGroup_rank_eq_five
    (hCFS : QuadricIntersectionModel.CFSTheorem28ii) (hMazur : MazurTorsionTheorem)
    (hReduction : GoodReductionHomomorphisms) (hFormal : FormalGoodReductionHomomorphisms)
    (hGT : GusicTadic.GusicTadicTheorem11) (hMW : MordellWeilTheorem)
    (hDescent : CompleteTwoDescentTheorem) (hOdd : OddPrimeTorsionIntegrality) (ε : Bool) :
    Module.rank ℤ (X (coordinateM hCFS ε)).toAffine.Point=5 := by
  cases ε
  · exact (pairOneSchemePointEquiv hCFS).toIntLinearEquiv.rank_eq.trans
      (pairOne_rank_eq_five hMazur hReduction hFormal hGT hMW hDescent hOdd)
  · exact (pairTwoSchemePointEquiv hCFS).toIntLinearEquiv.rank_eq.trans
      (pairTwo_rank_eq_five hMazur hReduction hFormal hGT hMW hDescent hOdd)

/-- Both printed pair bases have genus 1 and their elliptic
curve over the projective generic-stalk field has exact ordinary rank 5. -/
theorem pair_bases_genus_one_rank_five
    (hCFS : QuadricIntersectionModel.CFSTheorem28ii) (hMazur : MazurTorsionTheorem)
    (hReduction : GoodReductionHomomorphisms) (hFormal : FormalGoodReductionHomomorphisms)
    (hGT : GusicTadic.GusicTadicTheorem11) (hMW : MordellWeilTheorem)
    (hDescent : CompleteTwoDescentTheorem) (hOdd : OddPrimeTorsionIntegrality) (ε : Bool) :
    RationalCurveGenus.IsSmoothProperGenusOne
        (ThirdTwistPairGeometry.scheme ε) (ThirdTwistPairGeometry.structureMap ε) ∧
      (X (coordinateM hCFS ε)).IsElliptic ∧
      Module.rank ℤ (X (coordinateM hCFS ε)).toAffine.Point=5 :=
  ⟨ThirdTwistPairGeometry.genus_one hCFS ε,inferInstance,
    scheme_pointGroup_rank_eq_five hCFS hMazur hReduction hFormal hGT hMW hDescent hOdd ε⟩

end
end Z2Z4Rank6.ThirdTwistPairRank
