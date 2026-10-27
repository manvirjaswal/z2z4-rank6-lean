module

public import Z2Z4Rank6.ThirdTwistCoverFunctionField
public import Z2Z4Rank6.FieldPointEquivalence
public import Z2Z4Rank6.ThirdTwistRanksModels

@[expose] public section

/-! The curve over the Proj generic stalk has the point
group of X over the radical field, via the proved field isomorphism. -/
namespace Z2Z4Rank6.ThirdTwistField
noncomputable section
open AlgebraicGeometry
open ThirdTwistCoverFunctionField
open scoped Classical

section
variable [IsIntegral ThirdTwistCoverProjective.scheme]

local instance : Algebra ℚ ActualField := actualFieldRationalAlgebra

theorem scheme_curve_image :
    (X coordinateM).map functionFieldEquiv.toRingHom=X m := by
  ext <;> simp [X,E,a,b,map_ofNat]

instance schemeGenericFiberElliptic : (X coordinateM).IsElliptic := by
  constructor
  rw [isUnit_iff_ne_zero]
  intro hz
  apply (X m).isUnit_Δ.ne_zero
  rw [←scheme_curve_image,WeierstrassCurve.map_Δ,hz,map_zero]

def schemePointEquiv : (X coordinateM).toAffine.Point ≃+ (X m).toAffine.Point :=
  (FieldPointEquivalence.equiv functionFieldEquiv.toRingEquiv (X coordinateM)).trans
    (PointScaling.pointCongr scheme_curve_image)

theorem scheme_pointGroup_rank_eq_radical_rank :
    Module.rank ℤ (X coordinateM).toAffine.Point=Module.rank ℤ (X m).toAffine.Point :=
  schemePointEquiv.toIntLinearEquiv.rank_eq

end
end
end Z2Z4Rank6.ThirdTwistField
