module

public import Z2Z4Rank6.FirstExampleRankSixBasic
public import Z2Z4Rank6.FunctionFieldSpecialization
public import Z2Z4Rank6.ReductionCheckRational
public import Z2Z4Rank6.PointScaling

@[expose] public section

/-! The proved six independent points at c₀ transport by the
printed scaling to the coprime integral model. Source: Jaswal Proposition 5.1
and the exact-rank assertion before Proposition 6.2, DOI 10.5281/zenodo.23437117. -/
namespace Z2Z4Rank6.FirstExampleRankSix
open Common.WeierstrassCoordinates
noncomputable section

def longA : ℚ := (a baseC0.m)^2+(b baseC0.m)^2
def longB : ℚ := (a baseC0.m)^2*(b baseC0.m)^2

theorem source_curve : X baseC0.m=PointScaling.curve longA longB := rfl

theorem target_curve :
    PointScaling.curve (ReductionData.scale^2*longA) (ReductionData.scale^4*longB)=curve := by
  ext <;> norm_num [PointScaling.curve,curve,E,longA,longB,A,B,baseC0,a,b,
    ReductionData.scale]

/-- Group equivalence given by the printed scaling of x and y. -/
def fiberScaling : (X baseC0.m).toAffine.Point≃+RationalPoints curve :=
  ((PointScaling.pointCongr source_curve).trans
    (PointScaling.scaleEquiv longA longB ReductionData.scale (by norm_num [ReductionData.scale]))).trans
    (PointScaling.pointCongr target_curve)

def points (i : Fin 6) : RationalPoints curve :=
  fiberScaling (FunctionFieldLocal.basePoints i)

/-- These transported points have exactly the six printed normalized coordinates. -/
theorem points_coordinates (i : Fin 6) :
    encode (points i)=some (ReductionData.rationalX i,ReductionData.rationalY i) := by
  unfold points fiberScaling
  rw [AddEquiv.trans_apply,PointScaling.encode_pointCongr,AddEquiv.trans_apply,
    PointScaling.encode_scaleEquiv,PointScaling.encode_pointCongr]
  change some (ReductionData.scale^2*sixX baseC0.m i,
    ReductionData.scale^3*sixY baseC0.m baseC0.u baseC0.v i)=_
  apply congrArg some
  apply Prod.ext
  · exact (ReductionData.rationalX_eq_scaled_section i).symm
  · exact (ReductionData.rationalY_eq_scaled_section i).symm

/-- Independence reuses the proved six-prime reduction argument. -/
theorem points_independent (hMazur : MazurTorsionTheorem)
    (hReduction : GoodReductionHomomorphisms) : LinearIndependent ℤ points := by
  have hT : TorsionExact (X baseC0.m) :=
    X_torsion_of_congruent13 hMazur baseC0.m (Or.inl (by norm_num [baseC0]))
  exact (FunctionFieldLocal.basePoints_linearIndependent hReduction hT).map'
    fiberScaling.toIntLinearEquiv.toLinearMap (LinearMap.ker_eq_bot.mpr fiberScaling.injective)

theorem rank_at_least_six (hMazur : MazurTorsionTheorem)
    (hReduction : GoodReductionHomomorphisms) :
    6≤Module.rank ℤ (RationalPoints curve) := by
  simpa using (points_independent hMazur hReduction).cardinal_le_rank

end
end Z2Z4Rank6.FirstExampleRankSix
