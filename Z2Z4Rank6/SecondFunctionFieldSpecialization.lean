module

public import Z2Z4Rank6.SecondFunctionFieldCoordinates
public import Z2Z4Rank6.FunctionFieldSpecialization

@[expose] public section

/-!
# Specialization and independence over the Q(G₂)

The formal place and all six integral coordinates are constructed in the
preceding files. The formal reduction hypothesis is FormalGoodReductionHomomorphisms, from Silverman
VII.2.1.
-/

namespace Z2Z4Rank6

noncomputable section

set_option maxHeartbeats 1000000

open Common.WeierstrassCoordinates

namespace SecondFunctionFieldLocal

local instance : DecidableEq LS := Classical.decEq LS

theorem encode_points (j : Fin 6) :
    encode (SecondFunctionField.points j)=
      some (SecondFunctionField.genericBasePoint.sixX j,
        SecondFunctionField.genericBasePoint.sixY j) := by
  let : (SecondFamily.F SecondFunctionField.genericBasePoint.W).IsElliptic :=
    SecondFunctionField.genericFiberElliptic
  exact SecondFunctionField.genericBasePoint.encode_sixPoints
    SecondFunctionField.W_ne_zero SecondFunctionField.qA_W_ne_zero
    SecondFunctionField.qB_W_ne_zero j

def localPointMap : (SecondFamily.F SecondFunctionField.W).toAffine.Point →+
    (seriesCurve.map (algebraMap PS LS)).toAffine.Point :=
  (pointEquivOfEq seriesCurve_laurent.symm).toAddMonoidHom.comp
    (fieldPointMap embedding (SecondFamily.F SecondFunctionField.W))

theorem localPointMap_coordinates (j : Fin 6) :
    encode (localPointMap (SecondFunctionField.points j))=
      some (algebraMap PS LS (xSeries j),algebraMap PS LS (ySeries j)) := by
  change encode (pointEquivOfEq seriesCurve_laurent.symm
    (fieldPointMap embedding (SecondFamily.F SecondFunctionField.W)
      (SecondFunctionField.points j)))=_
  rw [encode_pointEquivOfEq,encode_fieldPointMap,encode_points]
  change some (embedding (SecondFunctionField.genericBasePoint.sixX j),
    embedding (SecondFunctionField.genericBasePoint.sixY j))=_
  rw [embedding_sixX,embedding_sixY]

private theorem localPointMap_shape (j : Fin 6) :
    ∃ h : (seriesCurve.map (algebraMap PS LS)).toAffine.Nonsingular
        (algebraMap PS LS (xSeries j)) (algebraMap PS LS (ySeries j)),
      localPointMap (SecondFunctionField.points j)=.some _ _ h := by
  have henc := localPointMap_coordinates j
  cases hp : localPointMap (SecondFunctionField.points j) with
  | zero =>
    simp only [hp,encode] at henc
    cases henc
  | some x y h =>
    rw [hp] at henc
    change some (x,y)=some (algebraMap PS LS (xSeries j),algebraMap PS LS (ySeries j)) at henc
    have hxy := Option.some.inj henc
    have hx := congrArg Prod.fst hxy
    have hy := congrArg Prod.snd hxy
    dsimp only at hx hy
    subst x
    subst y
    exact ⟨h,rfl⟩

/-- The additive specialization map, with all six printed values. -/
theorem exists_specialization_at_base (hFormal : FormalGoodReductionHomomorphisms) :
    ∃ spec : (SecondFamily.F SecondFunctionField.W).toAffine.Point →+
        (SecondFamily.F SecondReductionData.baseW).toAffine.Point,
      ∀ j : Fin 6, spec (SecondFunctionField.points j)=SecondReductionData.fiberPoints j := by
  obtain ⟨red,hred⟩ := hFormal ℚ seriesCurve inferInstance inferInstance
  let spec : (SecondFamily.F SecondFunctionField.W).toAffine.Point →+
      (SecondFamily.F SecondReductionData.baseW).toAffine.Point :=
    (pointEquivOfEq seriesCurve_constant).toAddMonoidHom.comp (red.comp localPointMap)
  refine ⟨spec,?_⟩
  intro j
  obtain ⟨h,hshape⟩ := localPointMap_shape j
  obtain ⟨hres,hvalue⟩ := hred (xSeries j) (ySeries j) h
  apply encode_injective (SecondFamily.F SecondReductionData.baseW)
  change encode (pointEquivOfEq seriesCurve_constant
    (red (localPointMap (SecondFunctionField.points j))))=_
  rw [encode_pointEquivOfEq,hshape,hvalue,SecondReductionData.encode_fiberPoints]
  change some (PowerSeries.constantCoeff (xSeries j),PowerSeries.constantCoeff (ySeries j))=_
  rw [xSeries_constant,ySeries_constant]

theorem points_linearIndependent_of_base
    (hFormal : FormalGoodReductionHomomorphisms)
    (hbase : LinearIndependent ℤ SecondReductionData.fiberPoints) :
    LinearIndependent ℤ SecondFunctionField.points := by
  obtain ⟨spec,hspec⟩ := exists_specialization_at_base hFormal
  apply Fintype.linearIndependent_iff.mpr
  intro n hn
  apply Fintype.linearIndependent_iff.mp hbase n
  have h := congrArg spec hn
  simpa only [map_sum,map_zsmul,map_zero,hspec] using h

end SecondFunctionFieldLocal

namespace SecondFunctionField

/-- The six named points in the degree-eight function field Q(G₂) are
integer-linearly independent. -/
theorem points_independent
    (hMazur : MazurTorsionTheorem) (hReduction : GoodReductionHomomorphisms)
    (hFormal : FormalGoodReductionHomomorphisms) : LinearIndependent ℤ points :=
  SecondFunctionFieldLocal.points_linearIndependent_of_base hFormal
    (SecondReductionData.fiberPoints_linearIndependent hMazur hReduction)

end SecondFunctionField
end
end Z2Z4Rank6
