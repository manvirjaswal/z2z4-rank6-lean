import Z2Z4Rank6.GFunctionFieldLocal
import Z2Z4Rank6.FunctionFieldSpecialization

/-!
# The rank-five lower bound over Q(G)

The formal place and integral coordinates are constructed before using
the published formal good-reduction theorem.
-/

namespace Z2Z4Rank6

noncomputable section

open Common.WeierstrassCoordinates

namespace GFunctionFieldLocal

local instance localLaurentDecidableEq : DecidableEq LS := Classical.decEq LS

theorem encode_points (j : Fin 5) : encode (GFunctionField.points j)=
    some (GFunctionField.fiveX GFunctionField.m GFunctionField.eta j,
      GFunctionField.fiveY GFunctionField.m GFunctionField.eta j) :=
  GFunctionField.encode_fivePoints _ _ GFunctionField.eta_sq
    GFunctionField.chart_denominator_ne_zero GFunctionField.chart_numerator_ne_zero j

def localPointMap : (X GFunctionField.m).toAffine.Point →+
    (seriesCurve.map (algebraMap PS LS)).toAffine.Point :=
  (pointEquivOfEq seriesCurve_laurent.symm).toAddMonoidHom.comp
    (fieldPointMap embedding (X GFunctionField.m))

theorem localPointMap_coordinates (j : Fin 5) :
    encode (localPointMap (GFunctionField.points j))=
      some (algebraMap PS LS (xSeries j),algebraMap PS LS (ySeries j)) := by
  change encode (pointEquivOfEq seriesCurve_laurent.symm
    (fieldPointMap embedding (X GFunctionField.m) (GFunctionField.points j)))=_
  rw [encode_pointEquivOfEq,encode_fieldPointMap,encode_points]
  change some (embedding (GFunctionField.fiveX GFunctionField.m GFunctionField.eta j),
    embedding (GFunctionField.fiveY GFunctionField.m GFunctionField.eta j))=_
  rw [embedding_fiveX,embedding_fiveY]

private theorem localPointMap_shape (j : Fin 5) :
    ∃ h : (seriesCurve.map (algebraMap PS LS)).toAffine.Nonsingular
        (algebraMap PS LS (xSeries j)) (algebraMap PS LS (ySeries j)),
      localPointMap (GFunctionField.points j)=.some _ _ h := by
  have henc := localPointMap_coordinates j
  cases hp : localPointMap (GFunctionField.points j) with
  | zero => simp only [hp,encode] at henc; cases henc
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

theorem exists_specialization (hFormal : FormalGoodReductionHomomorphisms) :
    ∃ spec : (X GFunctionField.m).toAffine.Point →+ (X GReductionData.baseM).toAffine.Point,
      ∀ j : Fin 5, spec (GFunctionField.points j)=GReductionData.fiberPoints j := by
  obtain ⟨red,hred⟩ := hFormal ℚ seriesCurve inferInstance inferInstance
  let spec : (X GFunctionField.m).toAffine.Point →+ (X GReductionData.baseM).toAffine.Point :=
    (pointEquivOfEq seriesCurve_constant).toAddMonoidHom.comp (red.comp localPointMap)
  refine ⟨spec,?_⟩
  intro j
  obtain ⟨h,hshape⟩ := localPointMap_shape j
  obtain ⟨hres,hvalue⟩ := hred (xSeries j) (ySeries j) h
  apply encode_injective (X GReductionData.baseM)
  change encode (pointEquivOfEq seriesCurve_constant
    (red (localPointMap (GFunctionField.points j))))=_
  rw [encode_pointEquivOfEq,hshape,hvalue,GReductionData.encode_fiberPoints]
  change some (PowerSeries.constantCoeff (xSeries j),PowerSeries.constantCoeff (ySeries j))=_
  rw [xSeries_constant,ySeries_constant]

end GFunctionFieldLocal

namespace GFunctionField

/-- The five points P₁,P₂,P₃,P₂′,P₃′ are independent over Q(G).
The hypotheses are the three published theorems. -/
theorem points_independent (hMazur : MazurTorsionTheorem)
    (hReduction : GoodReductionHomomorphisms) (hFormal : FormalGoodReductionHomomorphisms) :
    LinearIndependent ℤ points := by
  obtain ⟨spec,hspec⟩ := GFunctionFieldLocal.exists_specialization hFormal
  apply Fintype.linearIndependent_iff.mpr
  intro n hn
  apply Fintype.linearIndependent_iff.mp
    (GReductionData.fiberPoints_linearIndependent hMazur hReduction) n
  have h := congrArg spec hn
  simpa only [map_sum,map_zsmul,map_zero,hspec] using h

theorem rank_at_least_five (hMazur : MazurTorsionTheorem)
    (hReduction : GoodReductionHomomorphisms) (hFormal : FormalGoodReductionHomomorphisms) :
    ∃ P : Fin 5 → (X m).toAffine.Point, LinearIndependent ℤ P :=
  ⟨points,points_independent hMazur hReduction hFormal⟩

end GFunctionField
end
end Z2Z4Rank6
