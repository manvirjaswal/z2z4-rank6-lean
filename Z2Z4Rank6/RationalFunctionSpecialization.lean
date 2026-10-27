module

public import Z2Z4Rank6.UnivariateLocal
public import Z2Z4Rank6.RationalFunctionFamily
public import Z2Z4Rank6.FunctionFieldSpecialization

@[expose] public section

/-!
# Specialization of the original Q(t) family

The three printed polynomial sections specialize at every smooth rational
fiber through a shifted embedding into Q((T)) and the published formal good-reduction theorem. This
supplies the lower-bound
specialization step of Proposition 2.3 of M. Jaswal,
DOI 10.5281/zenodo.23437117.
-/

namespace Z2Z4Rank6.RationalFunctionSpecialization

open Common.WeierstrassCoordinates UnivariateLocal
noncomputable section
local instance : DecidableEq LS := Classical.decEq LS

/-- The integral formal equation at the rational parameter r. -/
def seriesCurve (r : ℚ) : WeierstrassCurve PS := X (mSeries r)

theorem seriesCurve_constant (r : ℚ) :
    (seriesCurve r).map PowerSeries.constantCoeff = X r := by
  rw [seriesCurve, FunctionFieldLocal.map_family, mSeries_constant]

theorem seriesCurve_laurent (r : ℚ) :
    (seriesCurve r).map (algebraMap PS LS) =
      RationalFunctionFamily.curve.map (baseEmbedding r) := by
  rw [seriesCurve, FunctionFieldLocal.map_family]
  change X (algebraMap PS LS (mSeries r)) = (X (RatFunc.X : RatFunc ℚ)).map (baseEmbedding r)
  rw [FunctionFieldLocal.map_family, baseEmbedding_X]

instance constantFiberElliptic (r : ℚ) [(X r).IsElliptic] :
    ((seriesCurve r).map PowerSeries.constantCoeff).IsElliptic := by
  rw [seriesCurve_constant]
  infer_instance

instance laurentFiberElliptic (r : ℚ) :
    ((seriesCurve r).map (algebraMap PS LS)).IsElliptic := by
  rw [seriesCurve_laurent]
  infer_instance

/-- The three integral abscissae in the shifted formal model. -/
def xSeries (r : ℚ) : Fin 3 → PS :=
  ![p1x (mSeries r),p2x (mSeries r),p3x (mSeries r)]

/-- The three integral signed ordinates in the shifted formal model. -/
def ySeries (r : ℚ) : Fin 3 → PS :=
  ![p1y (mSeries r),p2y (mSeries r),p3y (mSeries r)]

def specializedX (r : ℚ) : Fin 3 → ℚ := ![p1x r,p2x r,p3x r]
def specializedY (r : ℚ) : Fin 3 → ℚ := ![p1y r,p2y r,p3y r]

@[simp] theorem xSeries_constant (r : ℚ) (j : Fin 3) :
    PowerSeries.constantCoeff (xSeries r j)=specializedX r j := by
  fin_cases j <;> simp [xSeries, specializedX, p1x, p2x, p3x, map_ofNat]

@[simp] theorem ySeries_constant (r : ℚ) (j : Fin 3) :
    PowerSeries.constantCoeff (ySeries r j)=specializedY r j := by
  fin_cases j <;> simp [ySeries, specializedY, p1y, p2y, p3y, map_ofNat]

/-- The point map induced by the shifted field embedding. -/
def localPointMap (r : ℚ) : RationalFunctionFamily.curve.toAffine.Point →+
    ((seriesCurve r).map (algebraMap PS LS)).toAffine.Point :=
  (pointEquivOfEq (seriesCurve_laurent r).symm).toAddMonoidHom.comp
    (fieldPointMap (baseEmbedding r) RationalFunctionFamily.curve)

theorem localPointMap_coordinates (r : ℚ) (j : Fin 3) :
    encode (localPointMap r (RationalFunctionFamily.points j)) =
      some (algebraMap PS LS (xSeries r j),algebraMap PS LS (ySeries r j)) := by
  change encode (pointEquivOfEq (seriesCurve_laurent r).symm
    (fieldPointMap (baseEmbedding r) RationalFunctionFamily.curve
      (RationalFunctionFamily.points j))) = _
  rw [encode_pointEquivOfEq, encode_fieldPointMap]
  fin_cases j <;> simp [RationalFunctionFamily.points, point1, point2, point3,
    WeierstrassCurve.Affine.Point.mk, encode, xSeries, ySeries,
    RationalFunctionFamily.parameter, p1x, p1y, p2x, p2y, p3x, p3y, map_ofNat]

private theorem localPointMap_shape (r : ℚ) (j : Fin 3) :
    ∃ h : ((seriesCurve r).map (algebraMap PS LS)).toAffine.Nonsingular
        (algebraMap PS LS (xSeries r j)) (algebraMap PS LS (ySeries r j)),
      localPointMap r (RationalFunctionFamily.points j) = .some _ _ h := by
  have henc := localPointMap_coordinates r j
  cases hp : localPointMap r (RationalFunctionFamily.points j) with
  | zero => simp only [hp,encode] at henc; cases henc
  | some x y h =>
    rw [hp] at henc
    change some (x,y)=some (algebraMap PS LS (xSeries r j),algebraMap PS LS (ySeries r j)) at henc
    have hxy := Option.some.inj henc
    have hx := congrArg Prod.fst hxy
    have hy := congrArg Prod.snd hxy
    dsimp only at hx hy
    subst x
    subst y
    exact ⟨h,rfl⟩

/-- The three printed points on a smooth rational fiber. -/
def specializedPoints (r : ℚ) [(X r).IsElliptic] : Fin 3 → (X r).toAffine.Point :=
  ![point1 r,point2 r,point3 r]

theorem specializedPoints_coordinates (r : ℚ) [(X r).IsElliptic] (j : Fin 3) :
    encode (specializedPoints r j)=some (specializedX r j,specializedY r j) := by
  fin_cases j <;> rfl

/-- The published formal good-reduction theorem constructs
an additive specialization homomorphism at every smooth rational r,
with the three exact printed signed point images. -/
theorem exists_specialization (hFormal : FormalGoodReductionHomomorphisms)
    (r : ℚ) [(X r).IsElliptic] :
    ∃ spec : RationalFunctionFamily.curve.toAffine.Point →+ (X r).toAffine.Point,
      ∀ j : Fin 3, spec (RationalFunctionFamily.points j)=specializedPoints r j := by
  obtain ⟨red,hred⟩ := hFormal ℚ (seriesCurve r) inferInstance inferInstance
  let spec : RationalFunctionFamily.curve.toAffine.Point →+ (X r).toAffine.Point :=
    (pointEquivOfEq (seriesCurve_constant r)).toAddMonoidHom.comp (red.comp (localPointMap r))
  refine ⟨spec,?_⟩
  intro j
  obtain ⟨h,hshape⟩ := localPointMap_shape r j
  obtain ⟨hres,hvalue⟩ := hred (xSeries r j) (ySeries r j) h
  apply encode_injective (X r)
  change encode (pointEquivOfEq (seriesCurve_constant r)
    (red (localPointMap r (RationalFunctionFamily.points j)))) = _
  rw [encode_pointEquivOfEq,hshape,hvalue,specializedPoints_coordinates]
  change some (PowerSeries.constantCoeff (xSeries r j),PowerSeries.constantCoeff (ySeries r j)) = _
  rw [xSeries_constant,ySeries_constant]

end
end Z2Z4Rank6.RationalFunctionSpecialization
