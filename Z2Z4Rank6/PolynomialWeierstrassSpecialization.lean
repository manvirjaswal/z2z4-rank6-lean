import Z2Z4Rank6.UnivariateLocal
import Z2Z4Rank6.FunctionFieldSpecialization
import Z2Z4Rank6.PointScaling

/-! Specialization of a polynomial Weierstrass model at a smooth
rational fiber. The coordinate statement applies to every polynomial
section; it uses the formal good-reduction theorem. -/

namespace Z2Z4Rank6.PolynomialWeierstrassSpecialization
noncomputable section
open Polynomial Common.WeierstrassCoordinates UnivariateLocal
local instance : DecidableEq LS := Classical.decEq LS

abbrev polynomialMap : ℚ[X] →+* RatFunc ℚ := algebraMap ℚ[X] (RatFunc ℚ)
def evaluation (r : ℚ) : ℚ[X] →+* ℚ := Polynomial.evalRingHom r
def generic (A : WeierstrassCurve ℚ[X]) : WeierstrassCurve (RatFunc ℚ) := A.map polynomialMap
def fiber (A : WeierstrassCurve ℚ[X]) (r : ℚ) : WeierstrassCurve ℚ := A.map (evaluation r)
def series (A : WeierstrassCurve ℚ[X]) (r : ℚ) : WeierstrassCurve PS := A.map (polynomialSeries r)

theorem series_constant (A : WeierstrassCurve ℚ[X]) (r : ℚ) :
    (series A r).map PowerSeries.constantCoeff=fiber A r := by
  rw [series,fiber,WeierstrassCurve.map_map]
  congr 1
  apply RingHom.ext
  intro p
  exact polynomialSeries_constant r p

theorem series_laurent (A : WeierstrassCurve ℚ[X]) (r : ℚ) :
    (series A r).map (algebraMap PS LS)=(generic A).map (baseEmbedding r) := by
  rw [series,generic,WeierstrassCurve.map_map,WeierstrassCurve.map_map]
  congr 1
  apply RingHom.ext
  intro p
  exact (baseEmbedding_polynomial r p).symm

instance constant_elliptic (A : WeierstrassCurve ℚ[X]) (r : ℚ) [(fiber A r).IsElliptic] :
    ((series A r).map PowerSeries.constantCoeff).IsElliptic := by
  rw [series_constant]
  infer_instance

instance laurent_elliptic (A : WeierstrassCurve ℚ[X]) (r : ℚ) [(generic A).IsElliptic] :
    ((series A r).map (algebraMap PS LS)).IsElliptic := by
  rw [series_laurent]
  infer_instance

def localPointMap (A : WeierstrassCurve ℚ[X]) (r : ℚ) :
    (generic A).toAffine.Point →+ ((series A r).map (algebraMap PS LS)).toAffine.Point :=
  (PointScaling.pointCongr (series_laurent A r).symm).toAddMonoidHom.comp
    (fieldPointMap (baseEmbedding r) (generic A))

theorem localPointMap_coordinates (A : WeierstrassCurve ℚ[X]) (r : ℚ)
    (x y : ℚ[X]) (h : (generic A).toAffine.Nonsingular (polynomialMap x) (polynomialMap y)) :
    encode (localPointMap A r (.some _ _ h))=
      some (algebraMap PS LS (polynomialSeries r x),algebraMap PS LS (polynomialSeries r y)) := by
  rw [localPointMap,AddMonoidHom.comp_apply,AddEquiv.coe_toAddMonoidHom,
    PointScaling.encode_pointCongr,encode_fieldPointMap]
  simp only [encode,Option.map_some,baseEmbedding_polynomial,polynomialLaurent,RingHom.comp_apply]

theorem exists_specialization (hFormal : FormalGoodReductionHomomorphisms)
    (A : WeierstrassCurve ℚ[X]) (r : ℚ) [(generic A).IsElliptic] [(fiber A r).IsElliptic] :
    ∃ spec : (generic A).toAffine.Point →+ (fiber A r).toAffine.Point,
      ∀ (x y : ℚ[X]) (h : (generic A).toAffine.Nonsingular (polynomialMap x) (polynomialMap y)),
        encode (spec (.some _ _ h))=some (x.eval r,y.eval r) := by
  obtain ⟨red,hred⟩ := hFormal ℚ (series A r) inferInstance inferInstance
  let spec : (generic A).toAffine.Point →+ (fiber A r).toAffine.Point :=
    (PointScaling.pointCongr (series_constant A r)).toAddMonoidHom.comp
      (red.comp (localPointMap A r))
  refine ⟨spec,?_⟩
  intro x y h
  have he := localPointMap_coordinates A r x y h
  obtain ⟨hN,hshape⟩ :
      ∃ hN : ((series A r).map (algebraMap PS LS)).toAffine.Nonsingular
        (algebraMap PS LS (polynomialSeries r x)) (algebraMap PS LS (polynomialSeries r y)),
        localPointMap A r (.some _ _ h)=.some _ _ hN := by
    cases hp : localPointMap A r (.some _ _ h) with
    | zero => simp only [hp,encode] at he; cases he
    | some a b hN =>
      rw [hp] at he
      obtain ⟨ha,hb⟩ := Prod.mk.inj (Option.some.inj he)
      subst a
      subst b
      exact ⟨hN,rfl⟩
  obtain ⟨hres,hvalue⟩ := hred (polynomialSeries r x) (polynomialSeries r y) hN
  change encode (PointScaling.pointCongr (series_constant A r)
    (red (localPointMap A r (.some _ _ h))))=_
  rw [PointScaling.encode_pointCongr,hshape,hvalue]
  simp only [encode,polynomialSeries_constant]

end
end Z2Z4Rank6.PolynomialWeierstrassSpecialization
