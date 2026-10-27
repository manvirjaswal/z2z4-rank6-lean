module

public import Z2Z4Rank6.ConicBase
public import Z2Z4Rank6.UnivariateLocal
public import Z2Z4Rank6.FunctionFieldSpecialization

@[expose] public section

/-!
# The conic specialization in Proposition 7.1(a)

The formal parameter k=35/41+T gives integral m,u and all four coordinates.
The published formal good-reduction theorem then supplies an
additive specialization map with all four values proved.
-/

namespace Z2Z4Rank6.ConicSpecialization

open ConicBase Common.WeierstrassCoordinates

noncomputable section

set_option maxHeartbeats 500000

abbrev PS := PowerSeries ℚ
abbrev LS := LaurentSeries ℚ

local instance localLaurentDecidableEq : DecidableEq LS := Classical.decEq LS

def embedding : K →+* LS := UnivariateLocal.baseEmbedding baseK
def kSeries : PS := UnivariateLocal.mSeries baseK
def denominatorSeries : PS := kSeries^2-15
def mSeries : PS := (kSeries^2-70*kSeries+15)*denominatorSeries⁻¹
def uSeries : PS := (-5*(7*kSeries^2-6*kSeries+105))*denominatorSeries⁻¹

@[simp] theorem kSeries_constant : PowerSeries.constantCoeff kSeries=baseK := by
  simp [kSeries]

theorem denominator_constant_ne_zero : PowerSeries.constantCoeff denominatorSeries ≠ 0 := by
  norm_num [denominatorSeries,kSeries,baseK,map_ofNat]

theorem mSeries_constant : PowerSeries.constantCoeff mSeries=baseC0.m := by
  simpa [mSeries,denominatorSeries,kSeries,mParam,div_eq_mul_inv,
    PowerSeries.constantCoeff_inv,map_ofNat] using base_parameters.1

theorem uSeries_constant : PowerSeries.constantCoeff uSeries=baseC0.u := by
  simpa [uSeries,denominatorSeries,kSeries,uParam,div_eq_mul_inv,
    PowerSeries.constantCoeff_inv,map_ofNat] using base_parameters.2

theorem embedding_m : embedding m=algebraMap PS LS mSeries := by
  rw [mSeries,map_mul,UnivariateLocal.map_series_inv denominatorSeries denominator_constant_ne_zero]
  simp [embedding,m,mParam,k,denominatorSeries,kSeries,map_ofNat,div_eq_mul_inv]

theorem embedding_u : embedding u=algebraMap PS LS uSeries := by
  rw [uSeries,map_mul,UnivariateLocal.map_series_inv denominatorSeries denominator_constant_ne_zero]
  simp [embedding,u,uParam,k,denominatorSeries,kSeries,map_ofNat,div_eq_mul_inv]

def coordinateDenominator : PS := sectionDenominator mSeries

theorem coordinate_denominator_constant_ne_zero :
    PowerSeries.constantCoeff coordinateDenominator ≠ 0 := by
  rw [coordinateDenominator,map_sectionDenominator,mSeries_constant]
  exact FunctionFieldLocal.base_denominator_ne_zero

def xSeries (j : Fin 4) : PS := sectionXNumerator mSeries (column j)*coordinateDenominator⁻¹
def ySeries (j : Fin 4) : PS := sectionYNumerator mSeries uSeries 0 (column j)*coordinateDenominator⁻¹

theorem xSeries_constant (j : Fin 4) : PowerSeries.constantCoeff (xSeries j)=fourX baseC0.m j := by
  rw [xSeries,map_mul,map_sectionXNumerator,PowerSeries.constantCoeff_inv,
    coordinateDenominator,map_sectionDenominator,mSeries_constant]
  rw [← denominator_mul_fourX baseC0.m (by norm_num [baseC0]) (by norm_num [baseC0]) j]
  field_simp [FunctionFieldLocal.base_denominator_ne_zero]

theorem ySeries_constant (j : Fin 4) : PowerSeries.constantCoeff (ySeries j)=fourY baseC0.m baseC0.u j := by
  rw [ySeries,map_mul,map_sectionYNumerator,PowerSeries.constantCoeff_inv,
    coordinateDenominator,map_sectionDenominator,mSeries_constant,uSeries_constant,map_zero]
  rw [← denominator_mul_fourY baseC0.m baseC0.u baseC0.u_sq (by norm_num [baseC0])
    baseC0.u_ne_zero (by norm_num [baseC0]) j]
  field_simp [FunctionFieldLocal.base_denominator_ne_zero]

private theorem denominator_laurent_ne_zero : algebraMap PS LS coordinateDenominator ≠ 0 := by
  have hd : coordinateDenominator ≠ 0 := by
    intro h
    apply coordinate_denominator_constant_ne_zero
    rw [h,map_zero]
  simpa only [map_zero] using (IsFractionRing.injective PS LS).ne hd

private theorem denominator_mul_xSeries (j : Fin 4) :
    coordinateDenominator*xSeries j=sectionXNumerator mSeries (column j) := by
  rw [xSeries,mul_left_comm,PowerSeries.mul_inv_cancel _ coordinate_denominator_constant_ne_zero,mul_one]

private theorem denominator_mul_ySeries (j : Fin 4) :
    coordinateDenominator*ySeries j=sectionYNumerator mSeries uSeries 0 (column j) := by
  rw [ySeries,mul_left_comm,PowerSeries.mul_inv_cancel _ coordinate_denominator_constant_ne_zero,mul_one]

theorem embedding_fourX (j : Fin 4) :
    embedding (fourX m j)=algebraMap PS LS (xSeries j) := by
  apply mul_left_cancel₀ denominator_laurent_ne_zero
  have h := congrArg embedding (denominator_mul_fourX m m_ne_zero first_factor_ne_zero j)
  have he : algebraMap PS LS coordinateDenominator*embedding (fourX m j)=
      algebraMap PS LS (sectionXNumerator mSeries (column j)) := by
    simpa only [coordinateDenominator,map_mul,map_sectionDenominator,map_sectionXNumerator,
      embedding_m] using h
  rw [he,← map_mul,denominator_mul_xSeries]

theorem embedding_fourY (j : Fin 4) :
    embedding (fourY m u j)=algebraMap PS LS (ySeries j) := by
  apply mul_left_cancel₀ denominator_laurent_ne_zero
  have h := congrArg embedding
    (denominator_mul_fourY m u conic_relation m_ne_zero u_ne_zero first_factor_ne_zero j)
  have he : algebraMap PS LS coordinateDenominator*embedding (fourY m u j)=
      algebraMap PS LS (sectionYNumerator mSeries uSeries 0 (column j)) := by
    simpa only [coordinateDenominator,map_mul,map_sectionDenominator,map_sectionYNumerator,
      embedding_m,embedding_u,map_zero] using h
  rw [he,← map_mul,denominator_mul_ySeries]

def seriesCurve : WeierstrassCurve PS := X mSeries

theorem seriesCurve_constant : seriesCurve.map PowerSeries.constantCoeff=X baseC0.m := by
  rw [seriesCurve,FunctionFieldLocal.map_family,mSeries_constant]

theorem seriesCurve_laurent : seriesCurve.map (algebraMap PS LS)=(X m).map embedding := by
  rw [seriesCurve,FunctionFieldLocal.map_family,FunctionFieldLocal.map_family,embedding_m]

instance constantFiberElliptic : (seriesCurve.map PowerSeries.constantCoeff).IsElliptic := by
  rw [seriesCurve_constant]
  exact FunctionFieldLocal.baseFiberElliptic

instance laurentFiberElliptic : (seriesCurve.map (algebraMap PS LS)).IsElliptic := by
  rw [seriesCurve_laurent]
  infer_instance

def localPointMap : (X m).toAffine.Point →+ (seriesCurve.map (algebraMap PS LS)).toAffine.Point :=
  (pointEquivOfEq seriesCurve_laurent.symm).toAddMonoidHom.comp (fieldPointMap embedding (X m))

theorem encode_points (j : Fin 4) : encode (points j)=some (fourX m j,fourY m u j) :=
  encode_fourPoints m u conic_relation m_ne_zero u_ne_zero j

theorem localPointMap_coordinates (j : Fin 4) :
    encode (localPointMap (points j))=some (algebraMap PS LS (xSeries j),algebraMap PS LS (ySeries j)) := by
  change encode (pointEquivOfEq seriesCurve_laurent.symm (fieldPointMap embedding (X m) (points j)))=_
  rw [encode_pointEquivOfEq,encode_fieldPointMap,encode_points]
  change some (embedding (fourX m j),embedding (fourY m u j))=_
  rw [embedding_fourX,embedding_fourY]

private theorem localPointMap_shape (j : Fin 4) :
    ∃ h : (seriesCurve.map (algebraMap PS LS)).toAffine.Nonsingular
        (algebraMap PS LS (xSeries j)) (algebraMap PS LS (ySeries j)),
      localPointMap (points j)=.some _ _ h := by
  have henc := localPointMap_coordinates j
  cases hp : localPointMap (points j) with
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

def basePoints (j : Fin 4) : (X baseC0.m).toAffine.Point := FunctionFieldLocal.basePoints (column j)

theorem exists_specialization (hFormal : FormalGoodReductionHomomorphisms) :
    ∃ spec : (X m).toAffine.Point →+ (X baseC0.m).toAffine.Point,
      ∀ j : Fin 4, spec (points j)=basePoints j := by
  obtain ⟨red,hred⟩ := hFormal ℚ seriesCurve inferInstance inferInstance
  let spec : (X m).toAffine.Point →+ (X baseC0.m).toAffine.Point :=
    (pointEquivOfEq seriesCurve_constant).toAddMonoidHom.comp (red.comp localPointMap)
  refine ⟨spec,?_⟩
  intro j
  obtain ⟨h,hshape⟩ := localPointMap_shape j
  obtain ⟨hres,hvalue⟩ := hred (xSeries j) (ySeries j) h
  apply encode_injective (X baseC0.m)
  change encode (pointEquivOfEq seriesCurve_constant (red (localPointMap (points j))))=_
  rw [encode_pointEquivOfEq,hshape,hvalue]
  change some (PowerSeries.constantCoeff (xSeries j),PowerSeries.constantCoeff (ySeries j))=
    some (sixX baseC0.m (column j),sixY baseC0.m baseC0.u baseC0.v (column j))
  rw [xSeries_constant,ySeries_constant,fourX_eq_sixX,fourY_eq_sixY _ _ baseC0.v]

theorem basePoints_linearIndependent (hMazur : MazurTorsionTheorem)
    (hReduction : GoodReductionHomomorphisms) : LinearIndependent ℤ basePoints := by
  have h6 := FunctionFieldLocal.basePoints_linearIndependent hReduction
    (X_torsion_of_congruent13 hMazur baseC0.m (Or.inl (by norm_num [baseC0])))
  exact h6.comp column column_injective

theorem points_linearIndependent (hMazur : MazurTorsionTheorem)
    (hReduction : GoodReductionHomomorphisms) (hFormal : FormalGoodReductionHomomorphisms) :
    LinearIndependent ℤ points := by
  obtain ⟨spec,hspec⟩ := exists_specialization hFormal
  apply Fintype.linearIndependent_iff.mpr
  intro n hn
  apply Fintype.linearIndependent_iff.mp (basePoints_linearIndependent hMazur hReduction) n
  have h := congrArg spec hn
  simpa only [map_sum,map_zsmul,map_zero,hspec] using h

end
end Z2Z4Rank6.ConicSpecialization

namespace Z2Z4Rank6.ConicBase

/-- Proposition 7.1(a), independence of P₁,P₂,P₃,P₅ in the Q(k)-point
group. The hypotheses are the three published theorems. -/
theorem points_independent (hMazur : MazurTorsionTheorem)
    (hReduction : GoodReductionHomomorphisms) (hFormal : FormalGoodReductionHomomorphisms) :
    LinearIndependent ℤ points := ConicSpecialization.points_linearIndependent hMazur hReduction hFormal

end Z2Z4Rank6.ConicBase
