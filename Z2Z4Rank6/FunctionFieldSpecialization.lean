import Z2Z4Rank6.FunctionField
import Z2Z4Rank6.PointMap
import Mathlib.RingTheory.LaurentSeries
import Z2Z4Rank6.FunctionFieldCoordinates
import Z2Z4Rank6.ReductionCheckRank
import Z2Z4Rank6.TorsionCongruence

/-!
# The published reduction theorem for formal Laurent series

Reference: J. H. Silverman, *The Arithmetic of Elliptic Curves*, second edition,
Graduate Texts in Mathematics 106, Springer, 2009, Chapter VII,
Proposition 2.1, p. 188; the projective coordinate reduction is defined on
p. 187. Chapter VII's standing assumptions, p. 185, are completeness for a
discrete valuation and perfectness of the fraction and residue fields.
https://doi.org/10.1007/978-0-387-09494-6

For a characteristic-zero field F, F[[T]] is a complete discrete valuation
ring with fraction field F((T)) and residue field F via the constant
coefficient. Both fields are perfect. Nonsingular constant reduction makes the
discriminant a unit, so the integral equation is minimal and every point has
nonsingular reduction. The affine clause below is the reduction of coordinates
[x:y:1]. Surjectivity is not needed or asserted here.
-/

namespace Z2Z4Rank6


/-- Good reduction over F[[T]] gives an additive homomorphism from
the F((T))-point group to the F-point group, agreeing with
constant coefficients on integral affine coordinates. -/
def FormalGoodReductionAt {F : Type*} [Field F] [DecidableEq F]
    [DecidableEq (LaurentSeries F)]
    (W : WeierstrassCurve (PowerSeries F)) : Prop :=
  ∃ red : (W.map (algebraMap (PowerSeries F) (LaurentSeries F))).toAffine.Point →+
      (W.map (PowerSeries.constantCoeff : PowerSeries F →+* F)).toAffine.Point,
    ∀ (x y : PowerSeries F)
      (h : (W.map (algebraMap (PowerSeries F) (LaurentSeries F))).toAffine.Nonsingular
        (algebraMap (PowerSeries F) (LaurentSeries F) x)
        (algebraMap (PowerSeries F) (LaurentSeries F) y)),
      ∃ hred : (W.map (PowerSeries.constantCoeff : PowerSeries F →+* F)).toAffine.Nonsingular
          (PowerSeries.constantCoeff x) (PowerSeries.constantCoeff y),
        red (.some _ _ h) = .some (PowerSeries.constantCoeff x) (PowerSeries.constantCoeff y) hred

/-- Silverman's published reduction theorem is available for every
characteristic-zero coefficient field and every formal integral Weierstrass
model with good constant reduction. It is a hypothesis of the specialization argument. -/
def FormalGoodReductionHomomorphisms : Prop :=
  ∀ (F : Type) [Field F] [CharZero F] [DecidableEq F]
    [DecidableEq (LaurentSeries F)] (W : WeierstrassCurve (PowerSeries F)),
    (W.map (PowerSeries.constantCoeff : PowerSeries F →+* F)).IsElliptic →
    (W.map (algebraMap (PowerSeries F) (LaurentSeries F))).IsElliptic →
      FormalGoodReductionAt W

noncomputable section

set_option maxHeartbeats 1000000

open Common.WeierstrassCoordinates

namespace FunctionFieldLocal

local instance : DecidableEq LS := Classical.decEq LS

/-- The generic point group mapped to its formal local model. -/
def localPointMap : (X FunctionField.m).toAffine.Point →+
    (seriesCurve.map (algebraMap PS LS)).toAffine.Point :=
  (pointEquivOfEq seriesCurve_laurent.symm).toAddMonoidHom.comp
    (fieldPointMap embedding (X FunctionField.m))

/-- The coordinates of the six mapped points are fixed by their constructions
in FunctionFieldCoordinates. -/
theorem localPointMap_coordinates (j : Fin 6) :
    encode (localPointMap (FunctionField.points j)) =
      some (algebraMap PS LS (xSeries j),algebraMap PS LS (ySeries j)) := by
  change encode (pointEquivOfEq seriesCurve_laurent.symm
    (fieldPointMap embedding (X FunctionField.m) (FunctionField.points j))) = _
  rw [encode_pointEquivOfEq, encode_fieldPointMap]
  change some (embedding (sixX FunctionField.m j),
    embedding (sixY FunctionField.m FunctionField.u FunctionField.v j)) = _
  rw [embedding_sixX, embedding_sixY]

private theorem localPointMap_shape (j : Fin 6) :
    ∃ h : (seriesCurve.map (algebraMap PS LS)).toAffine.Nonsingular
        (algebraMap PS LS (xSeries j)) (algebraMap PS LS (ySeries j)),
      localPointMap (FunctionField.points j) = .some _ _ h := by
  have henc := localPointMap_coordinates j
  cases hp : localPointMap (FunctionField.points j) with
  | zero =>
    simp only [hp, encode] at henc
    cases henc
  | some x y h =>
    rw [hp] at henc
    change some (x,y) = some (algebraMap PS LS (xSeries j),algebraMap PS LS (ySeries j)) at henc
    have hxy := Option.some.inj henc
    have hx := congrArg Prod.fst hxy
    have hy := congrArg Prod.snd hxy
    dsimp only at hx hy
    subst x
    subst y
    exact ⟨h,rfl⟩

instance baseFiberElliptic : (X baseC0.m).IsElliptic :=
  X_good_of_congruent 0 (baseC0_integral 0).1 rfl

/-- The six printed rational specializations at c0. -/
def basePoints : Fin 6 → (X baseC0.m).toAffine.Point :=
  sixPoints baseC0.m baseC0.u baseC0.v baseC0.u_sq baseC0.v_sq
    (by norm_num [baseC0]) baseC0.u_ne_zero baseC0.v_ne_zero

/-- The published formal good-reduction theorem gives an
additive specialization homomorphism from X(Q(C)) to the original
rational fiber at c0, sending each of the six printed points to its printed
specialization. The function field, formal embedding, integral coordinates and
all six values have been constructed and proved beforehand. -/
theorem exists_specialization_at_base (hFormal : FormalGoodReductionHomomorphisms) :
    ∃ spec : (X FunctionField.m).toAffine.Point →+ (X baseC0.m).toAffine.Point,
      ∀ j : Fin 6, spec (FunctionField.points j) = basePoints j := by
  obtain ⟨red,hred⟩ := hFormal ℚ seriesCurve inferInstance inferInstance
  let spec : (X FunctionField.m).toAffine.Point →+ (X baseC0.m).toAffine.Point :=
    (pointEquivOfEq seriesCurve_constant).toAddMonoidHom.comp (red.comp localPointMap)
  refine ⟨spec, ?_⟩
  intro j
  obtain ⟨h,hshape⟩ := localPointMap_shape j
  obtain ⟨hres,hvalue⟩ := hred (xSeries j) (ySeries j) h
  apply encode_injective (X baseC0.m)
  change encode (pointEquivOfEq seriesCurve_constant (red (localPointMap (FunctionField.points j)))) = _
  rw [encode_pointEquivOfEq, hshape, hvalue]
  change some (PowerSeries.constantCoeff (xSeries j),PowerSeries.constantCoeff (ySeries j)) =
    some (sixX baseC0.m j,sixY baseC0.m baseC0.u baseC0.v j)
  rw [xSeries_constant, ySeries_constant]

/-- Independence of the six rational specializations implies
independence of the six generic points, via the constructed formal place. -/
theorem points_linearIndependent_of_base
    (hFormal : FormalGoodReductionHomomorphisms)
    (hbase : LinearIndependent ℤ basePoints) :
    LinearIndependent ℤ FunctionField.points := by
  obtain ⟨spec,hspec⟩ := exists_specialization_at_base hFormal
  apply Fintype.linearIndependent_iff.mpr
  intro n hn
  apply Fintype.linearIndependent_iff.mp hbase n
  have h := congrArg spec hn
  simpa only [map_sum, map_zsmul, map_zero, hspec] using h

/-- The six rational points at c0 are independent by the checked printed
matrix and the published rational good-reduction theorem. -/
theorem basePoints_linearIndependent
    (hReduction : GoodReductionHomomorphisms) (hT : TorsionExact (X baseC0.m)) :
    LinearIndependent ℤ basePoints := by
  apply sixPoints_linearIndependent_of_reduction_data hReduction baseC0
    (by norm_num [baseC0]) hT
  · intro i
    exact X_integralModel (baseC0_integral i).1
  · intro i
    exact reducedModel_X_of_congruent i (baseC0_integral i).1 rfl
  · intro i j
    exact baseC0.sixX_integral (baseC0_integral i).1 (baseC0_denominator_unit i) j
  · intro i j
    exact baseC0.sixY_integral (baseC0_integral i).1 (baseC0_integral i).2.1
      (baseC0_integral i).2.2 (baseC0_denominator_unit i) j
  · intro i j
    exact (baseC0_section_residues i j).1
  · intro i j
    exact (baseC0_section_residues i j).2

/-- Proposition 5.1's generic independence assertion, in the constructed
function field Q(C). The torsion condition follows from the paper's torsion criterion at c0. -/
theorem points_linearIndependent
    (hFormal : FormalGoodReductionHomomorphisms)
    (hReduction : GoodReductionHomomorphisms) (hT : TorsionExact (X baseC0.m)) :
    LinearIndependent ℤ FunctionField.points :=
  points_linearIndependent_of_base hFormal (basePoints_linearIndependent hReduction hT)

end FunctionFieldLocal

namespace FunctionField

/-- Proposition 5.1: the six printed points in the function field Q(C)
are integer-linearly independent. The hypotheses are Mazur's rational torsion classification and
the two published good-reduction theorems. -/
theorem points_independent
    (hMazur : MazurTorsionTheorem) (hReduction : GoodReductionHomomorphisms)
    (hFormal : FormalGoodReductionHomomorphisms) :
    LinearIndependent ℤ points := by
  apply FunctionFieldLocal.points_linearIndependent hFormal hReduction
  apply X_torsion_of_congruent13 hMazur baseC0.m
  exact Or.inl (by norm_num [baseC0])

end FunctionField
end

end Z2Z4Rank6
