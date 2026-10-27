import Z2Z4Rank6.SecondFunctionFieldCharactersBase
import Z2Z4Rank6.SecondFunctionFieldPointActions
import Z2Z4Rank6.FieldTwistEmbedding

/-! Injective untwisting maps from the four printed base twists
to F(Q(G₂)), with their values on all six printed sections. -/

namespace Z2Z4Rank6.SecondFunctionField.CharactersBase
noncomputable section
open Polynomial SecondFamily Common.WeierstrassCoordinates SecondFunctionFieldLocal
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

abbrev baseEmbedding : Base →+* K := algebraMap Base K
def A : Base := U RatFunc.X
def B : Base := (V RatFunc.X)^2
def twistRoot (j : Fin 6) : K := rootFactor genericBasePoint j

theorem curve_eq_long (j : Fin 6) :
    curve j=PointScaling.curve (twistFactor RatFunc.X j*A) (twistFactor RatFunc.X j^2*B) := rfl

theorem curve_image_eq :
    PointScaling.curve (baseEmbedding A) (baseEmbedding B)=F W := by
  ext <;> simp [A,B,PointScaling.curve,F,twistedF,U,V,lambda,W,map_ofNat]

theorem rootFactor_sq {L : Type*} [Field L] [CharZero L]
    (P : G2Point L) (j : Fin 6) : rootFactor P j^2=twistFactor P.W j := by
  fin_cases j
  · simp [rootFactor,twistFactor]
  · exact P.s2_sq
  · exact P.s2_sq
  · exact P.WqB_square
  · exact P.WqB_square
  · exact P.qH_square

theorem twistRoot_sq (j : Fin 6) :
    twistRoot j^2=baseEmbedding (twistFactor RatFunc.X j) := by
  rw [map_twistFactor]
  exact rootFactor_sq genericBasePoint j

theorem imageFactor_ne_zero (j : Fin 6) : baseEmbedding (twistFactor RatFunc.X j) ≠ 0 := by
  intro h
  apply twistFactor_ne_zero j
  exact baseEmbedding.injective (h.trans baseEmbedding.map_zero.symm)

def embeddingData (j : Fin 6) :
    FieldTwistEmbedding.Data baseEmbedding (twistFactor RatFunc.X j) (twistRoot j) (curve j) (F W) :=
  FieldTwistEmbedding.data (F:=Base) (L:=K) baseEmbedding A B (twistFactor RatFunc.X j)
    (twistRoot j) (twistFactor_ne_zero j) (twistRoot_sq j) (curve j) (F W)
    (curve_eq_long j) curve_image_eq

abbrev embed (j : Fin 6) : (curve j).toAffine.Point →+ PointGroup := (embeddingData j).hom

theorem embed_injective (j : Fin 6) : Function.Injective (embed j) := (embeddingData j).injective


local instance : Algebra ℚ K := DivisionRing.toRatAlgebra

theorem baseEmbedding_polynomial (p : ℚ[X]) :
    baseEmbedding (PolynomialWeierstrassSpecialization.polynomialMap p)=aeval W p := by
  have he : baseEmbedding.comp PolynomialWeierstrassSpecialization.polynomialMap=
      (aeval W).toRingHom := by
    apply Polynomial.ringHom_ext'
    · exact RingHom.ext_rat _ _
    · simp [baseEmbedding,PolynomialWeierstrassSpecialization.polynomialMap,
        RatFunc.algebraMap_X,W]
  exact RingHom.congr_fun he p

theorem generic_embed_point {L : Type*} [Field L] [CharZero L] [DecidableEq L]
    (f : Base →+* L) (P : G2Point L) (hW : P.W ≠ 0)
    (hA : qA P.W ≠ 0) (hB : qB P.W ≠ 0) [(F P.W).IsElliptic]
    (hpoly : ∀ p : ℚ[X], f (PolynomialWeierstrassSpecialization.polynomialMap p)=aeval P.W p)
    (hfactor : ∀ j, f (twistFactor RatFunc.X j)=twistFactor P.W j)
    (j : Fin 6)
    (D : FieldTwistEmbedding.Data f (twistFactor RatFunc.X j) (rootFactor P j) (curve j) (F P.W)) :
    D.hom (point j)=P.sixPoints hW hA hB j := by
  apply encode_injective (F P.W)
  have h := D.coordinates (point j)
  rw [encode_point] at h
  simp only [Option.map_some] at h
  rw [hpoly,hpoly,hfactor] at h
  rw [P.encode_sixPoints,sixX_fraction P hW j,sixY_fraction P hW j,qDenominator_eval]
  exact h

theorem embed_point (j : Fin 6) : embed j (point j)=points j := by
  let : (F genericBasePoint.W).IsElliptic := genericFiberElliptic
  exact generic_embed_point baseEmbedding genericBasePoint W_ne_zero qA_W_ne_zero qB_W_ne_zero
    baseEmbedding_polynomial map_twistFactor j (embeddingData j)

end
end Z2Z4Rank6.SecondFunctionField.CharactersBase
