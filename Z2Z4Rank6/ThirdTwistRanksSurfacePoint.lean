module

public import Z2Z4Rank6.ThirdTwistRankPoint
public import Z2Z4Rank6.QuadraticRatFuncEquiv

@[expose] public section

/-! The infinite-order point on the n(4n+45)-twist of Y over
Q(n). The n↦m² field embedding and coordinate scaling map
this point to the proved infinite-order q3-twist point over Q(m). -/
namespace Z2Z4Rank6.ThirdTwist.SurfacePoint
noncomputable section
open Common.WeierstrassCoordinates
open GusicTadic
abbrev F := RatFunc ℚ
abbrev m : F := RatFunc.X

theorem m_transcendental : Transcendental ℚ m := by
  convert RatFunc.transcendental_X (K:=ℚ) using 1
  exact Subsingleton.elim _ _

def squareEmbedding : F →+* F :=
  QuadraticRatFuncEquiv.baseEmbedding (m^2)
    (m_transcendental.pow (by decide : 0<(2:ℕ)))

@[simp] theorem squareEmbedding_X : squareEmbedding RatFunc.X=m^2 :=
  QuadraticRatFuncEquiv.baseEmbedding_X _ _

def factor (n : F) : F := n*(4*n+45)
def curve : WeierstrassCurve F :=
  PointScaling.curve (factor RatFunc.X*surfaceS RatFunc.X)
    ((factor RatFunc.X)^2*(surfaceW RatFunc.X)^2)

def A : F := q3 m*((a m)^2+(b m)^2)
def B : F := (q3 m)^2*(a m)^2*(b m)^2

theorem generic_curve_eq : genericModel (twistPolynomial 0)=PointScaling.curve A B := by
  rw [generic_eq_pointScaling]
  change PointScaling.curve (polyToRF q3Poly*_) ((polyToRF q3Poly)^2*_ * _)=_
  rw [q3_image]
  rfl

private theorem map_surfaceS {R S : Type*} [CommRing R] [CommRing S]
    (f : R→+*S) (n : R) : f (surfaceS n)=surfaceS (f n) := by
  simp [surfaceS,map_ofNat]

private theorem map_surfaceW {R S : Type*} [CommRing R] [CommRing S]
    (f : R→+*S) (n : R) : f (surfaceW n)=surfaceW (f n) := by
  simp [surfaceW,map_ofNat]

theorem mapped_curve : curve.map squareEmbedding=PointScaling.curve (m^2*A) (m^4*B) := by
  ext <;> simp [curve,PointScaling.curve,factor,map_surfaceS,map_surfaceW,
    surfaceS_base_change,surfaceW_base_change,A,B,q3,map_ofNat] <;> ring

instance curve_elliptic : curve.IsElliptic := by
  have hd : (curve.map squareEmbedding).Δ=m^12*(genericModel (twistPolynomial 0)).Δ := by
    rw [mapped_curve,generic_curve_eq]
    simp only [PointScaling.curve,WeierstrassCurve.Δ,WeierstrassCurve.b₂,
      WeierstrassCurve.b₄,WeierstrassCurve.b₆,WeierstrassCurve.b₈]
    ring
  constructor
  rw [isUnit_iff_ne_zero]
  intro hz
  have hn := mul_ne_zero (pow_ne_zero 12 RatFunc.X_ne_zero)
    (genericModel (twistPolynomial 0)).isUnit_Δ.ne_zero
  apply hn
  rw [←hd,WeierstrassCurve.map_Δ,hz,map_zero]

private theorem map_surfaceSectionX {R S : Type*} [CommRing R] [CommRing S]
    (f : R→+*S) (n : R) : f (surfaceSectionX n)=surfaceSectionX (f n) := by
  simp [surfaceSectionX,map_ofNat]

private theorem map_surfaceSectionY {R S : Type*} [CommRing R] [CommRing S]
    (f : R→+*S) (n : R) : f (surfaceSectionY n)=surfaceSectionY (f n) := by
  simp [surfaceSectionY,map_ofNat]

theorem mapped_x : squareEmbedding (surfaceSectionX (RatFunc.X:F))=m^2*sectionX m := by
  rw [map_surfaceSectionX,squareEmbedding_X]
  exact (section_base_change m).1

theorem mapped_y : squareEmbedding (surfaceSectionY (RatFunc.X:F))=m^3*sectionY m := by
  rw [map_surfaceSectionY,squareEmbedding_X]
  exact (section_base_change m).2

theorem point_nonsingular : curve.toAffine.Nonsingular
    (surfaceSectionX RatFunc.X) (surfaceSectionY RatFunc.X) := by
  apply (curve.toAffine.map_nonsingular squareEmbedding.injective _ _).mp
  change (curve.map squareEmbedding).toAffine.Nonsingular _ _
  rw [mapped_curve,mapped_x,mapped_y]
  apply PointScaling.scale_nonsingular A B m RatFunc.X_ne_zero
  have hn : (genericModel (twistPolynomial 0)).toAffine.Nonsingular
      (sectionX m) (sectionY m) := by
    apply (genericModel (twistPolynomial 0)).toAffine.equation_iff_nonsingular.mp
    change (twistModel (polyToRF q3Poly) (a m) (b m)).toAffine.Equation _ _
    rw [q3_image]
    exact section_affine_equation m
  rwa [generic_curve_eq] at hn

/-- The printed point, with its Q(n) coordinates, in the group. -/
def point : curve.toAffine.Point :=
  .some (surfaceSectionX RatFunc.X) (surfaceSectionY RatFunc.X) point_nonsingular

/-- The base-change and unscaling homomorphism from the surface twist. -/
def toGeneric : curve.toAffine.Point →+ (genericModel (twistPolynomial 0)).toAffine.Point :=
  (PointScaling.pointCongr generic_curve_eq.symm).toAddMonoidHom.comp
    (((PointScaling.scaleEquiv A B m RatFunc.X_ne_zero).symm.toAddMonoidHom).comp
      ((PointScaling.pointCongr mapped_curve).toAddMonoidHom.comp
        (fieldPointMap squareEmbedding curve)))

theorem toGeneric_point : toGeneric point=genericPoint := by
  apply encode_injective
  simp only [toGeneric,AddMonoidHom.comp_apply,AddEquiv.coe_toAddMonoidHom,
    PointScaling.encode_pointCongr,PointScaling.encode_scaleEquiv_symm,encode_fieldPointMap]
  simp only [point,encode,Option.map_some,mapped_x,mapped_y]
  change some (m⁻¹^2*(m^2*sectionX m),m⁻¹^3*(m^3*sectionY m))=
    some (sectionX m,sectionY m)
  congr 1
  apply Prod.ext <;> field_simp [show m≠0 from RatFunc.X_ne_zero]

/-- The printed Q(n) surface point has infinite order. -/
theorem point_infinite_order (hGT : GusicTadicTheorem11)
    (hOdd : OddPrimeTorsionIntegrality) : ¬IsOfFinAddOrder point := by
  intro h
  apply genericPoint_infinite_order hGT hOdd
  rw [←toGeneric_point]
  exact toGeneric.isOfFinAddOrder h

end
end Z2Z4Rank6.ThirdTwist.SurfacePoint
