import Z2Z4Rank6.ThirdTwistCoverProjectiveSmooth
import Z2Z4Rank6.ThirdTwistCoverPoints

/-! Full scheme rational points of the third-twist base.
Source: Jaswal, third-twist paragraph, DOI 10.5281/zenodo.23437117. -/
namespace Z2Z4Rank6.ThirdTwistCoverProjectiveRationalPoints
noncomputable section
open scoped Classical
open AlgebraicGeometry CategoryTheory
open ThirdTwistCoverProjective ThirdTwistCoverProjectiveCharts ThirdTwistCoverPolynomialData
open ThirdTwistCoverPoints
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

def zInclusion  : ThirdTwistCoverAffine.scheme⟶scheme :=
  (zChartSchemeIso).inv≫(zOpen).ι
instance zInclusion_openImmersion  : IsOpenImmersion (zInclusion) := by
  dsimp only [zInclusion]
  infer_instance

theorem zInclusion_opensRange  : (zInclusion).opensRange=zOpen := by
  dsimp only [zInclusion]
  rw [Scheme.Hom.opensRange_comp_of_isIso,Scheme.Opens.opensRange_ι]

def pointMorphism  (P:Point) : Source⟶scheme :=
  affineRationalPointEquiv P≫zInclusion

theorem pointMorphism_injective  : Function.Injective (pointMorphism) := by
  intro P Q h
  apply (affineRationalPointEquiv).injective
  exact (cancel_mono (zInclusion)).mp h

theorem zInclusion_structureMap  :
    zInclusion≫structureMap=ThirdTwistCoverAffine.structureMap := by
  rw [zInclusion,Category.assoc,←zChartSchemeIso_structureMap,Iso.inv_hom_id_assoc]

theorem pointMorphism_over  (P:Point) :
    pointMorphism P≫structureMap=𝟙 Source := by
  rw [pointMorphism,Category.assoc,zInclusion_structureMap]
  change Spec.map (CommRingCat.ofHom (evaluation P).toRingHom)≫
    Spec.map (CommRingCat.ofHom (algebraMap ℚ (ThirdTwistCoverAffine.CoordinateRing)))=𝟙 Source
  rw [←Spec.map_comp]
  have h : CommRingCat.ofHom (algebraMap ℚ (ThirdTwistCoverAffine.CoordinateRing))≫
      CommRingCat.ofHom (evaluation P).toRingHom=𝟙 (CommRingCat.of ℚ) := by
    apply CommRingCat.hom_ext
    exact RingHom.ext_rat _ _
  rw [h,Spec.map_id]

abbrev RationalPoint  := {p:Source⟶scheme // p≫structureMap=𝟙 Source}
def fromAffine  (P:Point) : RationalPoint :=
  ⟨pointMorphism P,pointMorphism_over P⟩

theorem range_subset_of_mem  (p:Source⟶scheme) (U:(scheme).Opens)
    (h:p sourcePoint∈U) : Set.range p⊆U := by
  rintro _ ⟨x,rfl⟩
  obtain rfl := Subsingleton.elim x sourcePoint
  exact h

/-- Degree-one m,z coordinates make the overlap precisely z/m≠0. -/
theorem mChart_preimage_zOpen  :
    chartInclusion 0 ⁻¹ᵁ zOpen=PrimeSpectrum.basicOpen (mRatio 3) := by
  change Proj.awayι (grading) (m) (coordinate_degree 0) (weights_pos 0) ⁻¹ᵁ
    Proj.basicOpen (grading) (z)=_
  rw [Proj.awayι_preimage_basicOpen (grading) (coordinate_degree 0) (weights_pos 0)
    (coordinate_degree 3) (weights_pos 3)]
  congr 1
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.Away.isLocalizationElem,HomogeneousLocalization.Away.val_mk,
    mRatio,ratio,WeightedProjectiveChartHelpers.fraction,
    show weights (0:Fin 5)=1 from rfl,show weights (3:Fin 5)=1 from rfl,pow_one]

instance chartInclusion_openImmersion  (k:Fin 5) : IsOpenImmersion (chartInclusion k) := by
  dsimp only [chartInclusion]
  infer_instance

theorem ratio_zero_of_outside  (q:Source⟶Spec (CommRingCat.of (ChartRing 0)))
    (h:chartInclusion 0 (q sourcePoint)∉zOpen) :
    (Spec.preimage q).hom (mRatio 3)=0 := by
  have hn : q sourcePoint∉PrimeSpectrum.basicOpen (mRatio 3) := by
    intro hq
    apply h
    change q sourcePoint∈chartInclusion 0 ⁻¹ᵁ zOpen
    rwa [mChart_preimage_zOpen]
  rw [←Spec.map_preimage q] at hn
  change ¬¬((Spec.preimage q).hom (mRatio 3)=0) at hn
  exact not_not.mp hn

/-- The infinity chart has no rational point with z/m=0. -/
theorem mChart_cannot_lie_outside  (q:Source⟶Spec (CommRingCat.of (ChartRing 0))) :
    chartInclusion 0 (q sourcePoint)∈zOpen := by
  by_contra hz
  have hz0 := ratio_zero_of_outside q hz
  have hu := congrArg (Spec.preimage q).hom (mRatio_u_sq)
  simp only [map_pow,ThirdTwistCoverEquations.map_binary] at hu
  norm_num [ThirdTwistCoverEquations.binary,map_one,hz0] at hu
  exact (by norm_num:¬IsSquare (15:ℚ)) ⟨(Spec.preimage q).hom (mRatio 1),by simpa only [sq] using hu.symm⟩

/-- Every rational scheme point lies in the printed affine chart. -/
theorem rational_point_mem_zOpen  (p:Source⟶scheme) : p sourcePoint∈zOpen := by
  by_contra hn
  have hm : p sourcePoint∈mOpen := by
    have ht : p sourcePoint∈zOpen⊔mOpen := by rw [two_chart_cover];trivial
    exact (show p sourcePoint∈zOpen∨p sourcePoint∈mOpen from ht).resolve_left hn
  have hrange : (chartInclusion 0).opensRange=mOpen :=
    Proj.opensRange_awayι (grading) (m) (coordinate_degree 0) (weights_pos 0)
  let q := IsOpenImmersion.lift (chartInclusion 0) p (by
    change Set.range p⊆(chartInclusion 0).opensRange
    rw [hrange]
    exact range_subset_of_mem p (mOpen) hm)
  have hq : q≫chartInclusion 0=p := IsOpenImmersion.lift_fac _ _ _
  apply hn
  simpa only [←Scheme.Hom.comp_apply,hq] using mChart_cannot_lie_outside q

def affineMorphismOfPoint  (p:Source⟶scheme) : Source⟶ThirdTwistCoverAffine.scheme :=
  IsOpenImmersion.lift (zInclusion) p (by
    change Set.range p⊆(zInclusion).opensRange
    rw [zInclusion_opensRange]
    exact range_subset_of_mem p (zOpen) (rational_point_mem_zOpen p))

theorem affineMorphismOfPoint_fac  (p:Source⟶scheme) :
    affineMorphismOfPoint p≫zInclusion=p := IsOpenImmersion.lift_fac _ _ _

/-- Exact equality of the projective and printed affine rational-point notions. -/
def morphismEquiv  : Point≃(Source⟶scheme) where
  toFun:=pointMorphism
  invFun p:=(affineRationalPointEquiv).symm (affineMorphismOfPoint p)
  left_inv P:=by
    apply (affineRationalPointEquiv).injective
    simp only [Equiv.apply_symm_apply]
    apply (cancel_mono (zInclusion)).mp
    rw [affineMorphismOfPoint_fac]
    rfl
  right_inv p:=by
    change affineRationalPointEquiv ((affineRationalPointEquiv).symm
      (affineMorphismOfPoint p))≫zInclusion=p
    rw [Equiv.apply_symm_apply]
    exact affineMorphismOfPoint_fac p

theorem every_morphism_over  (p:Source⟶scheme) : p≫structureMap=𝟙 Source := by
  obtain ⟨P,rfl⟩ := (morphismEquiv).surjective p
  exact pointMorphism_over P

/-- Rational-point equivalence over the rational structure map. -/
def rationalPointEquiv  : Point≃RationalPoint where
  toFun:=fromAffine
  invFun p:=(morphismEquiv).symm p.val
  left_inv:=(morphismEquiv).left_inv
  right_inv p:=Subtype.ext ((morphismEquiv).right_inv p.val)

/-- A rational point over m=1, on all three quadratic radicals. -/
def branchLift : Point where
  m := 1
  u := 35
  v := 35
  w := 7
  u_sq := by norm_num
  v_sq := by norm_num
  w_sq := by norm_num

def branchPoint  : RationalPoint := fromAffine (branchLift)

end
end Z2Z4Rank6.ThirdTwistCoverProjectiveRationalPoints
