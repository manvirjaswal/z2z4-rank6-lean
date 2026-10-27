module

public import Z2Z4Rank6.GTorsionCoverProjectiveSmooth
public import Z2Z4Rank6.GTorsionCoverPoints

@[expose] public section

/-! Full scheme rational points of the signed second torsion cover.
Source: Jaswal, Section 7, DOI 10.5281/zenodo.23437117. -/
namespace Z2Z4Rank6.GTorsionCoverProjectiveRationalPoints
noncomputable section
open scoped Classical
open AlgebraicGeometry CategoryTheory
open GTorsionCoverProjective GTorsionCoverProjectiveCharts GTorsionCoverPolynomialData
open GTorsionCoverPoints
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

def zInclusion (ε:Bool) : GTorsionCoverAffine.scheme ε⟶scheme ε :=
  (zChartSchemeIso ε).inv≫(zOpen ε).ι
instance zInclusion_openImmersion (ε:Bool) : IsOpenImmersion (zInclusion ε) := by
  dsimp only [zInclusion]
  infer_instance

theorem zInclusion_opensRange (ε:Bool) : (zInclusion ε).opensRange=zOpen ε := by
  dsimp only [zInclusion]
  rw [Scheme.Hom.opensRange_comp_of_isIso,Scheme.Opens.opensRange_ι]

def pointMorphism (ε:Bool) (P:SquareLift ε) : Source⟶scheme ε :=
  affineRationalPointEquiv ε P≫zInclusion ε

theorem pointMorphism_injective (ε:Bool) : Function.Injective (pointMorphism ε) := by
  intro P Q h
  apply (affineRationalPointEquiv ε).injective
  exact (cancel_mono (zInclusion ε)).mp h

theorem zInclusion_structureMap (ε:Bool) :
    zInclusion ε≫structureMap ε=GTorsionCoverAffine.structureMap ε := by
  rw [zInclusion,Category.assoc,←zChartSchemeIso_structureMap,Iso.inv_hom_id_assoc]

theorem pointMorphism_over (ε:Bool) (P:SquareLift ε) :
    pointMorphism ε P≫structureMap ε=𝟙 Source := by
  rw [pointMorphism,Category.assoc,zInclusion_structureMap]
  change Spec.map (CommRingCat.ofHom (evaluation ε P).toRingHom)≫
    Spec.map (CommRingCat.ofHom (algebraMap ℚ (GTorsionCoverAffine.CoordinateRing ε)))=𝟙 Source
  rw [←Spec.map_comp]
  have h : CommRingCat.ofHom (algebraMap ℚ (GTorsionCoverAffine.CoordinateRing ε))≫
      CommRingCat.ofHom (evaluation ε P).toRingHom=𝟙 (CommRingCat.of ℚ) := by
    apply CommRingCat.hom_ext
    exact RingHom.ext_rat _ _
  rw [h,Spec.map_id]

abbrev RationalPoint (ε:Bool) := {p:Source⟶scheme ε // p≫structureMap ε=𝟙 Source}
def fromAffine (ε:Bool) (P:SquareLift ε) : RationalPoint ε :=
  ⟨pointMorphism ε P,pointMorphism_over ε P⟩

theorem range_subset_of_mem (ε:Bool) (p:Source⟶scheme ε) (U:(scheme ε).Opens)
    (h:p sourcePoint∈U) : Set.range p⊆U := by
  rintro _ ⟨x,rfl⟩
  obtain rfl := Subsingleton.elim x sourcePoint
  exact h

/-- Degree-one m,z coordinates make the overlap precisely z/m≠0. -/
theorem mChart_preimage_zOpen (ε:Bool) :
    chartInclusion ε 0 ⁻¹ᵁ zOpen ε=PrimeSpectrum.basicOpen (mRatio ε 2) := by
  change Proj.awayι (grading ε) (m ε) (coordinate_degree ε 0) (weights_pos 0) ⁻¹ᵁ
    Proj.basicOpen (grading ε) (z ε)=_
  rw [Proj.awayι_preimage_basicOpen (grading ε) (coordinate_degree ε 0) (weights_pos 0)
    (coordinate_degree ε 2) (weights_pos 2)]
  congr 1
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.Away.isLocalizationElem,HomogeneousLocalization.Away.val_mk,
    mRatio,ratio,WeightedProjectiveChartHelpers.fraction,
    show weights (0:Fin 4)=1 from rfl,show weights (2:Fin 4)=1 from rfl,pow_one]

instance chartInclusion_openImmersion (ε:Bool) (k:Fin 4) : IsOpenImmersion (chartInclusion ε k) := by
  dsimp only [chartInclusion]
  infer_instance

theorem ratio_zero_of_outside (ε:Bool) (q:Source⟶Spec (CommRingCat.of (ChartRing ε 0)))
    (h:chartInclusion ε 0 (q sourcePoint)∉zOpen ε) :
    (Spec.preimage q).hom (mRatio ε 2)=0 := by
  have hn : q sourcePoint∉PrimeSpectrum.basicOpen (mRatio ε 2) := by
    intro hq
    apply h
    change q sourcePoint∈chartInclusion ε 0 ⁻¹ᵁ zOpen ε
    rwa [mChart_preimage_zOpen]
  rw [←Spec.map_preimage q] at hn
  change ¬¬((Spec.preimage q).hom (mRatio ε 2)=0) at hn
  exact not_not.mp hn

/-- The infinity chart has no rational point with z/m=0. -/
theorem mChart_cannot_lie_outside (ε:Bool) (q:Source⟶Spec (CommRingCat.of (ChartRing ε 0))) :
    chartInclusion ε 0 (q sourcePoint)∈zOpen ε := by
  by_contra hz
  have hz0 := ratio_zero_of_outside ε q hz
  have hu := congrArg (Spec.preimage q).hom (mRatio_u_sq ε)
  simp only [map_pow,GTorsionCoverEquations.map_binary] at hu
  norm_num [GTorsionCoverEquations.binary,map_one,hz0] at hu
  exact (by norm_num:¬IsSquare (99:ℚ)) ⟨(Spec.preimage q).hom (mRatio ε 1),by simpa only [sq] using hu.symm⟩

/-- Every rational scheme point lies in the printed affine chart. -/
theorem rational_point_mem_zOpen (ε:Bool) (p:Source⟶scheme ε) : p sourcePoint∈zOpen ε := by
  by_contra hn
  have hm : p sourcePoint∈mOpen ε := by
    have ht : p sourcePoint∈zOpen ε⊔mOpen ε := by rw [two_chart_cover];trivial
    exact (show p sourcePoint∈zOpen ε∨p sourcePoint∈mOpen ε from ht).resolve_left hn
  have hrange : (chartInclusion ε 0).opensRange=mOpen ε :=
    Proj.opensRange_awayι (grading ε) (m ε) (coordinate_degree ε 0) (weights_pos 0)
  let q := IsOpenImmersion.lift (chartInclusion ε 0) p (by
    change Set.range p⊆(chartInclusion ε 0).opensRange
    rw [hrange]
    exact range_subset_of_mem ε p (mOpen ε) hm)
  have hq : q≫chartInclusion ε 0=p := IsOpenImmersion.lift_fac _ _ _
  apply hn
  simpa only [←Scheme.Hom.comp_apply,hq] using mChart_cannot_lie_outside ε q

def affineMorphismOfPoint (ε:Bool) (p:Source⟶scheme ε) : Source⟶GTorsionCoverAffine.scheme ε :=
  IsOpenImmersion.lift (zInclusion ε) p (by
    change Set.range p⊆(zInclusion ε).opensRange
    rw [zInclusion_opensRange]
    exact range_subset_of_mem ε p (zOpen ε) (rational_point_mem_zOpen ε p))

theorem affineMorphismOfPoint_fac (ε:Bool) (p:Source⟶scheme ε) :
    affineMorphismOfPoint ε p≫zInclusion ε=p := IsOpenImmersion.lift_fac _ _ _

/-- Exact equality of the projective and printed affine rational-point notions. -/
def morphismEquiv (ε:Bool) : SquareLift ε≃(Source⟶scheme ε) where
  toFun:=pointMorphism ε
  invFun p:=(affineRationalPointEquiv ε).symm (affineMorphismOfPoint ε p)
  left_inv P:=by
    apply (affineRationalPointEquiv ε).injective
    simp only [Equiv.apply_symm_apply]
    apply (cancel_mono (zInclusion ε)).mp
    rw [affineMorphismOfPoint_fac]
    rfl
  right_inv p:=by
    change affineRationalPointEquiv ε ((affineRationalPointEquiv ε).symm
      (affineMorphismOfPoint ε p))≫zInclusion ε=p
    rw [Equiv.apply_symm_apply]
    exact affineMorphismOfPoint_fac ε p

theorem every_morphism_over (ε:Bool) (p:Source⟶scheme ε) : p≫structureMap ε=𝟙 Source := by
  obtain ⟨P,rfl⟩ := (morphismEquiv ε).surjective p
  exact pointMorphism_over ε P

/-- Rational-point equivalence over the rational structure map. -/
def rationalPointEquiv (ε:Bool) : SquareLift ε≃RationalPoint ε where
  toFun:=fromAffine ε
  invFun p:=(morphismEquiv ε).symm p.val
  left_inv:=(morphismEquiv ε).left_inv
  right_inv p:=Subtype.ext ((morphismEquiv ε).right_inv p.val)

/-- A rational branch point at m=1 exists for both signs. -/
def branchLift (ε : Bool) : SquareLift ε where
  c := {m := 1,eta := 980,equation := by norm_num [gQuartic]}
  r := 0
  r_sq := by simp [a,b]

def branchPoint (ε:Bool) : RationalPoint ε := fromAffine ε (branchLift ε)

end
end Z2Z4Rank6.GTorsionCoverProjectiveRationalPoints
