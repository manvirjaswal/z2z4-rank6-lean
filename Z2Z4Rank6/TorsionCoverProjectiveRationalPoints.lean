import Z2Z4Rank6.TorsionCoverProjectiveSmooth
import Z2Z4Rank6.BaseCurve

/-!
# Rational points of the signed projective torsion covers

Jaswal, DOI 10.5281/zenodo.23437117, Section 6, Theorem 1.2(c).
Morphisms Spec Q→the weighted Proj cover are identified with the printed
square lifts (c,r),r²=±a(m)b(m). The m-chart has no rational point with z=0,
since U²=15 there. Thus every rational point lies in the displayed
affine chart. This is a scheme-point equivalence.
-/
namespace Z2Z4Rank6.TorsionCoverProjectiveRationalPoints
noncomputable section
open scoped Classical
open AlgebraicGeometry CategoryTheory
open TorsionCoverProjective TorsionCoverProjectiveCharts TorsionCoverPolynomialData
open TorsionHyperelliptic
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

abbrev Source := Spec (CommRingCat.of ℚ)
def sourcePoint : Source := ⟨⊥,inferInstance⟩

theorem affine_u_sq (ε:Bool) : (TorsionCoverAffine.u ε)^2=
    5*(3*(TorsionCoverAffine.m ε)^2+242) := by
  have h := TorsionCoverAffine.root_sq ε 0
  norm_num [TorsionCoverAffine.radicand,affineRadicand] at h
  norm_num only [map_ofNat] at h
  linear_combination h

theorem affine_v_sq (ε:Bool) : (TorsionCoverAffine.v ε)^2=
    5*(2*(TorsionCoverAffine.m ε)^2+243) := by
  have h := TorsionCoverAffine.root_sq ε 1
  norm_num [TorsionCoverAffine.radicand,affineRadicand] at h
  norm_num only [map_ofNat] at h
  linear_combination h

theorem affine_r_sq (ε:Bool) : (TorsionCoverAffine.r ε)^2=
    algebraMap ℚ (TorsionCoverAffine.CoordinateRing ε) (sign ε)*
      a (TorsionCoverAffine.m ε)*b (TorsionCoverAffine.m ε) := by
  have h := TorsionCoverAffine.root_sq ε 2
  norm_num [TorsionCoverAffine.radicand,affineRadicand,a,b] at h
  norm_num only [map_ofNat] at h
  unfold a b
  linear_combination h

/-- Recover all printed coordinates from the affine quotient map. -/
def affinePoint (ε:Bool) (f:TorsionCoverAffine.CoordinateRing ε→ₐ[ℚ]ℚ) : SquareLift ε where
  c:={
    m:=f (TorsionCoverAffine.m ε)
    u:=f (TorsionCoverAffine.u ε)
    v:=f (TorsionCoverAffine.v ε)
    u_sq:=by
      have h := congrArg f (affine_u_sq ε)
      simpa only [map_add,map_mul,map_pow,map_ofNat] using h
    v_sq:=by
      have h := congrArg f (affine_v_sq ε)
      simpa only [map_add,map_mul,map_pow,map_ofNat] using h}
  r:=f (TorsionCoverAffine.r ε)
  r_sq:=by
    have h := congrArg f (affine_r_sq ε)
    simpa only [map_mul,AlgHom.commutes,Algebra.algebraMap_self_apply,map_pow,
      a,b,map_sub,map_add,map_neg,map_ofNat,map_one] using h

/-- Quotient evaluation at a printed square lift. -/
def evaluation (ε:Bool) (P:SquareLift ε) : TorsionCoverAffine.CoordinateRing ε→ₐ[ℚ]ℚ :=
  TripleSquareCover.lift (affineRadicand ε) P.c.m ![P.c.u,P.c.v,P.r] (by
    intro i
    fin_cases i
    · norm_num [affineRadicand]
      linear_combination P.c.u_sq
    · norm_num [affineRadicand]
      linear_combination P.c.v_sq
    · norm_num [affineRadicand,a,b]
      have h := P.r_sq
      dsimp [a,b] at h
      linear_combination h)

@[simp] theorem evaluation_m (ε:Bool) (P:SquareLift ε) : evaluation ε P (TorsionCoverAffine.m ε)=P.c.m := by
  simp [evaluation,TorsionCoverAffine.m]
@[simp] theorem evaluation_u (ε:Bool) (P:SquareLift ε) : evaluation ε P (TorsionCoverAffine.u ε)=P.c.u := by
  simp [evaluation,TorsionCoverAffine.u]
@[simp] theorem evaluation_v (ε:Bool) (P:SquareLift ε) : evaluation ε P (TorsionCoverAffine.v ε)=P.c.v := by
  simp [evaluation,TorsionCoverAffine.v]
@[simp] theorem evaluation_r (ε:Bool) (P:SquareLift ε) : evaluation ε P (TorsionCoverAffine.r ε)=P.r := by
  simp [evaluation,TorsionCoverAffine.r]

@[simp] theorem affinePoint_evaluation (ε:Bool) (P:SquareLift ε) : affinePoint ε (evaluation ε P)=P := by
  ext <;> simp [affinePoint]

@[simp] theorem evaluation_affinePoint (ε:Bool) (f:TorsionCoverAffine.CoordinateRing ε→ₐ[ℚ]ℚ) :
    evaluation ε (affinePoint ε f)=f := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i
  · change evaluation ε (affinePoint ε f) (TorsionCoverAffine.m ε)=f (TorsionCoverAffine.m ε)
    simp [affinePoint]
  · change evaluation ε (affinePoint ε f) (TorsionCoverAffine.u ε)=f (TorsionCoverAffine.u ε)
    simp [affinePoint]
  · change evaluation ε (affinePoint ε f) (TorsionCoverAffine.v ε)=f (TorsionCoverAffine.v ε)
    simp [affinePoint]
  · change evaluation ε (affinePoint ε f) (TorsionCoverAffine.r ε)=f (TorsionCoverAffine.r ε)
    simp [affinePoint]

/-- Full faithfulness of Spec identifies the affine morphisms. -/
def affineRationalPointEquiv (ε:Bool) : SquareLift ε≃(Source⟶TorsionCoverAffine.scheme ε) where
  toFun P:=Spec.map (CommRingCat.ofHom (evaluation ε P).toRingHom)
  invFun p:=affinePoint ε (rationalAlgHom (Spec.preimage p).hom)
  left_inv P:=by
    change affinePoint ε (rationalAlgHom (Spec.preimage
      (Spec.map (CommRingCat.ofHom (evaluation ε P).toRingHom))).hom)=P
    rw [Spec.preimage_map]
    exact affinePoint_evaluation ε P
  right_inv p:=by
    change Spec.map (CommRingCat.ofHom
      (evaluation ε (affinePoint ε (rationalAlgHom (Spec.preimage p).hom))).toRingHom)=p
    rw [evaluation_affinePoint]
    exact Spec.map_preimage p

def zInclusion (ε:Bool) : TorsionCoverAffine.scheme ε⟶scheme ε :=
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
    zInclusion ε≫structureMap ε=TorsionCoverAffine.structureMap ε := by
  rw [zInclusion,Category.assoc,←zChartSchemeIso_structureMap,Iso.inv_hom_id_assoc]

theorem pointMorphism_over (ε:Bool) (P:SquareLift ε) :
    pointMorphism ε P≫structureMap ε=𝟙 Source := by
  rw [pointMorphism,Category.assoc,zInclusion_structureMap]
  change Spec.map (CommRingCat.ofHom (evaluation ε P).toRingHom)≫
    Spec.map (CommRingCat.ofHom (algebraMap ℚ (TorsionCoverAffine.CoordinateRing ε)))=𝟙 Source
  rw [←Spec.map_comp]
  have h : CommRingCat.ofHom (algebraMap ℚ (TorsionCoverAffine.CoordinateRing ε))≫
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
    chartInclusion ε 0 ⁻¹ᵁ zOpen ε=PrimeSpectrum.basicOpen (mRatio ε 3) := by
  change Proj.awayι (grading ε) (m ε) (coordinate_degree ε 0) (weights_pos 0) ⁻¹ᵁ
    Proj.basicOpen (grading ε) (z ε)=_
  rw [Proj.awayι_preimage_basicOpen (grading ε) (coordinate_degree ε 0) (weights_pos 0)
    (coordinate_degree ε 3) (weights_pos 3)]
  congr 1
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.Away.isLocalizationElem,HomogeneousLocalization.Away.val_mk,
    mRatio,ratio,WeightedProjectiveChartHelpers.fraction,
    show weights (0:Fin 5)=1 from rfl,show weights (3:Fin 5)=1 from rfl,pow_one]

instance chartInclusion_openImmersion (ε:Bool) (k:Fin 5) : IsOpenImmersion (chartInclusion ε k) := by
  dsimp only [chartInclusion]
  infer_instance

theorem ratio_zero_of_outside (ε:Bool) (q:Source⟶Spec (CommRingCat.of (ChartRing ε 0)))
    (h:chartInclusion ε 0 (q sourcePoint)∉zOpen ε) :
    (Spec.preimage q).hom (mRatio ε 3)=0 := by
  have hn : q sourcePoint∉PrimeSpectrum.basicOpen (mRatio ε 3) := by
    intro hq
    apply h
    change q sourcePoint∈chartInclusion ε 0 ⁻¹ᵁ zOpen ε
    rwa [mChart_preimage_zOpen]
  rw [←Spec.map_preimage q] at hn
  change ¬¬((Spec.preimage q).hom (mRatio ε 3)=0) at hn
  exact not_not.mp hn

/-- The infinity chart has no rational point with z/m=0. -/
theorem mChart_cannot_lie_outside (ε:Bool) (q:Source⟶Spec (CommRingCat.of (ChartRing ε 0))) :
    chartInclusion ε 0 (q sourcePoint)∈zOpen ε := by
  by_contra hz
  have hz0 := ratio_zero_of_outside ε q hz
  have hu := congrArg (Spec.preimage q).hom (mRatio_u_sq ε)
  simp only [map_add,map_mul,map_pow,map_ofNat,hz0,zero_pow (by decide:2≠0),mul_zero,add_zero] at hu
  exact rational_fifteen_nonsquare ⟨(Spec.preimage q).hom (mRatio ε 1),by simpa only [sq] using hu.symm⟩

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

def affineMorphismOfPoint (ε:Bool) (p:Source⟶scheme ε) : Source⟶TorsionCoverAffine.scheme ε :=
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

/-- The printed branch point (1,35,35,0) exists for either sign. -/
def branchLift (ε:Bool) : SquareLift ε where
  c:=baseOrigin
  r:=0
  r_sq:=by norm_num [baseOrigin,a,b]

def branchPoint (ε:Bool) : RationalPoint ε := fromAffine ε (branchLift ε)

end
end Z2Z4Rank6.TorsionCoverProjectiveRationalPoints
