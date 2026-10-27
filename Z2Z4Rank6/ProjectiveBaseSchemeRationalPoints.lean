module

public import Z2Z4Rank6.ProjectiveBaseSchemeStructure

@[expose] public section

/-!
# Rational points of the projective base scheme

Jaswal, DOI 10.5281/zenodo.23437117, Lemma 4.1(a) and Theorem 1.2(a).
Rational points here are morphisms Spec Q → Proj C over Spec Q.
The two-chart cover and the nonsquare infinity equations force every such
morphism into the displayed affine chart.
-/
namespace Z2Z4Rank6.ProjectiveBaseSchemeRationalPoints
noncomputable section
open scoped Classical
open AlgebraicGeometry CategoryTheory
open ProjectiveBaseScheme ProjectiveBaseSchemeCharts
set_option backward.isDefEq.respectTransparency false

abbrev Source := Spec (CommRingCat.of ℚ)
def sourcePoint : Source := ⟨⊥,inferInstance⟩

/-- Recover the displayed rational coordinates from an algebra map. -/
def affinePoint (f : AffineBaseScheme.CoordinateRing →ₐ[ℚ] ℚ) : CPoint where
  m:=f AffineBaseScheme.m
  u:=f AffineBaseScheme.u
  v:=f AffineBaseScheme.v
  u_sq:=by
    have h := congrArg f AffineBaseScheme.u_sq
    simp only [map_add,map_mul,map_pow,map_ofNat] at h
    linear_combination h
  v_sq:=by
    have h := congrArg f AffineBaseScheme.v_sq
    simp only [map_add,map_mul,map_pow,map_ofNat] at h
    linear_combination h

@[simp] theorem affinePoint_evaluation (c : CPoint) :
    affinePoint (AffineBaseScheme.evaluation c)=c := by
  ext <;> simp [affinePoint]

@[simp] theorem evaluation_affinePoint (f : AffineBaseScheme.CoordinateRing →ₐ[ℚ] ℚ) :
    AffineBaseScheme.evaluation (affinePoint f)=f := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i
  · change AffineBaseScheme.evaluation (affinePoint f) AffineBaseScheme.m=f AffineBaseScheme.m
    simp [affinePoint]
  · change AffineBaseScheme.evaluation (affinePoint f) AffineBaseScheme.u=f AffineBaseScheme.u
    simp [affinePoint]
  · change AffineBaseScheme.evaluation (affinePoint f) AffineBaseScheme.v=f AffineBaseScheme.v
    simp [affinePoint]

/-- Spec's full faithfulness identifies affine scheme points with the
rational solutions of the two displayed equations. -/
def affineRationalPointEquiv : CPoint ≃ (Source ⟶ AffineBaseScheme.scheme) where
  toFun c := Spec.map (CommRingCat.ofHom (AffineBaseScheme.evaluation c).toRingHom)
  invFun p := affinePoint (rationalAlgHom (Spec.preimage p).hom)
  left_inv c := by
    change affinePoint (rationalAlgHom (Spec.preimage
      (Spec.map (CommRingCat.ofHom (AffineBaseScheme.evaluation c).toRingHom))).hom)=c
    rw [Spec.preimage_map]
    exact affinePoint_evaluation c
  right_inv p := by
    change Spec.map (CommRingCat.ofHom
      (AffineBaseScheme.evaluation (affinePoint (rationalAlgHom (Spec.preimage p).hom))).toRingHom)=p
    rw [evaluation_affinePoint]
    exact Spec.map_preimage p

/-- The open immersion of the displayed affine scheme in the projective scheme. -/
def zInclusion : AffineBaseScheme.scheme ⟶ scheme := zChartSchemeIso.inv ≫ zOpen.ι
instance zInclusion_openImmersion : IsOpenImmersion zInclusion := by
  dsimp only [zInclusion]
  infer_instance

theorem zInclusion_opensRange : zInclusion.opensRange=zOpen := by
  dsimp only [zInclusion]
  rw [Scheme.Hom.opensRange_comp_of_isIso,Scheme.Opens.opensRange_ι]

/-- Projective scheme morphism associated with a printed affine C-point. -/
def pointMorphism (c : CPoint) : Source ⟶ scheme := affineRationalPointEquiv c ≫ zInclusion

theorem pointMorphism_injective : Function.Injective pointMorphism := by
  intro c d h
  apply affineRationalPointEquiv.injective
  exact (cancel_mono zInclusion).mp h

theorem zInclusion_structureMap : zInclusion ≫ structureMap=AffineBaseScheme.structureMap := by
  rw [zInclusion,Category.assoc,←zChartSchemeIso_structureMap,Iso.inv_hom_id_assoc]

theorem pointMorphism_over (c : CPoint) : pointMorphism c ≫ structureMap=𝟙 Source := by
  rw [pointMorphism,Category.assoc,zInclusion_structureMap]
  change Spec.map (CommRingCat.ofHom (AffineBaseScheme.evaluation c).toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap ℚ AffineBaseScheme.CoordinateRing))=𝟙 Source
  rw [←Spec.map_comp]
  have h : (CommRingCat.ofHom (algebraMap ℚ AffineBaseScheme.CoordinateRing) ≫
      CommRingCat.ofHom (AffineBaseScheme.evaluation c).toRingHom)=𝟙 (CommRingCat.of ℚ) := by
    apply CommRingCat.hom_ext
    exact RingHom.ext_rat _ _
  rw [h,Spec.map_id]

/-- Scheme rational points, including their Q-structure compatibility. -/
abbrev RationalPoint := {p : Source ⟶ scheme // p ≫ structureMap=𝟙 Source}

def fromAffine (c : CPoint) : RationalPoint := ⟨pointMorphism c,pointMorphism_over c⟩

/-- A morphism from Spec Q has a single topological image point. -/
theorem range_subset_of_mem (p : Source ⟶ scheme) (U : scheme.Opens)
    (h : p sourcePoint∈U) : Set.range p⊆U := by
  rintro _ ⟨x,rfl⟩
  obtain rfl := Subsingleton.elim x sourcePoint
  exact h

/-- The overlap of the m-chart with z≠0 is precisely the nonzero z/m ratio. -/
theorem mChart_preimage_zOpen :
    chartInclusion 0 ⁻¹ᵁ zOpen=PrimeSpectrum.basicOpen (ratio 0 3) := by
  change Proj.awayι grading m (coordinate_degree 0) (by decide : 0<1) ⁻¹ᵁ
    Proj.basicOpen grading z=_
  rw [Proj.awayι_preimage_basicOpen grading (coordinate_degree 0) (by decide : 0<1)
    (coordinate_degree 3) (by decide : 0<1)]
  congr 1
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.Away.isLocalizationElem,HomogeneousLocalization.Away.val_mk,
    ratio, pow_one]

instance pointChartInclusion_openImmersion (k : Fin 4) : IsOpenImmersion (chartInclusion k) := by
  dsimp only [chartInclusion]
  infer_instance

/-- If a rational m-chart point lies outside z≠0, its z/m value is zero. -/
theorem ratio_zero_of_outside (q : Source ⟶ Spec (CommRingCat.of (ChartRing 0)))
    (h : chartInclusion 0 (q sourcePoint)∉zOpen) :
    (Spec.preimage q).hom (ratio 0 3)=0 := by
  have hn : q sourcePoint∉PrimeSpectrum.basicOpen (ratio 0 3) := by
    intro hq
    apply h
    change q sourcePoint∈chartInclusion 0 ⁻¹ᵁ zOpen
    rwa [mChart_preimage_zOpen]
  rw [←Spec.map_preimage q] at hn
  change ¬¬((Spec.preimage q).hom (ratio 0 3)=0) at hn
  exact not_not.mp hn

/-- The infinity equations have no rational point with z/m=0. -/
theorem mChart_cannot_lie_outside (q : Source ⟶ Spec (CommRingCat.of (ChartRing 0))) :
    chartInclusion 0 (q sourcePoint)∈zOpen := by
  by_contra hz
  have hz0 := ratio_zero_of_outside q hz
  let f : InfinityCoordinateRing →+* ℚ := (Spec.preimage q).hom.comp infinityToChart.toRingHom
  have hfz : f infinityZ=0 := by
    change (Spec.preimage q).hom (infinityToChart infinityZ)=0
    rw [infinityToChart_z]
    exact hz0
  have hu := congrArg f infinity_u_sq
  have hv := congrArg f infinity_v_sq
  simp only [map_add,map_mul,map_pow,map_ofNat,hfz,zero_pow (by decide : 2≠0),mul_zero,zero_add]
    at hu hv
  have hi := projective_infinity_trivial 1 (f infinityU) (f infinityV)
    (by simpa using hu) (by simpa using hv)
  norm_num at hi

/-- Every rational scheme point lies in the displayed affine chart. -/
theorem rational_point_mem_zOpen (p : Source ⟶ scheme) : p sourcePoint∈zOpen := by
  by_contra hn
  have hm : p sourcePoint∈mOpen := by
    have htop : p sourcePoint∈zOpen⊔mOpen := by rw [two_chart_cover]; trivial
    exact (show p sourcePoint∈zOpen∨p sourcePoint∈mOpen from htop).resolve_left hn
  have hrange : (chartInclusion 0).opensRange=mOpen := by
    dsimp only [chartInclusion]
    exact Proj.opensRange_awayι grading m (coordinate_degree 0) (by decide : 0<1)
  have hsubset : Set.range p⊆(chartInclusion 0).opensRange := by
    rw [hrange]
    exact range_subset_of_mem p mOpen hm
  let q := IsOpenImmersion.lift (chartInclusion 0) p hsubset
  have hq : q ≫ chartInclusion 0=p := IsOpenImmersion.lift_fac _ _ _
  apply hn
  have he := mChart_cannot_lie_outside q
  simpa only [←Scheme.Hom.comp_apply,hq] using he

theorem rational_point_range_zOpen (p : Source ⟶ scheme) : Set.range p⊆zOpen :=
  range_subset_of_mem p zOpen (rational_point_mem_zOpen p)

/-- Every projective rational point factors through the affine model. -/
def affineMorphismOfPoint (p : Source ⟶ scheme) : Source ⟶ AffineBaseScheme.scheme :=
  IsOpenImmersion.lift zInclusion p (by
    change Set.range p⊆zInclusion.opensRange
    rw [zInclusion_opensRange]
    exact rational_point_range_zOpen p)

theorem affineMorphismOfPoint_fac (p : Source ⟶ scheme) :
    affineMorphismOfPoint p ≫ zInclusion=p := IsOpenImmersion.lift_fac _ _ _

/-- Affine C-points and all projective scheme morphisms Spec Q→Cbar
are equivalent; in particular, the projective model adds no rational points. -/
def morphismEquiv : CPoint ≃ (Source ⟶ scheme) where
  toFun:=pointMorphism
  invFun p:=affineRationalPointEquiv.symm (affineMorphismOfPoint p)
  left_inv c:=by
    apply affineRationalPointEquiv.injective
    simp only [Equiv.apply_symm_apply]
    apply (cancel_mono zInclusion).mp
    rw [affineMorphismOfPoint_fac]
    rfl
  right_inv p:=by
    change affineRationalPointEquiv (affineRationalPointEquiv.symm
      (affineMorphismOfPoint p)) ≫ zInclusion=p
    rw [Equiv.apply_symm_apply]
    exact affineMorphismOfPoint_fac p

theorem every_morphism_over (p : Source ⟶ scheme) : p ≫ structureMap=𝟙 Source := by
  obtain ⟨c,rfl⟩ := morphismEquiv.surjective p
  exact pointMorphism_over c

/-- Equality of rational-point notions for the affine and
projective models, expressed as an equivalence over Spec Q. -/
def rationalPointEquiv : CPoint ≃ RationalPoint where
  toFun:=fromAffine
  invFun p:=morphismEquiv.symm p.val
  left_inv c:=morphismEquiv.left_inv c
  right_inv p:=Subtype.ext (morphismEquiv.right_inv p.val)

def basePoint : RationalPoint := fromAffine baseC0

end
end Z2Z4Rank6.ProjectiveBaseSchemeRationalPoints
