import Z2Z4Rank6.ECProjectiveSchemeSmooth

/-!
# Scheme rational points of the printed EC cubic

Jaswal, DOI 10.5281/zenodo.23437117, Theorem 1.2(a), Lemma 4.1.
Morphisms Spec Q→ProjEC are identified with Mathlib's nonsingular
Weierstrass points, including the unique point at infinity. The affine
coordinates and the exceptional infinity point are checked on charts.
-/
namespace Z2Z4Rank6.ECProjectiveSchemeRationalPoints
noncomputable section
open scoped Classical
open AlgebraicGeometry CategoryTheory
open ECProjectiveScheme ECProjectiveSchemeCharts
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

abbrev Source := Spec (CommRingCat.of ℚ)
def sourcePoint : Source := ⟨⊥,inferInstance⟩

@[ext] structure AffinePoint where
  x : ℚ
  y : ℚ
  equation : EC.toAffine.Equation x y

def affinePoint (f:ECProjectiveSchemeAffine.CoordinateRing→ₐ[ℚ]ℚ) : AffinePoint where
  x:=f ECProjectiveSchemeAffine.x
  y:=f ECProjectiveSchemeAffine.y
  equation:=by
    apply (ec_equation_iff _ _).mpr
    have h := congrArg f ECProjectiveSchemeAffine.equation
    simpa only [map_pow,map_add,map_sub,map_mul,map_ofNat] using h

@[simp] theorem evaluation_x (a b:ℚ) (h:EC.toAffine.Equation a b) :
    ECProjectiveSchemeAffine.evaluation a b h ECProjectiveSchemeAffine.x=a := by
  change (MvPolynomial.aeval ![a,b]) (MvPolynomial.X 0)=a
  simp
@[simp] theorem evaluation_y (a b:ℚ) (h:EC.toAffine.Equation a b) :
    ECProjectiveSchemeAffine.evaluation a b h ECProjectiveSchemeAffine.y=b := by
  change (MvPolynomial.aeval ![a,b]) (MvPolynomial.X 1)=b
  simp

@[simp] theorem affinePoint_evaluation (P:AffinePoint) :
    affinePoint (ECProjectiveSchemeAffine.evaluation P.x P.y P.equation)=P := by
  ext <;> simp [affinePoint]

theorem evaluation_affinePoint (f:ECProjectiveSchemeAffine.CoordinateRing→ₐ[ℚ]ℚ) :
    ECProjectiveSchemeAffine.evaluation (affinePoint f).x (affinePoint f).y
      (affinePoint f).equation=f := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i
  · change ECProjectiveSchemeAffine.evaluation (affinePoint f).x (affinePoint f).y
      (affinePoint f).equation ECProjectiveSchemeAffine.x=f ECProjectiveSchemeAffine.x
    simp [affinePoint]
  · change ECProjectiveSchemeAffine.evaluation (affinePoint f).x (affinePoint f).y
      (affinePoint f).equation ECProjectiveSchemeAffine.y=f ECProjectiveSchemeAffine.y
    simp [affinePoint]

def affineMorphismEquiv : AffinePoint≃(Source⟶ECProjectiveSchemeAffine.scheme) where
  toFun P:=Spec.map (CommRingCat.ofHom
    (ECProjectiveSchemeAffine.evaluation P.x P.y P.equation).toRingHom)
  invFun p:=affinePoint (rationalAlgHom (Spec.preimage p).hom)
  left_inv P:=by
    change affinePoint (rationalAlgHom (Spec.preimage (Spec.map (CommRingCat.ofHom
      (ECProjectiveSchemeAffine.evaluation P.x P.y P.equation).toRingHom))).hom)=P
    rw [Spec.preimage_map]
    exact affinePoint_evaluation P
  right_inv p:=by
    change Spec.map (CommRingCat.ofHom
      (ECProjectiveSchemeAffine.evaluation _ _ _).toRingHom)=p
    rw [evaluation_affinePoint]
    exact Spec.map_preimage p

def zInclusion : ECProjectiveSchemeAffine.scheme⟶scheme := zChartSchemeIso.inv≫zOpen.ι
instance zInclusion_openImmersion : IsOpenImmersion zInclusion := by
  dsimp only [zInclusion]
  infer_instance

theorem zInclusion_opensRange : zInclusion.opensRange=zOpen := by
  dsimp only [zInclusion]
  rw [Scheme.Hom.opensRange_comp_of_isIso,Scheme.Opens.opensRange_ι]

theorem zInclusion_structureMap : zInclusion≫structureMap=ECProjectiveSchemeAffine.structureMap := by
  rw [zInclusion,Category.assoc,←zChartSchemeIso_structureMap,Iso.inv_hom_id_assoc]

/-- The point map uses the affine quotient and the infinity morphism. -/
def pointMorphism : RationalPoints EC→(Source⟶scheme)
  | .zero=>infinityPoint
  | .some a b h=>affineMorphismEquiv ⟨a,b,h.1⟩≫zInclusion

theorem affine_morphism_mem_zOpen (q:Source⟶ECProjectiveSchemeAffine.scheme) :
    (q≫zInclusion) sourcePoint∈zOpen := by
  rw [←zInclusion_opensRange]
  exact ⟨q sourcePoint,rfl⟩

theorem pointMorphism_injective : Function.Injective pointMorphism := by
  intro P Q h
  cases P with
  | zero=>
    cases Q with
    | zero=>rfl
    | some a b hb=>
      have he := congrArg (fun p:Source⟶scheme=>p sourcePoint) h
      exact False.elim (infinityPoint_not_mem_zOpen sourcePoint
        (he ▸ affine_morphism_mem_zOpen (affineMorphismEquiv ⟨a,b,hb.1⟩)))
  | some a b ha=>
    cases Q with
    | zero=>
      have he := congrArg (fun p:Source⟶scheme=>p sourcePoint) h
      exact False.elim (infinityPoint_not_mem_zOpen sourcePoint
        (he ▸ affine_morphism_mem_zOpen (affineMorphismEquiv ⟨a,b,ha.1⟩)))
    | some c d hb=>
      have he := affineMorphismEquiv.injective ((cancel_mono zInclusion).mp h)
      have hx := congrArg AffinePoint.x he
      have hy := congrArg AffinePoint.y he
      dsimp at hx hy
      cases hx
      cases hy
      rfl

instance chartInclusion_openImmersion (k:Fin 3) : IsOpenImmersion (chartInclusion k) := by
  dsimp only [chartInclusion]
  infer_instance

theorem yChart_preimage_zOpen : chartInclusion 1 ⁻¹ᵁ zOpen=PrimeSpectrum.basicOpen (ratio 1 2) := by
  change Proj.awayι grading y (coordinate_degree 1) (by decide:0<1) ⁻¹ᵁ
    Proj.basicOpen grading z=_
  rw [Proj.awayι_preimage_basicOpen grading (coordinate_degree 1) (by decide:0<1)
    (coordinate_degree 2) (by decide:0<1)]
  congr 1
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.Away.isLocalizationElem,HomogeneousLocalization.Away.val_mk,
    ratio,pow_one]

theorem ratio_zero_of_outside (q:Source⟶Spec (CommRingCat.of (ChartRing 1)))
    (h:chartInclusion 1 (q sourcePoint)∉zOpen) : (Spec.preimage q).hom (ratio 1 2)=0 := by
  have hn : q sourcePoint∉PrimeSpectrum.basicOpen (ratio 1 2) := by
    intro hq
    apply h
    change q sourcePoint∈chartInclusion 1 ⁻¹ᵁ zOpen
    rwa [yChart_preimage_zOpen]
  rw [←Spec.map_preimage q] at hn
  change ¬¬((Spec.preimage q).hom (ratio 1 2)=0) at hn
  exact not_not.mp hn

/-- On the Y-chart, Z/Y=0 forces X/Y=0 and hence the infinity point. -/
theorem yChart_outside_eq_infinity (q:Source⟶Spec (CommRingCat.of (ChartRing 1)))
    (h:chartInclusion 1 (q sourcePoint)∉zOpen) :
    q=Spec.map (CommRingCat.ofHom infinityChartEvaluation.toRingHom) := by
  have hz := ratio_zero_of_outside q h
  let f : ECProjectiveSchemeInfinity.CoordinateRing→+*ℚ :=
    (Spec.preimage q).hom.comp ECProjectiveSchemeInfinity.infinityToChart.toRingHom
  have hfz : f ECProjectiveSchemeInfinity.z=0 := by
    change (Spec.preimage q).hom (ECProjectiveSchemeInfinity.infinityToChart ECProjectiveSchemeInfinity.z)=0
    rw [ECProjectiveSchemeInfinity.infinityToChart_z]
    exact hz
  have hx : f ECProjectiveSchemeInfinity.x=0 := by
    have he := congrArg f ECProjectiveSchemeInfinity.equation
    simp only [map_add,map_sub,map_mul,map_pow,map_ofNat,hfz,zero_pow (by decide:2≠0),
      zero_pow (by decide:3≠0),mul_zero,sub_zero,add_zero] at he
    exact (pow_eq_zero_iff (by decide:3≠0)).mp (by simpa using he.symm)
  have hrx : (Spec.preimage q).hom (ratio 1 0)=0 := by
    change (Spec.preimage q).hom
      (ECProjectiveSchemeInfinity.infinityToChart ECProjectiveSchemeInfinity.x)=0 at hx
    rwa [ECProjectiveSchemeInfinity.infinityToChart_x] at hx
  have he : rationalAlgHom (Spec.preimage q).hom=infinityChartEvaluation := by
    apply chartAlgHom_ext 1
    intro i
    fin_cases i
    · rw [infinityChartEvaluation_ratio]
      change (Spec.preimage q).hom (ratio 1 0)=0
      exact hrx
    · simp [ratio_self]
    · rw [infinityChartEvaluation_ratio]
      change (Spec.preimage q).hom (ratio 1 2)=0
      exact hz
  rw [←Spec.map_preimage q]
  congr 1
  exact congrArg (fun g:ChartRing 1→ₐ[ℚ]ℚ=>CommRingCat.ofHom g.toRingHom) he

private theorem range_subset_of_mem (p:Source⟶scheme) (U:scheme.Opens)
    (h:p sourcePoint∈U) : Set.range p⊆U := by
  rintro _ ⟨x,rfl⟩
  obtain rfl := Subsingleton.elim x sourcePoint
  exact h

/-- Every rational scheme point outside Z≠0 is the infinity morphism. -/
theorem outside_eq_infinity (p:Source⟶scheme) (h:p sourcePoint∉zOpen) : p=infinityPoint := by
  have hy : p sourcePoint∈yOpen := by
    have ht : p sourcePoint∈zOpen⊔yOpen := by rw [two_chart_cover];trivial
    exact (show p sourcePoint∈zOpen∨p sourcePoint∈yOpen from ht).resolve_left h
  have hrange : (chartInclusion 1).opensRange=yOpen := by
    exact Proj.opensRange_awayι grading y (coordinate_degree 1) (by decide:0<1)
  let q := IsOpenImmersion.lift (chartInclusion 1) p (by
    change Set.range p⊆(chartInclusion 1).opensRange
    rw [hrange]
    exact range_subset_of_mem p yOpen hy)
  have hq : q≫chartInclusion 1=p := IsOpenImmersion.lift_fac _ _ _
  have he := yChart_outside_eq_infinity q (by simpa only [←Scheme.Hom.comp_apply,hq] using h)
  rw [←hq,he]
  rfl

theorem pointMorphism_surjective : Function.Surjective pointMorphism := by
  intro p
  by_cases hp:p sourcePoint∈zOpen
  · let q := IsOpenImmersion.lift zInclusion p (by
      change Set.range p⊆zInclusion.opensRange
      rw [zInclusion_opensRange]
      exact range_subset_of_mem p zOpen hp)
    let P := affineMorphismEquiv.symm q
    refine ⟨WeierstrassCurve.Affine.Point.mk P.equation,?_⟩
    change affineMorphismEquiv (affineMorphismEquiv.symm q)≫zInclusion=p
    rw [Equiv.apply_symm_apply]
    exact IsOpenImmersion.lift_fac _ _ _
  · exact ⟨.zero,(outside_eq_infinity p hp).symm⟩

def morphismEquiv : RationalPoints EC≃(Source⟶scheme) :=
  Equiv.ofBijective pointMorphism ⟨pointMorphism_injective,pointMorphism_surjective⟩

/-- Every morphism Spec Q→EC is automatically a morphism over Q. -/
theorem pointMorphism_over (P:RationalPoints EC) : pointMorphism P≫structureMap=𝟙 Source := by
  cases P with
  | zero=>exact infinityPoint_over
  | some a b h=>
    rw [pointMorphism,Category.assoc,zInclusion_structureMap]
    change Spec.map (CommRingCat.ofHom (ECProjectiveSchemeAffine.evaluation a b h.1).toRingHom)≫
      Spec.map (CommRingCat.ofHom (algebraMap ℚ ECProjectiveSchemeAffine.CoordinateRing))=𝟙 Source
    rw [←Spec.map_comp]
    have he : CommRingCat.ofHom (algebraMap ℚ ECProjectiveSchemeAffine.CoordinateRing)≫
        CommRingCat.ofHom (ECProjectiveSchemeAffine.evaluation a b h.1).toRingHom=
          𝟙 (CommRingCat.of ℚ) := by
      apply CommRingCat.hom_ext
      exact RingHom.ext_rat _ _
    rw [he,Spec.map_id]

/-- Every scheme morphism from Spec Q respects the printed Q-structure. -/
theorem every_morphism_over (p:Source⟶scheme) : p≫structureMap=𝟙 Source := by
  obtain ⟨P,rfl⟩ := pointMorphism_surjective p
  exact pointMorphism_over P

abbrev RationalPoint := {p:Source⟶scheme // p≫structureMap=𝟙 Source}

/-- Equivalence between scheme rational points and Mathlib EC points. -/
def rationalPointEquiv : RationalPoints EC≃RationalPoint where
  toFun P:=⟨pointMorphism P,pointMorphism_over P⟩
  invFun p:=morphismEquiv.symm p.val
  left_inv:=morphismEquiv.left_inv
  right_inv p:=Subtype.ext (morphismEquiv.right_inv p.val)

@[simp] theorem rationalPointEquiv_zero : (rationalPointEquiv 0).val=infinityPoint := rfl

@[simp] theorem rationalPointEquiv_some (a b:ℚ) (h:EC.toAffine.Nonsingular a b) :
    (rationalPointEquiv (.some a b h)).val=
      affineMorphismEquiv ⟨a,b,h.1⟩≫zInclusion := rfl

end
end Z2Z4Rank6.ECProjectiveSchemeRationalPoints
