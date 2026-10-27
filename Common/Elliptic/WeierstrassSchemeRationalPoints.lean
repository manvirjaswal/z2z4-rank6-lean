import Common.Elliptic.WeierstrassSchemeCharts

/-!
# All rational scheme points of a nonsingular Weierstrass cubic

Every Spec Q-valued scheme point is exactly one canonical homogeneous
coordinate evaluation: (x:y:1), or (0:1:0). This proves the point-set bridge to Mathlib.
-/
namespace WeierstrassScheme.RationalPoints
noncomputable section
open scoped Classical
open AlgebraicGeometry CategoryTheory Charts
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1200000
variable (W : WeierstrassCurve ℚ)

abbrev Source := Spec (CommRingCat.of ℚ)
def sourcePoint : Source := ⟨⊥,inferInstance⟩

theorem evaluation_coordinate_unit (e : CoordinateRing W →ₐ[ℚ] ℚ) (k : Fin 3)
    (he : e (coordinate W k)=1) : IsUnit (e.toRingHom (coordinate W k)) := by
  change IsUnit (e (coordinate W k))
  rw [he]
  exact isUnit_one

def chartEvaluation (e : CoordinateRing W →ₐ[ℚ] ℚ) (k : Fin 3)
    (he : e (coordinate W k)=1) : ChartRing W k →ₐ[ℚ] ℚ :=
  rationalAlgHom ((Localization.awayLift e.toRingHom (coordinate W k)
    (evaluation_coordinate_unit W e k he)).comp
      (algebraMap (ChartRing W k) (LocalizedRing W k)))

@[simp] theorem chartEvaluation_ratio (e : CoordinateRing W →ₐ[ℚ] ℚ) (k : Fin 3)
    (he : e (coordinate W k)=1) (i : Fin 3) :
    chartEvaluation W e k he (ratio W k i)=e (coordinate W i) := by
  change Localization.awayLift e.toRingHom (coordinate W k) (evaluation_coordinate_unit W e k he) (ratio W k i).val=_
  rw [ratio_val,map_mul,IsLocalization.Away.lift_eq]
  have hi : Localization.awayLift e.toRingHom (coordinate W k)
      (evaluation_coordinate_unit W e k he) (inverseCoordinate W k)=1 := by
    have h := congrArg (Localization.awayLift e.toRingHom (coordinate W k)
      (evaluation_coordinate_unit W e k he)) (coordinate_mul_inverse W k)
    simp only [map_mul,map_one,IsLocalization.Away.lift_eq] at h
    change e (coordinate W k)*Localization.awayLift e.toRingHom (coordinate W k) _ _=1 at h
    simpa only [he,one_mul] using h
  rw [hi,mul_one]
  rfl

/-- Canonical projective-coordinate evaluation on a chosen chart. -/
def evaluationMorphism (e : CoordinateRing W →ₐ[ℚ] ℚ) (k : Fin 3)
    (he : e (coordinate W k)=1) : Source ⟶ scheme W :=
  Spec.map (CommRingCat.ofHom (chartEvaluation W e k he).toRingHom) ≫ chartInclusion W k

def infinity : Source ⟶ scheme W :=
  evaluationMorphism W (infinityEvaluation W) 1 (by simp)

def affine (x y : ℚ) (h : W.toAffine.Equation x y) : Source ⟶ scheme W :=
  evaluationMorphism W (affineEvaluation W x y h) 2 (by simp)

def pointMorphism : W.toAffine.Point → (Source ⟶ scheme W)
  | .zero => infinity W
  | .some x y h => affine W x y h.1

theorem evaluationMorphism_over (e : CoordinateRing W →ₐ[ℚ] ℚ) (k : Fin 3)
    (he : e (coordinate W k)=1) :
    evaluationMorphism W e k he ≫ structureMap W=𝟙 Source := by
  rw [evaluationMorphism,Category.assoc,chartInclusion_structureMap,←Spec.map_comp]
  have h : CommRingCat.ofHom (algebraMap ℚ (ChartRing W k)) ≫
      CommRingCat.ofHom (chartEvaluation W e k he).toRingHom=𝟙 (CommRingCat.of ℚ) := by
    apply CommRingCat.hom_ext
    exact RingHom.ext_rat _ _
  rw [h,Spec.map_id]

theorem pointMorphism_over (P : W.toAffine.Point) :
    pointMorphism W P ≫ structureMap W=𝟙 Source := by
  cases P <;> exact evaluationMorphism_over W _ _ _

theorem chart_preimage_basicOpen (k i : Fin 3) :
    chartInclusion W k ⁻¹ᵁ Proj.basicOpen (grading W) (coordinate W i)=
      PrimeSpectrum.basicOpen (ratio W k i) := by
  change Proj.awayι (grading W) (coordinate W k) (coordinate_degree W k) (by decide : 0<1)
    ⁻¹ᵁ Proj.basicOpen (grading W) (coordinate W i)=_
  rw [Proj.awayι_preimage_basicOpen _ (coordinate_degree W k) (by decide : 0<1)
    (coordinate_degree W i) (by decide : 0<1)]
  congr 1
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.Away.isLocalizationElem,HomogeneousLocalization.Away.val_mk,
    ratio,pow_one]

theorem infinity_outside_zOpen : infinity W sourcePoint∉zOpen W := by
  change (Spec.map (CommRingCat.ofHom
    (chartEvaluation W (infinityEvaluation W) 1 (by simp)).toRingHom)) sourcePoint∉
      chartInclusion W 1 ⁻¹ᵁ Proj.basicOpen (grading W) (coordinate W 2)
  rw [chart_preimage_basicOpen]
  change ¬chartEvaluation W (infinityEvaluation W) 1 (by simp) (ratio W 1 2)∉sourcePoint.asIdeal
  simp

theorem affine_mem_zOpen (x y : ℚ) (h : W.toAffine.Equation x y) :
    affine W x y h sourcePoint∈zOpen W := by
  change _∈Proj.basicOpen (grading W) (coordinate W 2)
  rw [←chartInclusion_opensRange W 2]
  exact ⟨_,rfl⟩

theorem pointMorphism_injective : Function.Injective (pointMorphism W) := by
  intro P Q h
  cases P with
  | zero =>
    cases Q with
    | zero => rfl
    | some x y hy =>
      have he := congrArg (fun p : Source ⟶ scheme W => p sourcePoint) h
      exact False.elim (infinity_outside_zOpen W (he ▸ affine_mem_zOpen W x y hy.1))
  | some x y hx =>
    cases Q with
    | zero =>
      have he := congrArg (fun p : Source ⟶ scheme W => p sourcePoint) h
      exact False.elim (infinity_outside_zOpen W (he ▸ affine_mem_zOpen W x y hx.1))
    | some a b ha =>
      have he := (cancel_mono (chartInclusion W 2)).mp h
      have hf := congrArg (fun p : Source ⟶ Spec (CommRingCat.of (ChartRing W 2)) =>
        (Spec.preimage p).hom) he
      simp only [Spec.preimage_map] at hf
      change (chartEvaluation W (affineEvaluation W x y hx.1) 2 (by simp)).toRingHom =
        (chartEvaluation W (affineEvaluation W a b ha.1) 2 (by simp)).toRingHom at hf
      have hx' : x=a := by
        calc
          x=chartEvaluation W (affineEvaluation W x y hx.1) 2 (by simp) (ratio W 2 0) := by simp
          _=chartEvaluation W (affineEvaluation W a b ha.1) 2 (by simp) (ratio W 2 0) :=
            RingHom.congr_fun hf _
          _=a := by simp
      have hy' : y=b := by
        calc
          y=chartEvaluation W (affineEvaluation W x y hx.1) 2 (by simp) (ratio W 2 1) := by simp
          _=chartEvaluation W (affineEvaluation W a b ha.1) 2 (by simp) (ratio W 2 1) :=
            RingHom.congr_fun hf _
          _=b := by simp
      cases hx'
      cases hy'
      rfl

private theorem range_subset_of_mem (p : Source ⟶ scheme W) (U : (scheme W).Opens)
    (h : p sourcePoint∈U) : Set.range p⊆U := by
  rintro _ ⟨x,rfl⟩
  obtain rfl := Subsingleton.elim x sourcePoint
  exact h

def evaluationOfMorphism (k : Fin 3) (q : Source ⟶ Spec (CommRingCat.of (ChartRing W k))) :
    ChartRing W k →ₐ[ℚ] ℚ := rationalAlgHom (Spec.preimage q).hom

theorem evaluationOfMorphism_relation (k : Fin 3)
    (q : Source ⟶ Spec (CommRingCat.of (ChartRing W k))) :
    let f := evaluationOfMorphism W k q
    f (ratio W k 1)^2*f (ratio W k 2)+W.a₁*(f (ratio W k 0)*f (ratio W k 1)*f (ratio W k 2))+
      W.a₃*(f (ratio W k 1)*f (ratio W k 2)^2)-f (ratio W k 0)^3-
      W.a₂*(f (ratio W k 0)^2*f (ratio W k 2))-
      W.a₄*(f (ratio W k 0)*f (ratio W k 2)^2)-W.a₆*f (ratio W k 2)^3=0 := by
  have h := congrArg (evaluationOfMorphism W k q) (ratio_relation W k)
  simpa only [map_add,map_sub,map_mul,map_pow,map_zero,AlgHom.commutes,Algebra.algebraMap_self, RingHom.id_apply]
    using h

theorem ratio_zero_of_outside (q : Source ⟶ Spec (CommRingCat.of (ChartRing W 1)))
    (h : chartInclusion W 1 (q sourcePoint)∉zOpen W) :
    evaluationOfMorphism W 1 q (ratio W 1 2)=0 := by
  have hn : q sourcePoint∉PrimeSpectrum.basicOpen (ratio W 1 2) := by
    intro hq
    apply h
    change q sourcePoint∈chartInclusion W 1 ⁻¹ᵁ Proj.basicOpen (grading W) (coordinate W 2)
    rwa [chart_preimage_basicOpen]
  rw [←Spec.map_preimage q] at hn
  change ¬¬((Spec.preimage q).hom (ratio W 1 2)=0) at hn
  exact not_not.mp hn

theorem outside_eq_infinity (p : Source ⟶ scheme W) (h : p sourcePoint∉zOpen W) :
    p=infinity W := by
  have hy : p sourcePoint∈yOpen W := by
    have ht : p sourcePoint∈zOpen W⊔yOpen W := by rw [two_chart_cover]; trivial
    exact (show p sourcePoint∈zOpen W∨p sourcePoint∈yOpen W from ht).resolve_left h
  let q := IsOpenImmersion.lift (chartInclusion W 1) p (by
    change Set.range p⊆(chartInclusion W 1).opensRange
    rw [chartInclusion_opensRange]
    exact range_subset_of_mem W p (yOpen W) hy)
  have hq : q≫chartInclusion W 1=p := IsOpenImmersion.lift_fac _ _ _
  have hz := ratio_zero_of_outside W q (by simpa only [←Scheme.Hom.comp_apply,hq] using h)
  have hx : evaluationOfMorphism W 1 q (ratio W 1 0)=0 := by
    have he := evaluationOfMorphism_relation W 1 q
    dsimp only at he
    simp only [hz,mul_zero,zero_pow (by decide : 2≠0),zero_pow (by decide : 3≠0),
      add_zero,sub_zero] at he
    apply (pow_eq_zero_iff (by decide : 3≠0)).mp
    linear_combination -he
  have he : evaluationOfMorphism W 1 q=chartEvaluation W (infinityEvaluation W) 1 (by simp) := by
    apply chartAlgHom_ext W 1
    intro i
    fin_cases i
    · simpa using hx
    · simp [ratio_self]
    · simpa using hz
  have heq : q=Spec.map (CommRingCat.ofHom
      (chartEvaluation W (infinityEvaluation W) 1 (by simp)).toRingHom) := by
    rw [←Spec.map_preimage q]
    congr 1
    exact congrArg (fun f : ChartRing W 1 →ₐ[ℚ] ℚ => CommRingCat.ofHom f.toRingHom) he
  rw [←hq,heq]
  rfl

theorem pointMorphism_surjective [W.IsElliptic] : Function.Surjective (pointMorphism W) := by
  intro p
  by_cases hp : p sourcePoint∈zOpen W
  · let q := IsOpenImmersion.lift (chartInclusion W 2) p (by
      change Set.range p⊆(chartInclusion W 2).opensRange
      rw [chartInclusion_opensRange]
      exact range_subset_of_mem W p (zOpen W) hp)
    let f := evaluationOfMorphism W 2 q
    have he : W.toAffine.Equation (f (ratio W 2 0)) (f (ratio W 2 1)) := by
      have h := evaluationOfMorphism_relation W 2 q
      dsimp only at h
      simp only [ratio_self,map_one,mul_one,one_pow] at h
      rw [WeierstrassCurve.Affine.equation_iff]
      linear_combination h
    refine ⟨.mk he,?_⟩
    have hf : f=chartEvaluation W (affineEvaluation W _ _ he) 2 (by simp) := by
      apply chartAlgHom_ext W 2
      intro i
      fin_cases i <;> simp [f,ratio_self]
    change Spec.map (CommRingCat.ofHom
      (chartEvaluation W (affineEvaluation W _ _ he) 2 _).toRingHom) ≫ chartInclusion W 2=p
    rw [←hf]
    change Spec.map (Spec.preimage q) ≫ chartInclusion W 2=p
    rw [Spec.map_preimage]
    exact IsOpenImmersion.lift_fac _ _ _
  · exact ⟨.zero,(outside_eq_infinity W p hp).symm⟩

abbrev RationalPoint := {p : Source ⟶ scheme W // p≫structureMap W=𝟙 Source}

def rationalPointEquiv [W.IsElliptic] : W.toAffine.Point ≃ RationalPoint W where
  toFun P := ⟨pointMorphism W P,pointMorphism_over W P⟩
  invFun p := (Equiv.ofBijective (pointMorphism W)
    ⟨pointMorphism_injective W,pointMorphism_surjective W⟩).symm p.val
  left_inv := (Equiv.ofBijective (pointMorphism W)
    ⟨pointMorphism_injective W,pointMorphism_surjective W⟩).left_inv
  right_inv p := Subtype.ext ((Equiv.ofBijective (pointMorphism W)
    ⟨pointMorphism_injective W,pointMorphism_surjective W⟩).right_inv p.val)

end
end WeierstrassScheme.RationalPoints
