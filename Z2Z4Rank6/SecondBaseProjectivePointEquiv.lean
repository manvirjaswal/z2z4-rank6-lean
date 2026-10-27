import Z2Z4Rank6.SecondBaseProjectiveCharts
import Z2Z4Rank6.SecondBaseProjectiveRationalPoints

/-! Every rational point of the projective G2 lies in the displayed
affine chart. The Spec-Q morphisms and all three printed square
equations are equivalent, with every coordinate retained. -/

namespace Z2Z4Rank6.SecondBaseProjectivePointEquiv
noncomputable section
open AlgebraicGeometry CategoryTheory
open SecondBaseProjectiveScheme SecondBaseProjectiveCharts
open scoped Classical
set_option backward.isDefEq.respectTransparency false

abbrev Source := SecondBaseProjectiveRationalPoints.Source
def sourcePoint : Source := ⟨⊥,inferInstance⟩

@[simp] theorem ratio_three_eq (i : Fin 4) :
    ratio 3 i=SecondBaseProjectiveRationalPoints.ratio i := rfl

def pointOfChart (f : ChartRing 3→+*ℚ) : SecondFamily.G2Point ℚ where
  W := (f (ratio 3 0))^2
  s1 := f (ratio 3 0)
  s2 := f (ratio 3 1)/1089
  s3 := f (ratio 3 2)/1089
  s1_sq := rfl
  s2_sq := by
    have h := congrArg f (ratio_u_sq 3)
    simp only [map_pow,map_sub,map_mul,map_ofNat,ratio_self,map_one] at h
    simp only [ratio_three_eq] at h
    norm_num [SecondFamily.qA,SecondFamily.beta]
    linear_combination h/1185921
  s3_sq := by
    have h := congrArg f (ratio_v_sq 3)
    simp only [map_pow,map_add,map_neg,map_mul,map_ofNat,ratio_self,map_one] at h
    simp only [ratio_three_eq] at h
    norm_num [SecondFamily.qB,SecondFamily.beta,SecondFamily.gamma]
    linear_combination h/1185921

@[simp] theorem pointOfChart_evaluation (P : SecondFamily.G2Point ℚ) :
    pointOfChart (SecondBaseProjectiveRationalPoints.chartEvaluation P)=P := by
  ext
  · change (SecondBaseProjectiveRationalPoints.chartEvaluation P (ratio 3 0))^2=P.W
    rw [ratio_three_eq,SecondBaseProjectiveRationalPoints.chartEvaluation_ratio]
    exact P.s1_sq
  · simp [pointOfChart]
  · simp [pointOfChart]
  · simp [pointOfChart]

@[simp] theorem evaluation_pointOfChart (f : ChartRing 3→+*ℚ) :
    SecondBaseProjectiveRationalPoints.chartEvaluation (pointOfChart f)=f := by
  apply chartRingHom_ext 3
  intro i
  rw [ratio_three_eq,SecondBaseProjectiveRationalPoints.chartEvaluation_ratio]
  fin_cases i
  · rfl
  · change 1089*(f (ratio 3 1)/1089)=f (ratio 3 1)
    ring
  · change 1089*(f (ratio 3 2)/1089)=f (ratio 3 2)
    ring
  · change 1=f (ratio 3 3)
    simp [ratio_self]

def affineMorphismEquiv : SecondFamily.G2Point ℚ≃(Source⟶Spec (CommRingCat.of (ChartRing 3))) where
  toFun P := Spec.map (CommRingCat.ofHom (SecondBaseProjectiveRationalPoints.chartEvaluation P))
  invFun p := pointOfChart (Spec.preimage p).hom
  left_inv P := by
    change pointOfChart (Spec.preimage
      (Spec.map (CommRingCat.ofHom (SecondBaseProjectiveRationalPoints.chartEvaluation P)))).hom=P
    rw [Spec.preimage_map]
    exact pointOfChart_evaluation P
  right_inv p := by
    change Spec.map (CommRingCat.ofHom
      (SecondBaseProjectiveRationalPoints.chartEvaluation (pointOfChart (Spec.preimage p).hom)))=p
    rw [evaluation_pointOfChart]
    exact Spec.map_preimage p

theorem range_subset_of_mem (p : Source⟶scheme) (U : scheme.Opens)
    (h : p sourcePoint∈U) : Set.range p⊆U := by
  rintro _ ⟨x,rfl⟩
  obtain rfl := Subsingleton.elim x sourcePoint
  exact h

theorem mChart_preimage_zOpen :
    chartInclusion 0 ⁻¹ᵁ zOpen=PrimeSpectrum.basicOpen (ratio 0 3) := by
  change Proj.awayι grading m (coordinate_degree 0) (by decide : 0<1) ⁻¹ᵁ
    Proj.basicOpen grading z=_
  rw [Proj.awayι_preimage_basicOpen grading (coordinate_degree 0) (by decide : 0<1)
    (coordinate_degree 3) (by decide : 0<1)]
  congr 1
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.Away.isLocalizationElem,
    HomogeneousLocalization.Away.val_mk,ratio,pow_one]

theorem ratio_zero_of_outside (q : Source⟶Spec (CommRingCat.of (ChartRing 0)))
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

theorem mChart_cannot_lie_outside (q : Source⟶Spec (CommRingCat.of (ChartRing 0))) :
    chartInclusion 0 (q sourcePoint)∈zOpen := by
  by_contra hz
  have hz0 := ratio_zero_of_outside q hz
  have hu := congrArg (Spec.preimage q).hom (ratio_u_sq 0)
  simp only [map_pow,map_sub,map_mul,map_ofNat,ratio_self,map_one,hz0,zero_pow (by decide : 2≠0),
    mul_zero,sub_zero] at hu
  apply (by norm_num : ¬IsSquare (29:ℚ))
  refine ⟨(Spec.preimage q).hom (ratio 0 1)/1089,?_⟩
  nlinarith [hu]

theorem rational_point_mem_zOpen (p : Source⟶scheme) : p sourcePoint∈zOpen := by
  by_contra hn
  have hm : p sourcePoint∈mOpen := by
    have ht : p sourcePoint∈zOpen⊔mOpen := by rw [two_chart_cover];trivial
    exact (show p sourcePoint∈zOpen∨p sourcePoint∈mOpen from ht).resolve_left hn
  have hrange : (chartInclusion 0).opensRange=mOpen := by
    dsimp only [chartInclusion]
    exact Proj.opensRange_awayι grading m (coordinate_degree 0) (by decide : 0<1)
  have hs : Set.range p⊆(chartInclusion 0).opensRange := by
    rw [hrange]
    exact range_subset_of_mem p mOpen hm
  let q := IsOpenImmersion.lift (chartInclusion 0) p hs
  have hq : q≫chartInclusion 0=p := IsOpenImmersion.lift_fac _ _ _
  apply hn
  have he := mChart_cannot_lie_outside q
  simpa only [←Scheme.Hom.comp_apply,hq] using he

def chartMorphismOfPoint (p : Source⟶scheme) : Source⟶Spec (CommRingCat.of (ChartRing 3)) :=
  IsOpenImmersion.lift (chartInclusion 3) p (by
    change Set.range p⊆(chartInclusion 3).opensRange
    rw [show (chartInclusion 3).opensRange=zOpen from
      Proj.opensRange_awayι grading z (coordinate_degree 3) (by decide : 0<1)]
    exact range_subset_of_mem p zOpen (rational_point_mem_zOpen p))

theorem chartMorphismOfPoint_fac (p : Source⟶scheme) :
    chartMorphismOfPoint p≫chartInclusion 3=p := IsOpenImmersion.lift_fac _ _ _

def morphismEquiv : SecondFamily.G2Point ℚ≃(Source⟶scheme) where
  toFun := SecondBaseProjectiveRationalPoints.pointMorphism
  invFun p := affineMorphismEquiv.symm (chartMorphismOfPoint p)
  left_inv P := by
    apply affineMorphismEquiv.injective
    simp only [Equiv.apply_symm_apply]
    apply (cancel_mono (chartInclusion 3)).mp
    rw [chartMorphismOfPoint_fac]
    rfl
  right_inv p := by
    change affineMorphismEquiv (affineMorphismEquiv.symm (chartMorphismOfPoint p))≫
      chartInclusion 3=p
    rw [Equiv.apply_symm_apply]
    exact chartMorphismOfPoint_fac p

def rationalPointEquiv : SecondFamily.G2Point ℚ≃SecondBaseProjectiveRationalPoints.RationalPoint where
  toFun := SecondBaseProjectiveRationalPoints.fromPrinted
  invFun p := morphismEquiv.symm p.val
  left_inv P := morphismEquiv.left_inv P
  right_inv p := Subtype.ext (morphismEquiv.right_inv p.val)

end
end Z2Z4Rank6.SecondBaseProjectivePointEquiv
