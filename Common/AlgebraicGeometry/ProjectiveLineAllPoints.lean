module

public import Common.AlgebraicGeometry.ProjectiveLinePointNaturality
public import Common.AlgebraicGeometry.ProjectiveLinePoints

@[expose] public section

/-!
# All linear rational points of the projective line

Every Spec k-valued morphism over Spec k is exactly a finite
coordinate point or infinity. The linearity equation is retained,
including when k has nontrivial field automorphisms.
-/
namespace AlgebraicGeometry.ProjectiveLine
noncomputable section
open CategoryTheory MvPolynomial Charts
set_option backward.isDefEq.respectTransparency false
variable (k : Type) [Field k]

theorem parameterPoint_over (t : Option k) : parameterPoint k t≫structureMap k=𝟙 _ := by
  cases t with
  | none=>simpa [parameterPoint] using infinityPoint_over k k
  | some t=>simpa [parameterPoint] using affinePoint_over k k t

theorem chart_preimage_basicOpen (i j : Fin 2) :
    chartInclusion k i ⁻¹ᵁ Proj.basicOpen (grading k) (coordinate k j)=
      PrimeSpectrum.basicOpen (ratio k i j) := by
  change Proj.awayι (grading k) (coordinate k i) (coordinate_degree k i) (by decide : 0<1)
    ⁻¹ᵁ Proj.basicOpen (grading k) (coordinate k j)=_
  rw [Proj.awayι_preimage_basicOpen _ (coordinate_degree k i) (by decide : 0<1)
    (coordinate_degree k j) (by decide : 0<1)]
  congr 1
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.Away.isLocalizationElem,HomogeneousLocalization.Away.val_mk,
    ratio,pow_one]

def chartMorphismEvaluation (i : Fin 2)
    (q : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (ChartRing k i)))
    (hq : q≫chartInclusion k i≫structureMap k=𝟙 _) : ChartRing k i →ₐ[k] k where
  toRingHom := (Spec.preimage q).hom
  commutes' a := by
    have h : CommRingCat.ofHom (algebraMap k (ChartRing k i))≫Spec.preimage q=𝟙 _ := by
      apply Spec.map_injective
      simpa only [Spec.map_comp,Spec.map_preimage,Spec.map_id,
        ←chartInclusion_structureMap,Category.assoc] using hq
    exact RingHom.congr_fun (CommRingCat.hom_ext_iff.mp h) a

private theorem range_subset_of_mem (p : Spec (CommRingCat.of k) ⟶ scheme k)
    (U : (scheme k).Opens) (h : p (sourcePoint k)∈U) : Set.range p⊆U := by
  rintro _ ⟨x,rfl⟩
  obtain rfl := Subsingleton.elim x (sourcePoint k)
  exact h

theorem parameterPoint_surjective
    (p : Spec (CommRingCat.of k) ⟶ scheme k) (hp : p≫structureMap k=𝟙 _) :
    ∃ t : Option k,parameterPoint k t=p := by
  by_cases hfin : p (sourcePoint k)∈Proj.basicOpen (grading k) (coordinate k 1)
  · let q := IsOpenImmersion.lift (chartInclusion k 1) p (by
      change Set.range p⊆(chartInclusion k 1).opensRange
      rw [chartInclusion_opensRange]
      exact range_subset_of_mem k p _ hfin)
    have hq : q≫chartInclusion k 1=p := IsOpenImmersion.lift_fac _ _ _
    let f := chartMorphismEvaluation k 1 q (by rw [←Category.assoc,hq,hp])
    refine ⟨some (f (ratio k 1 0)), ?_⟩
    change affinePoint k k (f (ratio k 1 0))=p
    rw [affinePoint_eq_chart]
    have hf : f=chartEvaluation 1 (MvPolynomial.aeval ![f (ratio k 1 0),1])
        (by simp [coordinate]) := by
      apply chartAlgHom_ext k 1
      intro j
      fin_cases j <;> simp [coordinate,ratio_self]
    rw [←hf]
    change Spec.map (Spec.preimage q)≫chartInclusion k 1=p
    rw [Spec.map_preimage,hq]
  · have hzero : p (sourcePoint k)∈Proj.basicOpen (grading k) (coordinate k 0) := by
      have ht : p (sourcePoint k)∈⨆ i : Fin 2,Proj.basicOpen (grading k) (coordinate k i) := by
        rw [coordinate_opens_cover]
        trivial
      obtain ⟨i,hi⟩ := TopologicalSpace.Opens.mem_iSup.mp ht
      fin_cases i
      · exact hi
      · exact False.elim (hfin hi)
    let q := IsOpenImmersion.lift (chartInclusion k 0) p (by
      change Set.range p⊆(chartInclusion k 0).opensRange
      rw [chartInclusion_opensRange]
      exact range_subset_of_mem k p _ hzero)
    have hq : q≫chartInclusion k 0=p := IsOpenImmersion.lift_fac _ _ _
    let f := chartMorphismEvaluation k 0 q (by rw [←Category.assoc,hq,hp])
    have hz : f (ratio k 0 1)=0 := by
      have hn : q (sourcePoint k)∉PrimeSpectrum.basicOpen (ratio k 0 1) := by
        intro hn
        apply hfin
        rw [←hq,Scheme.Hom.comp_apply]
        change q (sourcePoint k)∈chartInclusion k 0 ⁻¹ᵁ
          Proj.basicOpen (grading k) (coordinate k 1)
        rwa [chart_preimage_basicOpen]
      rw [←Spec.map_preimage q] at hn
      change ¬¬((Spec.preimage q).hom (ratio k 0 1)=0) at hn
      exact not_not.mp hn
    refine ⟨none,?_⟩
    change infinityPoint k k=p
    rw [infinityPoint_eq_chart]
    have hf : f=chartEvaluation 0 (MvPolynomial.aeval ![(1:k),0])
        (by simp [coordinate]) := by
      apply chartAlgHom_ext k 0
      intro j
      fin_cases j
      · simp [ratio_self]
      · simpa [coordinate] using hz
    rw [←hf]
    change Spec.map (Spec.preimage q)≫chartInclusion k 0=p
    rw [Spec.map_preimage,hq]


end
end AlgebraicGeometry.ProjectiveLine
