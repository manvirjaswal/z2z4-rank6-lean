module

public import Z2Z4Rank6.SecondBaseProjectiveScheme

@[expose] public section

/-! Coordinate opens and homogeneous ratios of the projective G2
intersection. The two degree-one opens M≠0 and Z≠0 cover its Proj. -/

namespace Z2Z4Rank6.SecondBaseProjectiveCharts
noncomputable section
open MvPolynomial AlgebraicGeometry CategoryTheory
open SecondBaseProjectiveScheme
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false

def zOpen : scheme.Opens := Proj.basicOpen grading z
def mOpen : scheme.Opens := Proj.basicOpen grading m

theorem coordinate_adjoin : Algebra.adjoin (grading 0) (Set.range coordinate)=⊤ := by
  have hpoly : ∀p : PolynomialRing,Ideal.Quotient.mk definingIdeal p∈
      Algebra.adjoin (grading 0) (Set.range coordinate) := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C r =>
      have h0 : Ideal.Quotient.mk definingIdeal (MvPolynomial.C r)∈grading 0 :=
        ⟨MvPolynomial.C r,isHomogeneous_C (Fin 4) r,rfl⟩
      exact (Algebra.adjoin (grading 0) (Set.range coordinate)).algebraMap_mem
        ⟨Ideal.Quotient.mk definingIdeal (MvPolynomial.C r),h0⟩
    | add p q hp hq => simpa only [map_add] using add_mem hp hq
    | mul_X p i hp =>
      simpa only [map_mul,coordinate] using mul_mem hp
        (Algebra.subset_adjoin (show coordinate i∈Set.range coordinate from ⟨i,rfl⟩))
  apply top_unique
  intro x _
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective x
  exact hpoly p

theorem coordinate_opens_cover : ⨆i : Fin 4,Proj.basicOpen grading (coordinate i)=⊤ :=
  Proj.iSup_basicOpen_eq_top' grading coordinate (fun i=>⟨1,coordinate_degree i⟩)
    coordinate_adjoin

theorem two_chart_cover : zOpen⊔mOpen=⊤ := by
  apply top_unique
  intro x _
  change z∉x.asHomogeneousIdeal ∨ m∉x.asHomogeneousIdeal
  by_contra h
  push Not at h
  have hz : z∈x.asHomogeneousIdeal.toIdeal := h.1
  have hm : m∈x.asHomogeneousIdeal.toIdeal := h.2
  have hu : u∈x.asHomogeneousIdeal.toIdeal := by
    apply x.isPrime.mem_of_pow_mem 2
    rw [u_sq]
    exact Ideal.sub_mem _
      (Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ hm 2 (by decide)))
      (Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ hz 2 (by decide)))
  have hv : v∈x.asHomogeneousIdeal.toIdeal := by
    apply x.isPrime.mem_of_pow_mem 2
    rw [v_sq]
    exact Ideal.add_mem _
      (Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ hm 2 (by decide)))
      (Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ hz 2 (by decide)))
  have hall : ∀i : Fin 4,coordinate i∈x.asHomogeneousIdeal := by
    intro i
    fin_cases i
    · exact hm
    · exact hu
    · exact hv
    · exact hz
  have hx : x∈⨆i : Fin 4,Proj.basicOpen grading (coordinate i) := by
    rw [coordinate_opens_cover]
    trivial
  obtain ⟨i,hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  exact hi (hall i)

abbrev ChartRing (k : Fin 4) := HomogeneousLocalization.Away grading (coordinate k)
abbrev LocalizedRing (k : Fin 4) := Localization.Away (coordinate k)

instance chartAlgebra (k : Fin 4) : Algebra ℚ (ChartRing k) :=
  ((HomogeneousLocalization.fromZeroRingHom grading (Submonoid.powers (coordinate k))).comp
    (algebraMap ℚ (grading 0))).toAlgebra

def ratio (k i : Fin 4) : ChartRing k :=
  HomogeneousLocalization.Away.mk grading (coordinate_degree k) 1 (coordinate i)
    (by simpa using coordinate_degree i)

def inverseCoordinate (k : Fin 4) : LocalizedRing k := IsLocalization.Away.invSelf (coordinate k)

theorem coordinate_mul_inverse (k : Fin 4) :
    algebraMap CoordinateRing (LocalizedRing k) (coordinate k)*inverseCoordinate k=1 :=
  IsLocalization.Away.mul_invSelf _

theorem ratio_val (k i : Fin 4) :
    (ratio k i).val=algebraMap CoordinateRing (LocalizedRing k) (coordinate i)*
      inverseCoordinate k := by
  simp only [ratio,HomogeneousLocalization.Away.val_mk]
  rw [Localization.mk_eq_mk',IsLocalization.mk'_eq_mul_mk'_one]
  simp only [pow_one,inverseCoordinate,IsLocalization.Away.invSelf]

theorem ratio_self (k : Fin 4) : ratio k k=1 := by
  apply HomogeneousLocalization.val_injective
  rw [ratio_val,HomogeneousLocalization.val_one,coordinate_mul_inverse]

theorem ratio_u_sq (k : Fin 4) :
    (ratio k 1)^2=34391709*(ratio k 0)^2-751709*(ratio k 3)^2 := by
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.val_pow,HomogeneousLocalization.val_sub,
    HomogeneousLocalization.val_mul,ratio_val]
  norm_num only [←HomogeneousLocalization.algebraMap_apply,map_ofNat]
  have h := congrArg (algebraMap CoordinateRing (LocalizedRing k)) u_sq
  simp only [map_sub,map_mul,map_pow,map_ofNat] at h
  linear_combination inverseCoordinate k^2*h

theorem ratio_v_sq (k : Fin 4) :
    (ratio k 2)^2= -751709*(ratio k 0)^2+3779309*(ratio k 3)^2 := by
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.val_pow,HomogeneousLocalization.val_add,
    HomogeneousLocalization.val_mul,HomogeneousLocalization.val_neg,ratio_val]
  norm_num only [←HomogeneousLocalization.algebraMap_apply,map_ofNat,map_neg]
  have h := congrArg (algebraMap CoordinateRing (LocalizedRing k)) v_sq
  simp only [map_add,map_neg,map_mul,map_pow,map_ofNat] at h
  linear_combination inverseCoordinate k^2*h

theorem degreeZero_eq_rat (r : grading 0) : ∃q : ℚ,r=algebraMap ℚ (grading 0) q := by
  obtain ⟨p,hp,he⟩ := r.property
  have hp0 : p.totalDegree=0 := (MvPolynomial.totalDegree_zero_iff_isHomogeneous (Fin 4)).mpr hp
  have hpC := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hp0
  refine ⟨p.coeff 0,Subtype.ext ?_⟩
  change (r:CoordinateRing)=algebraMap ℚ CoordinateRing (p.coeff 0)
  rw [←he,hpC]
  simp only [MvPolynomial.coeff_C]
  rfl

theorem monomial_ratio (k : Fin 4) (a : ℕ) (ai : Fin 4→ℕ)
    (hai : ∑i,ai i=a) (ha : (∏i,coordinate i^ai i)∈grading (a • (1:ℕ))) :
    HomogeneousLocalization.Away.mk grading (coordinate_degree k) a
      (∏i,coordinate i^ai i) ha=∏i,ratio k i^ai i := by
  apply HomogeneousLocalization.val_injective
  calc
    _=algebraMap CoordinateRing (LocalizedRing k) (∏i,coordinate i^ai i)*
        inverseCoordinate k^a := by
      rw [HomogeneousLocalization.Away.val_mk,Localization.mk_eq_mk',
        IsLocalization.mk'_eq_mul_mk'_one]
      congr 1
      simp only [inverseCoordinate,IsLocalization.Away.invSelf,←IsLocalization.mk'_pow,one_pow]
      rfl
    _=_ := by
      change _=algebraMap (ChartRing k) (LocalizedRing k) (∏i,ratio k i^ai i)
      rw [map_prod,map_prod]
      simp only [map_pow,HomogeneousLocalization.algebraMap_apply,ratio_val,mul_pow]
      rw [Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum,hai]

def rationalAlgHom {R S : Type*} [CommRing R] [CommRing S]
    [Algebra ℚ R] [Algebra ℚ S] (f : R→+*S) : R→ₐ[ℚ]S :=
  {toRingHom := f
   commutes' := fun q=>RingHom.congr_fun
      (RingHom.ext_rat (f.comp (algebraMap ℚ R)) (algebraMap ℚ S)) q}

theorem chartAlgHom_ext {S : Type*} [CommRing S] [Algebra ℚ S] (k : Fin 4)
    (f g : ChartRing k→ₐ[ℚ]S) (h : ∀i,f (ratio k i)=g (ratio k i)) : f=g := by
  have hspan := HomogeneousLocalization.Away.span_mk_prod_pow_eq_top
    (coordinate_degree k) coordinate coordinate_adjoin (fun _ : Fin 4=>(1:ℕ))
    (fun i=>coordinate_degree i)
  apply AlgHom.ext
  intro x
  have hx : x∈Submodule.span (grading 0)
      {HomogeneousLocalization.Away.mk grading (coordinate_degree k) a
        (∏i,coordinate i^ai i) (hai ▸ SetLike.prod_pow_mem_graded _ _ _ _
          (fun i _=>coordinate_degree i)) |
        (a : ℕ) (ai : Fin 4→ℕ) (hai : ∑i,ai i • (1:ℕ)=a • (1:ℕ))} := by
    rw [hspan]
    trivial
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a,ai,hai,rfl⟩ := hy
    rw [monomial_ratio k a ai (by simpa using hai)]
    simp only [map_prod,map_pow,h]
  | zero => simp
  | add x y hx hy hfx hfy => simp only [map_add,hfx,hfy]
  | smul r x hx hfx =>
    obtain ⟨q,rfl⟩ := degreeZero_eq_rat r
    change f (algebraMap ℚ (ChartRing k) q*x)=g (algebraMap ℚ (ChartRing k) q*x)
    simp only [map_mul,AlgHom.commutes,hfx]

theorem chartRingHom_ext {S : Type*} [CommRing S] [Algebra ℚ S] (k : Fin 4)
    (f g : ChartRing k→+*S) (h : ∀i,f (ratio k i)=g (ratio k i)) : f=g :=
  congrArg AlgHom.toRingHom (chartAlgHom_ext k (rationalAlgHom f) (rationalAlgHom g) h)

def chartInclusion (k : Fin 4) : Spec (CommRingCat.of (ChartRing k))⟶scheme :=
  Proj.awayι grading (coordinate k) (coordinate_degree k) (by decide : 0<1)

instance chartInclusion_openImmersion (k : Fin 4) : IsOpenImmersion (chartInclusion k) := by
  dsimp only [chartInclusion]
  infer_instance

end
end Z2Z4Rank6.SecondBaseProjectiveCharts
