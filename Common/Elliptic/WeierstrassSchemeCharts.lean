module

public import Common.Elliptic.WeierstrassSchemePoints
public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization

@[expose] public section

/-!
# Coordinate charts of an arbitrary rational Weierstrass cubic

Homogeneous localization rings and coordinate ratios. The two charts
Y != 0 and Z != 0 cover the entire cubic. All assertions are elementary
quotient/localization arguments.
-/
namespace WeierstrassScheme.Charts
noncomputable section
open scoped Classical BigOperators
open MvPolynomial AlgebraicGeometry CategoryTheory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
variable (W : WeierstrassCurve ℚ)

abbrev ChartRing (k : Fin 3) := HomogeneousLocalization.Away (grading W) (coordinate W k)
abbrev LocalizedRing (k : Fin 3) := Localization.Away (coordinate W k)

instance chartAlgebra (k : Fin 3) : Algebra ℚ (ChartRing W k) :=
  ((HomogeneousLocalization.fromZeroRingHom (grading W) (Submonoid.powers (coordinate W k))).comp
    (algebraMap ℚ (grading W 0))).toAlgebra

def ratio (k i : Fin 3) : ChartRing W k :=
  HomogeneousLocalization.Away.mk (grading W) (coordinate_degree W k) 1 (coordinate W i)
    (by simpa using coordinate_degree W i)

def inverseCoordinate (k : Fin 3) : LocalizedRing W k :=
  IsLocalization.Away.invSelf (coordinate W k)

theorem coordinate_mul_inverse (k : Fin 3) :
    algebraMap (CoordinateRing W) (LocalizedRing W k) (coordinate W k)*inverseCoordinate W k=1 :=
  IsLocalization.Away.mul_invSelf _

theorem ratio_val (k i : Fin 3) :
    (ratio W k i).val=algebraMap (CoordinateRing W) (LocalizedRing W k) (coordinate W i)*
      inverseCoordinate W k := by
  simp only [ratio,HomogeneousLocalization.Away.val_mk]
  rw [Localization.mk_eq_mk',IsLocalization.mk'_eq_mul_mk'_one]
  simp only [pow_one,inverseCoordinate,IsLocalization.Away.invSelf]

theorem ratio_self (k : Fin 3) : ratio W k k=1 := by
  apply HomogeneousLocalization.val_injective
  rw [ratio_val,HomogeneousLocalization.val_one,coordinate_mul_inverse]

theorem coordinate_adjoin : Algebra.adjoin (grading W 0) (Set.range (coordinate W))=⊤ := by
  have hpoly : ∀p : PolynomialRing ℚ, Ideal.Quotient.mk (definingIdeal W) p∈
      Algebra.adjoin (grading W 0) (Set.range (coordinate W)) := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C r =>
      have h0 : Ideal.Quotient.mk (definingIdeal W) (C r)∈grading W 0 :=
        ⟨C r,isHomogeneous_C (Fin 3) r,rfl⟩
      exact (Algebra.adjoin (grading W 0) (Set.range (coordinate W))).algebraMap_mem
        ⟨Ideal.Quotient.mk (definingIdeal W) (C r),h0⟩
    | add p q hp hq => simpa only [map_add] using add_mem hp hq
    | mul_X p i hp =>
      simpa only [map_mul,coordinate] using mul_mem hp
        (Algebra.subset_adjoin (show coordinate W i∈Set.range (coordinate W) from ⟨i,rfl⟩))
  apply top_unique
  intro q _
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective q
  exact hpoly p

theorem monomial_ratio (k : Fin 3) (a : ℕ) (ai : Fin 3 → ℕ)
    (hai : ∑i,ai i=a) (ha : (∏i,coordinate W i^ai i)∈grading W (a • (1:ℕ))) :
    HomogeneousLocalization.Away.mk (grading W) (coordinate_degree W k) a
      (∏i,coordinate W i^ai i) ha=∏i,ratio W k i^ai i := by
  apply HomogeneousLocalization.val_injective
  calc
    _=algebraMap (CoordinateRing W) (LocalizedRing W k) (∏i,coordinate W i^ai i)*
        inverseCoordinate W k^a := by
      rw [HomogeneousLocalization.Away.val_mk,Localization.mk_eq_mk',
        IsLocalization.mk'_eq_mul_mk'_one]
      congr 1
      simp only [inverseCoordinate,IsLocalization.Away.invSelf,←IsLocalization.mk'_pow,one_pow]
      rfl
    _=_ := by
      change _=algebraMap (ChartRing W k) (LocalizedRing W k) (∏i,ratio W k i^ai i)
      rw [map_prod,map_prod]
      simp only [map_pow,HomogeneousLocalization.algebraMap_apply,ratio_val,mul_pow]
      rw [Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum,hai]

theorem chartAlgHom_ext {S : Type*} [CommRing S] [Algebra ℚ S] (k : Fin 3)
    (f g : ChartRing W k →ₐ[ℚ] S) (h : ∀i,f (ratio W k i)=g (ratio W k i)) : f=g := by
  have hspan := HomogeneousLocalization.Away.span_mk_prod_pow_eq_top
    (coordinate_degree W k) (coordinate W) (coordinate_adjoin W) (fun _ : Fin 3 => (1:ℕ))
    (fun i => coordinate_degree W i)
  apply AlgHom.ext
  intro x
  have hx : x∈Submodule.span (grading W 0)
      {HomogeneousLocalization.Away.mk (grading W) (coordinate_degree W k) a
        (∏i,coordinate W i^ai i) (hai ▸ SetLike.prod_pow_mem_graded _ _ _ _
          (fun i _ => coordinate_degree W i)) |
        (a : ℕ) (ai : Fin 3 → ℕ) (hai : ∑i,ai i • (1:ℕ)=a • (1:ℕ))} := by
    rw [hspan]
    trivial
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a,ai,hai,rfl⟩ := hy
    rw [monomial_ratio W k a ai (by simpa using hai)]
    simp only [map_prod,map_pow,h]
  | zero => simp
  | add x y hx hy hfx hfy => simp only [map_add,hfx,hfy]
  | smul r x hx hfx =>
    obtain ⟨q,rfl⟩ := degreeZero_eq_coefficient W r
    change f (algebraMap ℚ (ChartRing W k) q*x)=g (algebraMap ℚ (ChartRing W k) q*x)
    simp only [map_mul,AlgHom.commutes,hfx]

def rationalAlgHom {R S : Type*} [CommRing R] [CommRing S]
    [Algebra ℚ R] [Algebra ℚ S] (f : R →+* S) : R →ₐ[ℚ] S :=
  {toRingHom := f
   commutes' := by
    intro q
    exact RingHom.congr_fun
      (RingHom.ext_rat (f.comp (algebraMap ℚ R)) (algebraMap ℚ S)) q}

theorem cubic_relation :
    coordinate W 1^2*coordinate W 2+
      algebraMap ℚ (CoordinateRing W) W.a₁*(coordinate W 0*coordinate W 1*coordinate W 2)+
      algebraMap ℚ (CoordinateRing W) W.a₃*(coordinate W 1*coordinate W 2^2)-
      coordinate W 0^3-algebraMap ℚ (CoordinateRing W) W.a₂*(coordinate W 0^2*coordinate W 2)-
      algebraMap ℚ (CoordinateRing W) W.a₄*(coordinate W 0*coordinate W 2^2)-
      algebraMap ℚ (CoordinateRing W) W.a₆*coordinate W 2^3=0 := by
  have h : Ideal.Quotient.mk (definingIdeal W) (relation W)=0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  have hc (q : ℚ) : Ideal.Quotient.mk (definingIdeal W) (C q)=
      algebraMap ℚ (CoordinateRing W) q :=
    (Ideal.Quotient.mkₐ ℚ (definingIdeal W)).commutes q
  simpa only [relation,map_sub,map_add,map_pow,map_mul,coordinate,hc] using h

theorem ratio_relation (k : Fin 3) :
    ratio W k 1^2*ratio W k 2+
      algebraMap ℚ (ChartRing W k) W.a₁*(ratio W k 0*ratio W k 1*ratio W k 2)+
      algebraMap ℚ (ChartRing W k) W.a₃*(ratio W k 1*ratio W k 2^2)-
      ratio W k 0^3-algebraMap ℚ (ChartRing W k) W.a₂*(ratio W k 0^2*ratio W k 2)-
      algebraMap ℚ (ChartRing W k) W.a₄*(ratio W k 0*ratio W k 2^2)-
      algebraMap ℚ (ChartRing W k) W.a₆*ratio W k 2^3=0 := by
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.val_add,HomogeneousLocalization.val_sub,
    HomogeneousLocalization.val_pow,HomogeneousLocalization.val_mul,
    HomogeneousLocalization.val_zero,ratio_val]
  norm_num only [←HomogeneousLocalization.algebraMap_apply]
  have hc (q : ℚ) :
      algebraMap (ChartRing W k) (LocalizedRing W k) (algebraMap ℚ (ChartRing W k) q)=
      algebraMap (CoordinateRing W) (LocalizedRing W k) (algebraMap ℚ (CoordinateRing W) q) :=
    RingHom.congr_fun (RingHom.ext_rat
      ((algebraMap (ChartRing W k) (LocalizedRing W k)).comp (algebraMap ℚ (ChartRing W k)))
      ((algebraMap (CoordinateRing W) (LocalizedRing W k)).comp
        (algebraMap ℚ (CoordinateRing W)))) q
  simp only [hc]
  have h := congrArg (algebraMap (CoordinateRing W) (LocalizedRing W k)) (cubic_relation W)
  simp only [map_sub,map_add,map_pow,map_mul,map_zero] at h
  linear_combination inverseCoordinate W k^3*h

def chartInclusion (k : Fin 3) : Spec (CommRingCat.of (ChartRing W k)) ⟶ scheme W :=
  Proj.awayι (grading W) (coordinate W k) (coordinate_degree W k) (by decide : 0<1)

instance chartInclusion_openImmersion (k : Fin 3) : IsOpenImmersion (chartInclusion W k) := by
  dsimp only [chartInclusion]
  infer_instance

def zOpen : (scheme W).Opens := Proj.basicOpen (grading W) (coordinate W 2)
def yOpen : (scheme W).Opens := Proj.basicOpen (grading W) (coordinate W 1)

theorem coordinate_opens_cover :
    ⨆ i : Fin 3, Proj.basicOpen (grading W) (coordinate W i)=⊤ :=
  Proj.iSup_basicOpen_eq_top' (grading W) (coordinate W)
    (fun i=>⟨1,coordinate_degree W i⟩) (coordinate_adjoin W)

theorem two_chart_cover : zOpen W⊔yOpen W=⊤ := by
  apply top_unique
  intro p _
  change coordinate W 2∉p.asHomogeneousIdeal ∨ coordinate W 1∉p.asHomogeneousIdeal
  by_contra h
  push Not at h
  let : p.asHomogeneousIdeal.toIdeal.IsPrime := p.isPrime
  have hz := Ideal.Quotient.eq_zero_iff_mem.mpr h.1
  have he := congrArg (Ideal.Quotient.mk p.asHomogeneousIdeal.toIdeal) (cubic_relation W)
  simp only [map_add,map_sub,map_mul,map_pow,map_zero,hz,mul_zero,zero_pow (by decide : 2≠0),
    zero_pow (by decide : 3≠0),add_zero,sub_zero] at he
  have hx : coordinate W 0∈p.asHomogeneousIdeal := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply (pow_eq_zero_iff (by decide : 3≠0)).mp
    linear_combination -he
  have hall : ∀ i : Fin 3, coordinate W i∈p.asHomogeneousIdeal := by
    intro i
    fin_cases i
    · exact hx
    · exact h.2
    · exact h.1
  have hp : p∈⨆ i : Fin 3, Proj.basicOpen (grading W) (coordinate W i) := by
    rw [coordinate_opens_cover]
    trivial
  obtain ⟨i,hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hp
  exact hi (hall i)

theorem chartInclusion_opensRange (k : Fin 3) :
    (chartInclusion W k).opensRange=Proj.basicOpen (grading W) (coordinate W k) :=
  Proj.opensRange_awayι _ _ _ _

theorem chartInclusion_structureMap (k : Fin 3) :
    chartInclusion W k ≫ structureMap W=
      Spec.map (CommRingCat.ofHom (algebraMap ℚ (ChartRing W k))) := by
  dsimp only [chartInclusion,structureMap,scheme]
  rw [←Category.assoc,Proj.awayι_toSpecZero,←Spec.map_comp]
  rfl

end
end WeierstrassScheme.Charts
