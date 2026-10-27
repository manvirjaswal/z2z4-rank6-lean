import Z2Z4Rank6.ProjectiveBaseScheme
import Z2Z4Rank6.AffineBaseScheme

/-!
# Dehomogenizing the projective base scheme

Jaswal, DOI 10.5281/zenodo.23437117, Section 3. The z-chart of the
homogeneous intersection is the affine coordinate ring of C.
The m-chart is its corresponding affine model at infinity.
-/
namespace Z2Z4Rank6.ProjectiveBaseSchemeCharts
noncomputable section
open scoped Classical BigOperators
open MvPolynomial AlgebraicGeometry CategoryTheory
open ProjectiveBaseScheme

abbrev ChartRing (k : Fin 4) := HomogeneousLocalization.Away grading (coordinate k)
abbrev LocalizedRing (k : Fin 4) := Localization.Away (coordinate k)

instance chartAlgebra (k : Fin 4) : Algebra ℚ (ChartRing k) :=
  ((HomogeneousLocalization.fromZeroRingHom grading (Submonoid.powers (coordinate k))).comp
    (algebraMap ℚ (grading 0))).toAlgebra

/-- Degree-zero ratio of two homogeneous coordinates. -/
def ratio (k i : Fin 4) : ChartRing k :=
  HomogeneousLocalization.Away.mk grading (coordinate_degree k) 1 (coordinate i)
    (by simpa using coordinate_degree i)

def inverseCoordinate (k : Fin 4) : LocalizedRing k :=
  IsLocalization.Away.invSelf (coordinate k)

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

/-- Degree-zero elements of this polynomial quotient are rational constants. -/
theorem degreeZero_eq_rat (r : grading 0) :
    ∃q : ℚ,r=algebraMap ℚ (grading 0) q := by
  obtain ⟨p,hp,he⟩ := r.property
  have hp0 : p.totalDegree=0 := (MvPolynomial.totalDegree_zero_iff_isHomogeneous (Fin 4)).mpr hp
  have hpC := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hp0
  refine ⟨p.coeff 0,Subtype.ext ?_⟩
  change (r:CoordinateRing)=algebraMap ℚ CoordinateRing (p.coeff 0)
  rw [←he,hpC]
  simp only [MvPolynomial.coeff_C]
  rfl

/-- A monomial of matching degree divided by a coordinate power is exactly
the corresponding product of degree-zero coordinate ratios. -/
theorem monomial_ratio (k : Fin 4) (a : ℕ) (ai : Fin 4 → ℕ)
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

/-- Coordinate ratios determine every rational-algebra map from a chart. -/
theorem chartAlgHom_ext {S : Type*} [CommRing S] [Algebra ℚ S] (k : Fin 4)
    (f g : ChartRing k →ₐ[ℚ] S) (h : ∀i,f (ratio k i)=g (ratio k i)) : f=g := by
  have hspan := HomogeneousLocalization.Away.span_mk_prod_pow_eq_top
    (coordinate_degree k) coordinate coordinate_adjoin (fun _ : Fin 4 => (1:ℕ))
    (fun i => coordinate_degree i)
  apply AlgHom.ext
  intro x
  have hx : x∈Submodule.span (grading 0)
      {HomogeneousLocalization.Away.mk grading (coordinate_degree k) a
        (∏i,coordinate i^ai i) (hai ▸ SetLike.prod_pow_mem_graded _ _ _ _
          (fun i _ => coordinate_degree i)) |
        (a : ℕ) (ai : Fin 4 → ℕ) (hai : ∑i,ai i • (1:ℕ)=a • (1:ℕ))} := by
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

/-- Rational algebra structure on a ring map is unique. -/
def rationalAlgHom {R S : Type*} [CommRing R] [CommRing S]
    [Algebra ℚ R] [Algebra ℚ S] (f : R →+* S) : R →ₐ[ℚ] S :=
  {toRingHom := f
   commutes' := by
    intro q
    exact RingHom.congr_fun
      (RingHom.ext_rat (f.comp (algebraMap ℚ R)) (algebraMap ℚ S)) q}

/-- The quotient map setting z=1. -/
def atZOne : CoordinateRing →ₐ[ℚ] AffineBaseScheme.CoordinateRing :=
  Ideal.Quotient.liftₐ definingIdeal
    (MvPolynomial.aeval ![AffineBaseScheme.m,AffineBaseScheme.u,AffineBaseScheme.v,1]) (by
      have hker : definingIdeal≤RingHom.ker
          (MvPolynomial.aeval ![AffineBaseScheme.m,AffineBaseScheme.u,AffineBaseScheme.v,1]).toRingHom := by
        apply Ideal.span_le.mpr
        rintro p ⟨i,rfl⟩
        change (MvPolynomial.aeval _) (relation i)=0
        fin_cases i
        · norm_num [ProjectiveBaseScheme.relation]
          norm_num only [map_ofNat]
          linear_combination AffineBaseScheme.u_sq
        · norm_num [ProjectiveBaseScheme.relation]
          norm_num only [map_ofNat]
          linear_combination AffineBaseScheme.v_sq
      intro p hp
      exact hker hp)

@[simp] theorem atZOne_coordinate (i : Fin 4) :
    atZOne (coordinate i)=![AffineBaseScheme.m,AffineBaseScheme.u,AffineBaseScheme.v,1] i := by
  change (MvPolynomial.aeval _) (MvPolynomial.X i)=_
  simp

def chartToAffine : ChartRing 3 →ₐ[ℚ] AffineBaseScheme.CoordinateRing :=
  rationalAlgHom ((Localization.awayLift atZOne.toRingHom z (by simp [z])).comp
    (algebraMap (ChartRing 3) (LocalizedRing 3)))

@[simp] theorem chartToAffine_ratio (i : Fin 4) :
    chartToAffine (ratio 3 i)=![AffineBaseScheme.m,AffineBaseScheme.u,AffineBaseScheme.v,1] i := by
  change Localization.awayLift atZOne.toRingHom z (by simp [z]) (ratio 3 i).val=_
  rw [ratio_val,map_mul]
  rw [IsLocalization.Away.lift_eq]
  change atZOne (coordinate i)*
    (Localization.awayLift atZOne.toRingHom z (by simp [z])) (inverseCoordinate 3)=_
  have hi : (Localization.awayLift atZOne.toRingHom z (by simp [z])) (inverseCoordinate 3)=1 := by
    have h := congrArg (Localization.awayLift atZOne.toRingHom z
      (by simp [z])) (coordinate_mul_inverse 3)
    simp only [map_mul,map_one,IsLocalization.Away.lift_eq] at h
    change atZOne (coordinate 3)*
      (Localization.awayLift atZOne.toRingHom z _) (inverseCoordinate 3)=1 at h
    simpa [atZOne_coordinate] using h
  rw [hi,mul_one,atZOne_coordinate]

/-- The affine generators interpreted as homogeneous ratios. -/
def affineToChart : AffineBaseScheme.CoordinateRing →ₐ[ℚ] ChartRing 3 :=
  Ideal.Quotient.liftₐ AffineBaseScheme.definingIdeal
    (MvPolynomial.aeval ![ratio 3 0,ratio 3 1,ratio 3 2]) (by
      have hker : AffineBaseScheme.definingIdeal≤RingHom.ker
          (MvPolynomial.aeval ![ratio 3 0,ratio 3 1,ratio 3 2]).toRingHom := by
        apply Ideal.span_le.mpr
        rintro p ⟨i,rfl⟩
        change (MvPolynomial.aeval _) (AffineBaseScheme.relation i)=0
        fin_cases i
        all_goals simp [AffineBaseScheme.relation]
        all_goals apply HomogeneousLocalization.val_injective
        all_goals simp only [HomogeneousLocalization.val_sub,HomogeneousLocalization.val_pow,
          HomogeneousLocalization.val_mul,
          HomogeneousLocalization.val_zero,ratio_val]
        all_goals norm_num only [←HomogeneousLocalization.algebraMap_apply,map_ofNat]
        · have h := congrArg (algebraMap CoordinateRing (LocalizedRing 3)) u_sq
          simp only [map_add,map_mul,map_pow,map_ofNat] at h
          have hz := congrArg (fun t : LocalizedRing 3 => t^2) (coordinate_mul_inverse 3)
          linear_combination inverseCoordinate 3^2*h+1210*hz
        · have h := congrArg (algebraMap CoordinateRing (LocalizedRing 3)) v_sq
          simp only [map_add,map_mul,map_pow,map_ofNat] at h
          have hz := congrArg (fun t : LocalizedRing 3 => t^2) (coordinate_mul_inverse 3)
          linear_combination inverseCoordinate 3^2*h+1215*hz
      intro p hp
      exact hker hp)

@[simp] theorem affineToChart_m : affineToChart AffineBaseScheme.m=ratio 3 0 := by
  change (MvPolynomial.aeval _) (MvPolynomial.X 0)=_
  simp
@[simp] theorem affineToChart_u : affineToChart AffineBaseScheme.u=ratio 3 1 := by
  change (MvPolynomial.aeval _) (MvPolynomial.X 1)=_
  simp
@[simp] theorem affineToChart_v : affineToChart AffineBaseScheme.v=ratio 3 2 := by
  change (MvPolynomial.aeval _) (MvPolynomial.X 2)=_
  simp

/-- Setting z=1 after inserting homogeneous ratios fixes every affine coordinate. -/
theorem chartToAffine_comp_affineToChart :
    chartToAffine.comp affineToChart=AlgHom.id ℚ AffineBaseScheme.CoordinateRing := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i
  · change chartToAffine (affineToChart AffineBaseScheme.m)=AffineBaseScheme.m
    rw [affineToChart_m,chartToAffine_ratio]
    rfl
  · change chartToAffine (affineToChart AffineBaseScheme.u)=AffineBaseScheme.u
    rw [affineToChart_u,chartToAffine_ratio]
    rfl
  · change chartToAffine (affineToChart AffineBaseScheme.v)=AffineBaseScheme.v
    rw [affineToChart_v,chartToAffine_ratio]
    rfl

/-- Homogeneous coordinate ratios are fixed by dehomogenization and reconstruction. -/
theorem affineToChart_comp_chartToAffine :
    affineToChart.comp chartToAffine=AlgHom.id ℚ (ChartRing 3) := by
  apply chartAlgHom_ext 3
  intro i
  fin_cases i
  all_goals simp [ratio_self]

/-- Exact algebra isomorphism between the z-chart and C's affine quotient. -/
def zChartRingEquiv : zChartRing ≃ₐ[ℚ] AffineBaseScheme.CoordinateRing :=
  {chartToAffine with
    invFun := affineToChart
    left_inv := fun x => AlgHom.congr_fun affineToChart_comp_chartToAffine x
    right_inv := fun x => AlgHom.congr_fun chartToAffine_comp_affineToChart x}

/-- The affine scheme of the displayed C equations is the z≠0 open. -/
def zChartSchemeIso : zOpen.toScheme ≅ AffineBaseScheme.scheme :=
  zChartIso ≪≫ Scheme.Spec.mapIso zChartRingEquiv.toRingEquiv.toCommRingCatIso.symm.op

end
end Z2Z4Rank6.ProjectiveBaseSchemeCharts
