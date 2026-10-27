module

public import Z2Z4Rank6.ECProjectiveSchemeAffine
public import Z2Z4Rank6.ProjectiveBaseSchemeCharts

@[expose] public section

/-! Degree-zero localization chart and the printed affine Weierstrass
quotient. Source: Jaswal, DOI 10.5281/zenodo.23437117, Theorem 1.2(a), Lemma 4.1.
The inverse laws use the homogeneous-localization monomial spanning set.
-/
namespace Z2Z4Rank6.ECProjectiveSchemeCharts
noncomputable section
open scoped Classical BigOperators
open MvPolynomial AlgebraicGeometry CategoryTheory
open ECProjectiveScheme

abbrev ChartRing (k : Fin 3) := HomogeneousLocalization.Away grading (coordinate k)
abbrev LocalizedRing (k : Fin 3) := Localization.Away (coordinate k)

instance chartAlgebra (k : Fin 3) : Algebra ℚ (ChartRing k) :=
  ((HomogeneousLocalization.fromZeroRingHom grading (Submonoid.powers (coordinate k))).comp
    (algebraMap ℚ (grading 0))).toAlgebra

/-- Degree-zero ratio of two homogeneous coordinates. -/
def ratio (k i : Fin 3) : ChartRing k :=
  HomogeneousLocalization.Away.mk grading (coordinate_degree k) 1 (coordinate i)
    (by simpa using coordinate_degree i)

def inverseCoordinate (k : Fin 3) : LocalizedRing k :=
  IsLocalization.Away.invSelf (coordinate k)

theorem coordinate_mul_inverse (k : Fin 3) :
    algebraMap CoordinateRing (LocalizedRing k) (coordinate k)*inverseCoordinate k=1 :=
  IsLocalization.Away.mul_invSelf _

theorem ratio_val (k i : Fin 3) :
    (ratio k i).val=algebraMap CoordinateRing (LocalizedRing k) (coordinate i)*
      inverseCoordinate k := by
  simp only [ratio,HomogeneousLocalization.Away.val_mk]
  rw [Localization.mk_eq_mk',IsLocalization.mk'_eq_mul_mk'_one]
  simp only [pow_one,inverseCoordinate,IsLocalization.Away.invSelf]

theorem ratio_self (k : Fin 3) : ratio k k=1 := by
  apply HomogeneousLocalization.val_injective
  rw [ratio_val,HomogeneousLocalization.val_one,coordinate_mul_inverse]

/-- Degree-zero elements of this polynomial quotient are rational constants. -/
theorem degreeZero_eq_rat (r : grading 0) :
    ∃q : ℚ,r=algebraMap ℚ (grading 0) q := by
  obtain ⟨p,hp,he⟩ := r.property
  have hp0 : p.totalDegree=0 := (MvPolynomial.totalDegree_zero_iff_isHomogeneous (Fin 3)).mpr hp
  have hpC := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hp0
  refine ⟨p.coeff 0,Subtype.ext ?_⟩
  change (r:CoordinateRing)=algebraMap ℚ CoordinateRing (p.coeff 0)
  rw [←he,hpC]
  simp only [MvPolynomial.coeff_C]
  rfl

/-- A monomial of matching degree divided by a coordinate power is exactly
the corresponding product of degree-zero coordinate ratios. -/
theorem monomial_ratio (k : Fin 3) (a : ℕ) (ai : Fin 3 → ℕ)
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
theorem chartAlgHom_ext {S : Type*} [CommRing S] [Algebra ℚ S] (k : Fin 3)
    (f g : ChartRing k →ₐ[ℚ] S) (h : ∀i,f (ratio k i)=g (ratio k i)) : f=g := by
  have hspan := HomogeneousLocalization.Away.span_mk_prod_pow_eq_top
    (coordinate_degree k) coordinate coordinate_adjoin (fun _ : Fin 3 => (1:ℕ))
    (fun i => coordinate_degree i)
  apply AlgHom.ext
  intro x
  have hx : x∈Submodule.span (grading 0)
      {HomogeneousLocalization.Away.mk grading (coordinate_degree k) a
        (∏i,coordinate i^ai i) (hai ▸ SetLike.prod_pow_mem_graded _ _ _ _
          (fun i _ => coordinate_degree i)) |
        (a : ℕ) (ai : Fin 3 → ℕ) (hai : ∑i,ai i • (1:ℕ)=a • (1:ℕ))} := by
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

/-- Setting the homogeneous coordinate Z to 1. -/
def atZOne : CoordinateRing→ₐ[ℚ] ECProjectiveSchemeAffine.CoordinateRing :=
  Ideal.Quotient.liftₐ definingIdeal
    (MvPolynomial.aeval ![ECProjectiveSchemeAffine.x,ECProjectiveSchemeAffine.y,1]) (by
      have hker : definingIdeal≤RingHom.ker (MvPolynomial.aeval
          ![ECProjectiveSchemeAffine.x,ECProjectiveSchemeAffine.y,1]).toRingHom := by
        apply Ideal.span_le.mpr
        rintro p (rfl:p=relation)
        change (MvPolynomial.aeval _) relation=0
        norm_num [relation]
        norm_num only [map_ofNat]
        linear_combination ECProjectiveSchemeAffine.equation
      intro p hp
      exact hker hp)

@[simp] theorem atZOne_coordinate (i:Fin 3) :
    atZOne (coordinate i)=![ECProjectiveSchemeAffine.x,ECProjectiveSchemeAffine.y,1] i := by
  change (MvPolynomial.aeval _) (MvPolynomial.X i)=_
  simp

def chartToAffine : ChartRing 2→ₐ[ℚ] ECProjectiveSchemeAffine.CoordinateRing :=
  rationalAlgHom ((Localization.awayLift atZOne.toRingHom z (by simp [z])).comp
    (algebraMap (ChartRing 2) (LocalizedRing 2)))

@[simp] theorem chartToAffine_ratio (i:Fin 3) :
    chartToAffine (ratio 2 i)=![ECProjectiveSchemeAffine.x,ECProjectiveSchemeAffine.y,1] i := by
  change Localization.awayLift atZOne.toRingHom z (by simp [z]) (ratio 2 i).val=_
  rw [ratio_val,map_mul,IsLocalization.Away.lift_eq]
  have hi : Localization.awayLift atZOne.toRingHom z (by simp [z]) (inverseCoordinate 2)=1 := by
    have h := congrArg (Localization.awayLift atZOne.toRingHom z (by simp [z]))
      (coordinate_mul_inverse 2)
    simp only [map_mul,map_one,IsLocalization.Away.lift_eq] at h
    change atZOne (coordinate 2)*Localization.awayLift atZOne.toRingHom z _ (inverseCoordinate 2)=1 at h
    simpa [atZOne_coordinate] using h
  rw [hi,mul_one]
  exact atZOne_coordinate i

/-- The affine coordinates inserted as homogeneous ratios. -/
def affineToChart : ECProjectiveSchemeAffine.CoordinateRing→ₐ[ℚ]ChartRing 2 :=
  Ideal.Quotient.liftₐ ECProjectiveSchemeAffine.definingIdeal
    (MvPolynomial.aeval ![ratio 2 0,ratio 2 1]) (by
      have hker : ECProjectiveSchemeAffine.definingIdeal≤RingHom.ker
          (MvPolynomial.aeval ![ratio 2 0,ratio 2 1]).toRingHom := by
        apply Ideal.span_le.mpr
        rintro p ⟨i,rfl⟩
        change (MvPolynomial.aeval _) (ECProjectiveSchemeAffine.relation i)=0
        simp [ECProjectiveSchemeAffine.relation]
        apply HomogeneousLocalization.val_injective
        simp only [HomogeneousLocalization.val_add,HomogeneousLocalization.val_sub,
          HomogeneousLocalization.val_pow,HomogeneousLocalization.val_mul,
          HomogeneousLocalization.val_zero,ratio_val]
        norm_num only [←HomogeneousLocalization.algebraMap_apply,map_ofNat]
        have h := congrArg (algebraMap CoordinateRing (LocalizedRing 2)) cubic_equation
        simp only [map_add,map_sub,map_mul,map_pow,map_ofNat] at h
        have hz := coordinate_mul_inverse 2
        linear_combination inverseCoordinate 2^3*h-
          ((algebraMap CoordinateRing (LocalizedRing 2) y)^2*inverseCoordinate 2^2-
           (algebraMap CoordinateRing (LocalizedRing 2) x)^2*inverseCoordinate 2^2+
           137620*algebraMap CoordinateRing (LocalizedRing 2) x*inverseCoordinate 2*
             (1+algebraMap CoordinateRing (LocalizedRing 2) z*inverseCoordinate 2)+
           10504000*(1+algebraMap CoordinateRing (LocalizedRing 2) z*inverseCoordinate 2+
             (algebraMap CoordinateRing (LocalizedRing 2) z)^2*inverseCoordinate 2^2))*hz
      intro p hp
      exact hker hp)

@[simp] theorem affineToChart_x : affineToChart ECProjectiveSchemeAffine.x=ratio 2 0 := by
  change (MvPolynomial.aeval _) (MvPolynomial.X 0)=_
  simp
@[simp] theorem affineToChart_y : affineToChart ECProjectiveSchemeAffine.y=ratio 2 1 := by
  change (MvPolynomial.aeval _) (MvPolynomial.X 1)=_
  simp

theorem chartToAffine_comp_affineToChart :
    chartToAffine.comp affineToChart=AlgHom.id ℚ ECProjectiveSchemeAffine.CoordinateRing := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i
  · change chartToAffine (affineToChart ECProjectiveSchemeAffine.x)=ECProjectiveSchemeAffine.x
    rw [affineToChart_x,chartToAffine_ratio]
    rfl
  · change chartToAffine (affineToChart ECProjectiveSchemeAffine.y)=ECProjectiveSchemeAffine.y
    rw [affineToChart_y,chartToAffine_ratio]
    rfl

theorem affineToChart_comp_chartToAffine :
    affineToChart.comp chartToAffine=AlgHom.id ℚ (ChartRing 2) := by
  apply chartAlgHom_ext 2
  intro i
  fin_cases i <;> simp [ratio_self]

/-- Exact algebra isomorphism for the affine Z-chart. -/
def zChartRingEquiv : zChartRing≃ₐ[ℚ]ECProjectiveSchemeAffine.CoordinateRing :=
  {chartToAffine with
    invFun:=affineToChart
    left_inv:=fun q=>AlgHom.congr_fun affineToChart_comp_chartToAffine q
    right_inv:=fun q=>AlgHom.congr_fun chartToAffine_comp_affineToChart q}

def zChartSchemeIso : zOpen.toScheme≅ECProjectiveSchemeAffine.scheme :=
  zChartIso ≪≫ Scheme.Spec.mapIso zChartRingEquiv.toRingEquiv.toCommRingCatIso.symm.op

end
end Z2Z4Rank6.ECProjectiveSchemeCharts
