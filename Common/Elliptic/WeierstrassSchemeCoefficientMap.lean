import Common.Elliptic.WeierstrassSchemeGenericCharts
import Common.AlgebraicGeometry.ProjGradedChartMap
import Mathlib.RingTheory.MvPolynomial.Ideal

/-! Coefficient maps of the complete homogeneous Weierstrass cubic. -/
namespace WeierstrassScheme.CoefficientMap
noncomputable section
open MvPolynomial AlgebraicGeometry CategoryTheory HomogeneousIdeal
set_option backward.isDefEq.respectTransparency false
variable {k K : Type} [Field k] [Field K] (f : k →+* K)
variable (W : WeierstrassCurve k)

@[simp] theorem relation_map : MvPolynomial.map f (relation W)=relation (W.map f) := by
  simp [relation]

def quotientHom : CoordinateRing W →+* CoordinateRing (W.map f) :=
  Ideal.Quotient.lift (definingIdeal W)
    ((Ideal.Quotient.mk (definingIdeal (W.map f))).comp (MvPolynomial.map f)) (by
      have hker : definingIdeal W ≤ RingHom.ker
          ((Ideal.Quotient.mk (definingIdeal (W.map f))).comp (MvPolynomial.map f)) := by
        apply Ideal.span_le.mpr
        rintro p (rfl : p=relation W)
        change Ideal.Quotient.mk _ (MvPolynomial.map f (relation W))=0
        rw [relation_map]
        exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
      intro p hp
      exact hker hp)

@[simp] theorem quotientHom_mk (p : PolynomialRing k) :
    quotientHom f W (Ideal.Quotient.mk (definingIdeal W) p)=
      Ideal.Quotient.mk (definingIdeal (W.map f)) (MvPolynomial.map f p) := rfl

def gradedHom : grading W →+*ᵍ grading (W.map f) where
  toRingHom := quotientHom f W
  map_mem := by
    intro n p hp
    obtain ⟨q,hq,rfl⟩ := hp
    exact ⟨MvPolynomial.map f q,MvPolynomial.IsHomogeneous.map hq f,rfl⟩

@[simp] theorem gradedHom_coordinate (i : Fin 3) :
    gradedHom f W (coordinate W i)=coordinate (W.map f) i := by
  change quotientHom f W (Ideal.Quotient.mk _ (X i))=_
  simp [coordinate]

@[simp] theorem gradedHom_scalar (a : k) :
    gradedHom f W (algebraMap k (CoordinateRing W) a)=
      algebraMap K (CoordinateRing (W.map f)) (f a) := by
  change quotientHom f W (Ideal.Quotient.mk _ (C a))=_
  simp only [quotientHom_mk,MvPolynomial.map_C]
  rfl

theorem irrelevant_le : irrelevant (grading (W.map f)) ≤
    (irrelevant (grading W)).map (gradedHom f W) := by
  apply (HomogeneousIdeal.irrelevant_le (grading (W.map f))).mpr
  intro n hn p hp
  obtain ⟨q,hq,rfl⟩ := hp
  have hq0 : q.coeff 0=0 := hq.coeff_eq_zero (by simpa using hn.ne)
  have hspan : q∈Ideal.span (Set.range (X : Fin 3 → PolynomialRing K)) := by
    rw [←Set.image_univ,MvPolynomial.mem_ideal_span_X_image]
    intro m hm
    have hm0 : m≠0 := by
      intro h
      subst m
      simp [MvPolynomial.mem_support_iff,hq0] at hm
    obtain ⟨i,hi⟩ : ∃ i,m i≠0 := by
      by_contra! h
      apply hm0
      ext i
      exact h i
    exact ⟨i,Set.mem_univ i,hi⟩
  have he : Ideal.span (Set.range (X : Fin 3 → PolynomialRing K)) ≤
      Ideal.comap (Ideal.Quotient.mk (definingIdeal (W.map f)))
        ((irrelevant (grading W)).map (gradedHom f W)).toIdeal := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    have h := Ideal.mem_map_of_mem (gradedHom f W)
      (mem_irrelevant_of_mem (grading W) (by decide : 0<1) (coordinate_degree W i))
    change coordinate (W.map f) i∈((irrelevant (grading W)).map (gradedHom f W)).toIdeal
    simpa only [HomogeneousIdeal.toIdeal_map,gradedHom_coordinate] using h
  exact he hspan

def schemeHom : scheme (W.map f) ⟶ scheme W := Proj.map (gradedHom f W) (irrelevant_le f W)

theorem schemeHom_over : schemeHom f W≫structureMap W=
    structureMap (W.map f)≫Spec.map (CommRingCat.ofHom f) := by
  dsimp only [schemeHom,structureMap]
  rw [←Category.assoc,Proj.map_toSpecZero,Category.assoc,←Spec.map_comp,Category.assoc,
    ←Spec.map_comp]
  congr 2
  apply CommRingCat.hom_ext
  ext a
  exact gradedHom_scalar f W a

end
end WeierstrassScheme.CoefficientMap
