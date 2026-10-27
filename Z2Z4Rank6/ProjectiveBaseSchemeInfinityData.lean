import Z2Z4Rank6.ProjectiveBaseScheme
import Mathlib.RingTheory.Extension.Presentation.Basic

/-!
# The affine equations on the m-chart of the projective base

Jaswal, DOI 10.5281/zenodo.23437117, Section 3. Setting m=1 in the
projective equations gives u²=1210z²+15, v²=1215z²+10.
-/
namespace Z2Z4Rank6.ProjectiveBaseSchemeCharts
noncomputable section
open scoped Classical
open AlgebraicGeometry CategoryTheory

abbrev InfinityPolynomialRing := MvPolynomial (Fin 3) ℚ

def infinityRelation : Fin 2 → InfinityPolynomialRing :=
  ![MvPolynomial.X 1^2-1210*MvPolynomial.X 0^2-15,
    MvPolynomial.X 2^2-1215*MvPolynomial.X 0^2-10]

def infinityIdeal : Ideal InfinityPolynomialRing := Ideal.span (Set.range infinityRelation)
abbrev InfinityCoordinateRing := InfinityPolynomialRing ⧸ infinityIdeal

def infinityZ : InfinityCoordinateRing := Ideal.Quotient.mk infinityIdeal (MvPolynomial.X 0)
def infinityU : InfinityCoordinateRing := Ideal.Quotient.mk infinityIdeal (MvPolynomial.X 1)
def infinityV : InfinityCoordinateRing := Ideal.Quotient.mk infinityIdeal (MvPolynomial.X 2)

def infinityPresentation : Algebra.Presentation ℚ InfinityCoordinateRing (Fin 3) (Fin 2) :=
  Algebra.Presentation.naive (v:=infinityRelation)

instance infinity_finitePresentation : Algebra.FinitePresentation ℚ InfinityCoordinateRing :=
  infinityPresentation.finitePresentation_of_isFinite

@[simp] theorem infinity_relation_zero (i : Fin 2) :
    Ideal.Quotient.mk infinityIdeal (infinityRelation i)=0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i,rfl⟩)

theorem infinity_u_sq : infinityU^2=1210*infinityZ^2+15 := by
  have h := infinity_relation_zero 0
  change Ideal.Quotient.mk infinityIdeal
    (MvPolynomial.X 1^2-1210*MvPolynomial.X 0^2-15)=0 at h
  simp only [map_sub,map_pow,map_mul,map_ofNat] at h
  change infinityU^2-1210*infinityZ^2-15=0 at h
  linear_combination h

theorem infinity_v_sq : infinityV^2=1215*infinityZ^2+10 := by
  have h := infinity_relation_zero 1
  change Ideal.Quotient.mk infinityIdeal
    (MvPolynomial.X 2^2-1215*MvPolynomial.X 0^2-10)=0 at h
  simp only [map_sub,map_pow,map_mul,map_ofNat] at h
  change infinityV^2-1215*infinityZ^2-10=0 at h
  linear_combination h

def infinityScheme : Scheme := Spec (CommRingCat.of InfinityCoordinateRing)
def infinityStructureMap : infinityScheme ⟶ Spec (CommRingCat.of ℚ) :=
  Spec.map (CommRingCat.ofHom (algebraMap ℚ InfinityCoordinateRing))

def infinityMinorFactor (i : Fin 3) : InfinityCoordinateRing :=
  ![infinityU*infinityV,infinityZ*infinityV,infinityZ*infinityU] i

/-- The three Jacobian-minor factors generate the unit ideal. -/
theorem infinityMinorFactors_span_top : Ideal.span (Set.range infinityMinorFactor)=⊤ := by
  let J : Ideal InfinityCoordinateRing := Ideal.span (Set.range infinityMinorFactor)
  have huv : infinityU*infinityV∈J := Ideal.subset_span ⟨0,rfl⟩
  have hzv : infinityZ*infinityV∈J := Ideal.subset_span ⟨1,rfl⟩
  have hzu : infinityZ*infinityU∈J := Ideal.subset_span ⟨2,rfl⟩
  have hline : 1210*((infinityZ*infinityV)*(infinityZ*infinityV))-
      1215*((infinityZ*infinityU)*(infinityZ*infinityU))∈J :=
    J.sub_mem (J.mul_mem_left 1210 (J.mul_mem_left (infinityZ*infinityV) hzv))
      (J.mul_mem_left 1215 (J.mul_mem_left (infinityZ*infinityU) hzu))
  have he : 1210*((infinityZ*infinityV)*(infinityZ*infinityV))-
      1215*((infinityZ*infinityU)*(infinityZ*infinityU))= -6125*infinityZ^2 := by
    calc
      _=infinityZ^2*(1210*infinityV^2-1215*infinityU^2) := by ring
      _=_ := by rw [infinity_u_sq,infinity_v_sq]; ring
  rw [he] at hline
  have hunit : IsUnit (-6125 : InfinityCoordinateRing) := by
    simpa only [map_neg,map_ofNat] using
      (show IsUnit (-6125:ℚ) by norm_num).map (algebraMap ℚ InfinityCoordinateRing)
  obtain ⟨a,ha⟩ := hunit
  have hz2 : infinityZ^2∈J := by
    have h := J.mul_mem_left (↑a⁻¹) hline
    rw [←ha,←mul_assoc,Units.inv_mul,one_mul] at h
    exact h
  have huv2 : infinityU^2*infinityV^2∈J := by
    convert J.mul_mem_left (infinityU*infinityV) huv using 1
    ring
  have hconst : (150 : InfinityCoordinateRing)∈J := by
    have h := J.sub_mem huv2 (J.mul_mem_left (1470150*infinityZ^2+30325) hz2)
    convert h using 1
    rw [infinity_u_sq,infinity_v_sq]
    ring
  apply J.eq_top_of_isUnit_mem hconst
  simpa only [map_ofNat] using (show IsUnit (150:ℚ) by norm_num).map
    (algebraMap ℚ InfinityCoordinateRing)

end
end Z2Z4Rank6.ProjectiveBaseSchemeCharts
