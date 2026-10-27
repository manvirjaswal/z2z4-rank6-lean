module

public import Z2Z4Rank6.ProjectiveBaseSchemeGrading
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.Tactic

@[expose] public section

/-!
# The projective base scheme

Jaswal, DOI 10.5281/zenodo.23437117, Section 3: the projective closure
of C is the intersection u²=15m²+1210z², v²=10m²+1215z² in P³.
Here it is the Mathlib scheme Proj of the homogeneous coordinate
ring.
-/
namespace Z2Z4Rank6.ProjectiveBaseScheme
noncomputable section
open scoped Classical
open MvPolynomial AlgebraicGeometry CategoryTheory

abbrev PolynomialRing := MvPolynomial (Fin 4) ℚ

def polynomialGrading : ℕ → Submodule ℚ PolynomialRing :=
  MvPolynomial.homogeneousSubmodule (Fin 4) ℚ

instance polynomialGradedAlgebra : GradedAlgebra polynomialGrading :=
  MvPolynomial.gradedAlgebra

/-- Coordinates are indexed (m,u,v,z). -/
def relation : Fin 2 → PolynomialRing :=
  ![X 1^2-C 15*X 0^2-C 1210*X 3^2,
    X 2^2-C 10*X 0^2-C 1215*X 3^2]

def definingIdeal : Ideal PolynomialRing := Ideal.span (Set.range relation)

theorem relation_homogeneous (i : Fin 2) : (relation i).IsHomogeneous 2 := by
  fin_cases i
  · exact (((isHomogeneous_X ℚ (1:Fin 4)).pow 2).sub
      (((isHomogeneous_X ℚ (0:Fin 4)).pow 2).C_mul 15)).sub
      (((isHomogeneous_X ℚ (3:Fin 4)).pow 2).C_mul 1210)
  · exact (((isHomogeneous_X ℚ (2:Fin 4)).pow 2).sub
      (((isHomogeneous_X ℚ (0:Fin 4)).pow 2).C_mul 10)).sub
      (((isHomogeneous_X ℚ (3:Fin 4)).pow 2).C_mul 1215)

theorem definingIdeal_homogeneous : definingIdeal.IsHomogeneous polynomialGrading :=
  Ideal.homogeneous_span polynomialGrading _ (by
    rintro _ ⟨i,rfl⟩
    exact ⟨2,relation_homogeneous i⟩)

abbrev CoordinateRing := PolynomialRing ⧸ definingIdeal

def grading : ℕ → Submodule ℚ CoordinateRing :=
  ProjectiveBaseSchemeGrading.component polynomialGrading definingIdeal

instance coordinateRingGradedAlgebra : GradedAlgebra grading :=
  ProjectiveBaseSchemeGrading.quotientGradedAlgebra polynomialGrading definingIdeal
    definingIdeal_homogeneous

/-- Quotient images of the four homogeneous coordinates. -/
def coordinate (i : Fin 4) : CoordinateRing := Ideal.Quotient.mk definingIdeal (X i)

abbrev m := coordinate 0
abbrev u := coordinate 1
abbrev v := coordinate 2
abbrev z := coordinate 3

theorem coordinate_degree (i : Fin 4) : coordinate i∈grading 1 :=
  ⟨X i,isHomogeneous_X ℚ i,rfl⟩

theorem coordinate_relation (i : Fin 2) :
    Ideal.Quotient.mk definingIdeal (relation i)=0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i,rfl⟩)

theorem u_sq : u^2=15*m^2+1210*z^2 := by
  have h := coordinate_relation 0
  change Ideal.Quotient.mk definingIdeal
    (X 1^2-C 15*X 0^2-C 1210*X 3^2)=0 at h
  simp only [map_sub,map_pow,map_mul] at h
  change u^2-15*m^2-1210*z^2=0 at h
  linear_combination h

theorem v_sq : v^2=10*m^2+1215*z^2 := by
  have h := coordinate_relation 1
  change Ideal.Quotient.mk definingIdeal
    (X 2^2-C 10*X 0^2-C 1215*X 3^2)=0 at h
  simp only [map_sub,map_pow,map_mul] at h
  change v^2-10*m^2-1215*z^2=0 at h
  linear_combination h

/-- The projective base as a scheme. -/
def scheme : Scheme := AlgebraicGeometry.Proj grading

/-- The four coordinate images generate the quotient as a degree-zero
algebra, so the standard coordinate opens cover its projective spectrum. -/
theorem coordinate_adjoin : Algebra.adjoin (grading 0) (Set.range coordinate)=⊤ := by
  have hpoly : ∀p : PolynomialRing,Ideal.Quotient.mk definingIdeal p∈
      Algebra.adjoin (grading 0) (Set.range coordinate) := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C r =>
      have h0 : Ideal.Quotient.mk definingIdeal (C r)∈grading 0 :=
        ⟨C r,isHomogeneous_C (Fin 4) r,rfl⟩
      exact (Algebra.adjoin (grading 0) (Set.range coordinate)).algebraMap_mem
        ⟨Ideal.Quotient.mk definingIdeal (C r),h0⟩
    | add p q hp hq => simpa only [map_add] using add_mem hp hq
    | mul_X p i hp =>
      simpa only [map_mul,coordinate] using mul_mem hp
        (Algebra.subset_adjoin (show coordinate i∈Set.range coordinate from ⟨i,rfl⟩))
  apply top_unique
  intro x _
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective x
  exact hpoly p

theorem coordinate_opens_cover :
    ⨆ i : Fin 4,Proj.basicOpen grading (coordinate i)=⊤ :=
  Proj.iSup_basicOpen_eq_top' grading coordinate (fun i => ⟨1,coordinate_degree i⟩)
    coordinate_adjoin

/-- The two standard affine opens intended to cover the projective curve. -/
def zOpen : scheme.Opens := Proj.basicOpen grading z
def mOpen : scheme.Opens := Proj.basicOpen grading m

/-- The two-open cover: a homogeneous prime containing m and z
would contain u and v by the two quadratic equations. -/
theorem two_chart_cover : zOpen ⊔ mOpen=⊤ := by
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
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ hm 2 (by decide)))
      (Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ hz 2 (by decide)))
  have hv : v∈x.asHomogeneousIdeal.toIdeal := by
    apply x.isPrime.mem_of_pow_mem 2
    rw [v_sq]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ hm 2 (by decide)))
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

abbrev zChartRing := HomogeneousLocalization.Away grading z
abbrev mChartRing := HomogeneousLocalization.Away grading m

/-- Affine scheme isomorphism for the z≠0 chart. -/
def zChartIso : zOpen.toScheme ≅ Spec (CommRingCat.of zChartRing) :=
  Proj.basicOpenIsoSpec grading z (coordinate_degree 3) (by decide : 0<1)

/-- Affine scheme isomorphism for the m≠0 chart. -/
def mChartIso : mOpen.toScheme ≅ Spec (CommRingCat.of mChartRing) :=
  Proj.basicOpenIsoSpec grading m (coordinate_degree 0) (by decide : 0<1)

end
end Z2Z4Rank6.ProjectiveBaseScheme
