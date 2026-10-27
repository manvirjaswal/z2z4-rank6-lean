module

public import Z2Z4Rank6.ProjectiveBaseSchemeGrading
public import Z2Z4Rank6.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.Tactic

@[expose] public section

/-!
# The projective Weierstrass cubic E_C

Jaswal, DOI 10.5281/zenodo.23437117, Theorem 1.2(a), Lemma 4.1.
The coordinate order is(X,Y,Z). The homogeneous cubic is
Y²Z−MvPolynomial.X³−MvPolynomial.X²Z+137620XZ²+10504000Z³=0, including the printed nonzero a6.
Its Proj is constructed from the graded quotient ring.
-/
namespace Z2Z4Rank6.ECProjectiveScheme
noncomputable section
open scoped Classical
open MvPolynomial AlgebraicGeometry CategoryTheory

abbrev PolynomialRing := MvPolynomial (Fin 3) ℚ
def polynomialGrading : ℕ→Submodule ℚ PolynomialRing :=
  MvPolynomial.homogeneousSubmodule (Fin 3) ℚ
instance polynomialGradedAlgebra : GradedAlgebra polynomialGrading := MvPolynomial.gradedAlgebra

def relation : PolynomialRing :=
  MvPolynomial.X 1^2*MvPolynomial.X 2-MvPolynomial.X 0^3-MvPolynomial.X 0^2*MvPolynomial.X 2+C 137620*MvPolynomial.X 0*MvPolynomial.X 2^2+C 10504000*MvPolynomial.X 2^3

def definingIdeal : Ideal PolynomialRing := Ideal.span {relation}

theorem relation_homogeneous : relation.IsHomogeneous 3 := by
  have hx := isHomogeneous_X ℚ (0:Fin 3)
  have hy := isHomogeneous_X ℚ (1:Fin 3)
  have hz := isHomogeneous_X ℚ (2:Fin 3)
  have h1 : (MvPolynomial.X (1:Fin 3)^2*MvPolynomial.X 2).IsHomogeneous 3 :=
    (hy.pow 2).mul hz
  have h2 : (MvPolynomial.X (0:Fin 3)^3).IsHomogeneous 3 := hx.pow 3
  have h3 : (MvPolynomial.X (0:Fin 3)^2*MvPolynomial.X 2).IsHomogeneous 3 :=
    (hx.pow 2).mul hz
  have h4 : (C (137620:ℚ)*MvPolynomial.X (0:Fin 3)*MvPolynomial.X 2^2).IsHomogeneous 3 := by
    simpa only [mul_assoc] using (hx.mul (hz.pow 2)).C_mul 137620
  have h5 : (C (10504000:ℚ)*MvPolynomial.X (2:Fin 3)^3).IsHomogeneous 3 :=
    (hz.pow 3).C_mul 10504000
  exact (((h1.sub h2).sub h3).add h4).add h5

theorem definingIdeal_homogeneous : definingIdeal.IsHomogeneous polynomialGrading :=
  Ideal.homogeneous_span polynomialGrading _ (by
    rintro p (rfl: p=relation)
    exact ⟨3,relation_homogeneous⟩)

abbrev CoordinateRing := PolynomialRing⧸definingIdeal
def grading : ℕ→Submodule ℚ CoordinateRing :=
  ProjectiveBaseSchemeGrading.component polynomialGrading definingIdeal
instance coordinateRingGradedAlgebra : GradedAlgebra grading :=
  ProjectiveBaseSchemeGrading.quotientGradedAlgebra polynomialGrading definingIdeal
    definingIdeal_homogeneous

def coordinate (i:Fin 3) : CoordinateRing := Ideal.Quotient.mk definingIdeal (MvPolynomial.X i)
abbrev x := coordinate 0
abbrev y := coordinate 1
abbrev z := coordinate 2

theorem coordinate_degree (i:Fin 3) : coordinate i∈grading 1 :=
  ⟨MvPolynomial.X i,isHomogeneous_X ℚ i,rfl⟩

theorem coordinate_relation : Ideal.Quotient.mk definingIdeal relation=0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton relation))

theorem cubic_equation : y^2*z=x^3+x^2*z-137620*x*z^2-10504000*z^3 := by
  have h := coordinate_relation
  simp only [relation,map_sub,map_add,map_pow,map_mul] at h
  change y^2*z-x^3-x^2*z+137620*x*z^2+10504000*z^3=0 at h
  linear_combination h

/-- The projective cubic scheme. -/
def scheme : Scheme := Proj grading

theorem coordinate_adjoin : Algebra.adjoin (grading 0) (Set.range coordinate)=⊤ := by
  have hpoly : ∀p:PolynomialRing,Ideal.Quotient.mk definingIdeal p∈
      Algebra.adjoin (grading 0) (Set.range coordinate) := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C r =>
      have h0 : Ideal.Quotient.mk definingIdeal (C r)∈grading 0 :=
        ⟨C r,isHomogeneous_C (Fin 3) r,rfl⟩
      exact (Algebra.adjoin (grading 0) (Set.range coordinate)).algebraMap_mem
        ⟨Ideal.Quotient.mk definingIdeal (C r),h0⟩
    | add p q hp hq => simpa only [map_add] using add_mem hp hq
    | mul_X p i hp =>
      simpa only [map_mul,coordinate] using mul_mem hp
        (Algebra.subset_adjoin (show coordinate i∈Set.range coordinate from ⟨i,rfl⟩))
  apply top_unique
  intro q _
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective q
  exact hpoly p

theorem coordinate_opens_cover : ⨆i:Fin 3,Proj.basicOpen grading (coordinate i)=⊤ :=
  Proj.iSup_basicOpen_eq_top' grading coordinate (fun i=>⟨1,coordinate_degree i⟩) coordinate_adjoin

def zOpen : scheme.Opens := Proj.basicOpen grading z
def yOpen : scheme.Opens := Proj.basicOpen grading y

/-- The displayed affine chart and the chart containing infinity cover the cubic. -/
theorem two_chart_cover : zOpen⊔yOpen=⊤ := by
  apply top_unique
  intro p _
  change z∉p.asHomogeneousIdeal ∨ y∉p.asHomogeneousIdeal
  by_contra h
  push Not at h
  have hz : z∈p.asHomogeneousIdeal.toIdeal := h.1
  have hy : y∈p.asHomogeneousIdeal.toIdeal := h.2
  have hx : x∈p.asHomogeneousIdeal.toIdeal := by
    apply p.isPrime.mem_of_pow_mem 3
    have he : x^3=y^2*z-x^2*z+137620*x*z^2+10504000*z^3 := by
      linear_combination -cubic_equation
    rw [he]
    exact Ideal.add_mem _ (Ideal.add_mem _
      (Ideal.sub_mem _ (Ideal.mul_mem_left _ _ hz) (Ideal.mul_mem_left _ _ hz))
      (Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ hz 2 (by decide))))
      (Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ hz 3 (by decide)))
  have hall : ∀i:Fin 3,coordinate i∈p.asHomogeneousIdeal := by
    intro i
    fin_cases i
    · exact hx
    · exact hy
    · exact hz
  have hp : p∈⨆i:Fin 3,Proj.basicOpen grading (coordinate i) := by
    rw [coordinate_opens_cover]
    trivial
  obtain ⟨i,hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hp
  exact hi (hall i)

abbrev zChartRing := HomogeneousLocalization.Away grading z
abbrev yChartRing := HomogeneousLocalization.Away grading y
def zChartIso : zOpen.toScheme≅Spec (CommRingCat.of zChartRing) :=
  Proj.basicOpenIsoSpec grading z (coordinate_degree 2) (by decide:0<1)
def yChartIso : yOpen.toScheme≅Spec (CommRingCat.of yChartRing) :=
  Proj.basicOpenIsoSpec grading y (coordinate_degree 1) (by decide:0<1)

/-- Evaluation at the homogeneous coordinates (0,1,0). -/
def infinityEvaluation : CoordinateRing→ₐ[ℚ]ℚ :=
  Ideal.Quotient.liftₐ definingIdeal (MvPolynomial.aeval ![(0:ℚ),1,0]) (by
    have hker : definingIdeal≤RingHom.ker (MvPolynomial.aeval ![(0:ℚ),1,0]).toRingHom := by
      apply Ideal.span_le.mpr
      rintro p (rfl:p=relation)
      change (MvPolynomial.aeval ![(0:ℚ),1,0]) relation=0
      norm_num [relation]
    intro p hp
    exact hker hp)

@[simp] theorem infinityEvaluation_coordinate (i:Fin 3) :
    infinityEvaluation (coordinate i)=![(0:ℚ),1,0] i := by
  change (MvPolynomial.aeval ![(0:ℚ),1,0]) (MvPolynomial.X i)=_
  simp

instance coordinateRing_nontrivial : Nontrivial CoordinateRing :=
  infinityEvaluation.toRingHom.domain_nontrivial

end
end Z2Z4Rank6.ECProjectiveScheme
