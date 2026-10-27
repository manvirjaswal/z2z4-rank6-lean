module

public import Z2Z4Rank6.ProjectiveBaseSchemeGrading
public import Z2Z4Rank6.TorsionSquareLiftData
public import Z2Z4Rank6.HeightInvariantForms
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.Tactic

@[expose] public section

/-!
# Weighted projective square-obstruction covers

Jaswal, Section 6, DOI 10.5281/zenodo.23437117. The two covers have equations
u²=15m²+1210z², v²=10m²+1215z², r²=±A(z,m)B(z,m), with weights
(m,u,v,z,r)=(1,1,1,1,4). This file constructs their homogeneous
quotient Proj schemes and two-chart cover. Genus is a separate
structure-sheaf cohomology calculation.
-/

namespace Z2Z4Rank6.TorsionCoverProjective
noncomputable section
open scoped Classical
open MvPolynomial AlgebraicGeometry CategoryTheory

abbrev PolynomialRing := MvPolynomial (Fin 5) ℚ
def weights : Fin 5→ℕ := ![1,1,1,1,4]
def polynomialGrading : ℕ→Submodule ℚ PolynomialRing :=
  MvPolynomial.weightedHomogeneousSubmodule ℚ weights
instance polynomialGradedAlgebra : GradedAlgebra polynomialGrading :=
  MvPolynomial.weightedGradedAlgebra ℚ weights

def relation (ε : Bool) : Fin 3→PolynomialRing :=
  ![MvPolynomial.X 1^2-C 15*MvPolynomial.X 0^2-C 1210*MvPolynomial.X 3^2,
    MvPolynomial.X 2^2-C 10*MvPolynomial.X 0^2-C 1215*MvPolynomial.X 3^2,
    MvPolynomial.X 4^2-C (TorsionHyperelliptic.sign ε)*
      HeightInvariantForms.binaryA (MvPolynomial.X 3) (MvPolynomial.X 0)*HeightInvariantForms.binaryB (MvPolynomial.X 3) (MvPolynomial.X 0)]
def relationDegree : Fin 3→ℕ := ![2,2,8]
def definingIdeal (ε : Bool) : Ideal PolynomialRing := Ideal.span (Set.range (relation ε))

private theorem m_homogeneous : (MvPolynomial.X (0:Fin 5) : PolynomialRing).IsWeightedHomogeneous weights 1 := by
  simpa [weights] using isWeightedHomogeneous_X ℚ weights (0:Fin 5)
private theorem z_homogeneous : (MvPolynomial.X (3:Fin 5) : PolynomialRing).IsWeightedHomogeneous weights 1 := by
  simpa [weights] using isWeightedHomogeneous_X ℚ weights (3:Fin 5)

theorem binaryA_homogeneous :
    IsWeightedHomogeneous weights
      (HeightInvariantForms.binaryA (MvPolynomial.X (3:Fin 5)) (MvPolynomial.X 0) : PolynomialRing) 4 := by
  have h := ((((m_homogeneous.sub (z_homogeneous.C_mul 99)).mul
    (m_homogeneous.add z_homogeneous)).mul
    (m_homogeneous.sub (z_homogeneous.C_mul 11))).mul
    (m_homogeneous.add (z_homogeneous.C_mul 9))).C_mul 7
  norm_num only [map_ofNat,map_neg] at h
  convert h using 1; simp only [HeightInvariantForms.binaryA]; ring

theorem binaryB_homogeneous :
    IsWeightedHomogeneous weights
      (HeightInvariantForms.binaryB (MvPolynomial.X (3:Fin 5)) (MvPolynomial.X 0) : PolynomialRing) 4 := by
  have h := ((((m_homogeneous.add (z_homogeneous.C_mul 99)).mul
    (m_homogeneous.sub z_homogeneous)).mul
    (m_homogeneous.add (z_homogeneous.C_mul 11))).mul
    (m_homogeneous.sub (z_homogeneous.C_mul 9))).C_mul (-7)
  norm_num only [map_ofNat,map_neg] at h
  convert h using 1; simp only [HeightInvariantForms.binaryB]; ring

theorem relation_homogeneous (ε : Bool) (i : Fin 3) :
    (relation ε i).IsWeightedHomogeneous weights (relationDegree i) := by
  fin_cases i
  · exact (((isWeightedHomogeneous_X ℚ weights (1:Fin 5)).pow 2).sub
      (m_homogeneous.pow 2 |>.C_mul 15)).sub (z_homogeneous.pow 2 |>.C_mul 1210)
  · exact (((isWeightedHomogeneous_X ℚ weights (2:Fin 5)).pow 2).sub
      (m_homogeneous.pow 2 |>.C_mul 10)).sub (z_homogeneous.pow 2 |>.C_mul 1215)
  · exact ((isWeightedHomogeneous_X ℚ weights (4:Fin 5)).pow 2).sub
      ((binaryA_homogeneous.C_mul (TorsionHyperelliptic.sign ε)).mul binaryB_homogeneous)

theorem definingIdeal_homogeneous (ε : Bool) : (definingIdeal ε).IsHomogeneous polynomialGrading :=
  Ideal.homogeneous_span polynomialGrading _ (by
    rintro _ ⟨i,rfl⟩
    exact ⟨relationDegree i,relation_homogeneous ε i⟩)

abbrev CoordinateRing (ε : Bool) := PolynomialRing⧸definingIdeal ε
def grading (ε : Bool) : ℕ→Submodule ℚ (CoordinateRing ε) :=
  ProjectiveBaseSchemeGrading.component polynomialGrading (definingIdeal ε)
instance coordinateRingGradedAlgebra (ε : Bool) : GradedAlgebra (grading ε) :=
  ProjectiveBaseSchemeGrading.quotientGradedAlgebra polynomialGrading (definingIdeal ε)
    (definingIdeal_homogeneous ε)

def coordinate (ε : Bool) (i : Fin 5) : CoordinateRing ε := Ideal.Quotient.mk (definingIdeal ε) (MvPolynomial.X i)
abbrev m (ε : Bool) := coordinate ε 0
abbrev u (ε : Bool) := coordinate ε 1
abbrev v (ε : Bool) := coordinate ε 2
abbrev z (ε : Bool) := coordinate ε 3
abbrev r (ε : Bool) := coordinate ε 4

theorem coordinate_degree (ε : Bool) (i : Fin 5) : coordinate ε i∈grading ε (weights i) :=
  ⟨MvPolynomial.X i,isWeightedHomogeneous_X ℚ weights i,rfl⟩
theorem coordinate_relation (ε : Bool) (i : Fin 3) :
    Ideal.Quotient.mk (definingIdeal ε) (relation ε i)=0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i,rfl⟩)

theorem u_sq (ε : Bool) : u ε^2=15*m ε^2+1210*z ε^2 := by
  have h := coordinate_relation ε 0
  change Ideal.Quotient.mk (definingIdeal ε) (MvPolynomial.X 1^2-C 15*MvPolynomial.X 0^2-C 1210*MvPolynomial.X 3^2)=0 at h
  simp only [map_sub,map_pow,map_mul] at h
  change u ε^2-15*m ε^2-1210*z ε^2=0 at h
  linear_combination h

theorem v_sq (ε : Bool) : v ε^2=10*m ε^2+1215*z ε^2 := by
  have h := coordinate_relation ε 1
  change Ideal.Quotient.mk (definingIdeal ε) (MvPolynomial.X 2^2-C 10*MvPolynomial.X 0^2-C 1215*MvPolynomial.X 3^2)=0 at h
  simp only [map_sub,map_pow,map_mul] at h
  change v ε^2-10*m ε^2-1215*z ε^2=0 at h
  linear_combination h

theorem r_sq (ε : Bool) : r ε^2=
    algebraMap ℚ (CoordinateRing ε) (TorsionHyperelliptic.sign ε)*
      HeightInvariantForms.binaryA (z ε) (m ε)*HeightInvariantForms.binaryB (z ε) (m ε) := by
  have h := coordinate_relation ε 2
  change Ideal.Quotient.mk (definingIdeal ε)
    (MvPolynomial.X 4^2-C (TorsionHyperelliptic.sign ε)*
      HeightInvariantForms.binaryA (MvPolynomial.X 3) (MvPolynomial.X 0)*HeightInvariantForms.binaryB (MvPolynomial.X 3) (MvPolynomial.X 0))=0 at h
  simp only [HeightInvariantForms.binaryA,HeightInvariantForms.binaryB,map_sub,map_add,map_pow,
    map_mul,map_neg,map_ofNat] at h
  change r ε^2-algebraMap ℚ (CoordinateRing ε) (TorsionHyperelliptic.sign ε)*
    HeightInvariantForms.binaryA (z ε) (m ε)*HeightInvariantForms.binaryB (z ε) (m ε)=0 at h
  exact sub_eq_zero.mp h

def scheme (ε : Bool) : Scheme := AlgebraicGeometry.Proj (grading ε)

theorem coordinate_adjoin (ε : Bool) :
    Algebra.adjoin (grading ε 0) (Set.range (coordinate ε))=⊤ := by
  have hpoly : ∀p : PolynomialRing,Ideal.Quotient.mk (definingIdeal ε) p∈
      Algebra.adjoin (grading ε 0) (Set.range (coordinate ε)) := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C q =>
      have h0 : Ideal.Quotient.mk (definingIdeal ε) (C q)∈grading ε 0 :=
        ⟨C q,isWeightedHomogeneous_C weights q,rfl⟩
      exact (Algebra.adjoin (grading ε 0) (Set.range (coordinate ε))).algebraMap_mem
        ⟨Ideal.Quotient.mk (definingIdeal ε) (C q),h0⟩
    | add p q hp hq => simpa only [map_add] using add_mem hp hq
    | mul_X p i hp =>
      simpa only [map_mul,coordinate] using mul_mem hp
        (Algebra.subset_adjoin (show coordinate ε i∈Set.range (coordinate ε) from ⟨i,rfl⟩))
  apply top_unique
  intro x _
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective x
  exact hpoly p

theorem coordinate_opens_cover (ε : Bool) :
    ⨆i : Fin 5,Proj.basicOpen (grading ε) (coordinate ε i)=⊤ :=
  Proj.iSup_basicOpen_eq_top' (grading ε) (coordinate ε)
    (fun i => ⟨weights i,coordinate_degree ε i⟩) (coordinate_adjoin ε)

def zOpen (ε : Bool) : (scheme ε).Opens := Proj.basicOpen (grading ε) (z ε)
def mOpen (ε : Bool) : (scheme ε).Opens := Proj.basicOpen (grading ε) (m ε)

theorem two_chart_cover (ε : Bool) : zOpen ε⊔mOpen ε=⊤ := by
  apply top_unique
  intro x _
  change z ε∉x.asHomogeneousIdeal ∨ m ε∉x.asHomogeneousIdeal
  by_contra h
  push Not at h
  have hz : z ε∈x.asHomogeneousIdeal.toIdeal := h.1
  have hm : m ε∈x.asHomogeneousIdeal.toIdeal := h.2
  have hu : u ε∈x.asHomogeneousIdeal.toIdeal := by
    apply x.isPrime.mem_of_pow_mem 2
    rw [u_sq]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ hm 2 (by decide)))
      (Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ hz 2 (by decide)))
  have hv : v ε∈x.asHomogeneousIdeal.toIdeal := by
    apply x.isPrime.mem_of_pow_mem 2
    rw [v_sq]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ hm 2 (by decide)))
      (Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ hz 2 (by decide)))
  have hr : r ε∈x.asHomogeneousIdeal.toIdeal := by
    apply x.isPrime.mem_of_pow_mem 2
    rw [r_sq]
    have hl : m ε-99*z ε∈x.asHomogeneousIdeal.toIdeal :=
      Ideal.sub_mem _ hm (Ideal.mul_mem_left _ _ hz)
    have ha : HeightInvariantForms.binaryA (z ε) (m ε)∈x.asHomogeneousIdeal.toIdeal :=
      Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _
        (Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ hl)))
    exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ ha)
  have hall : ∀i : Fin 5,coordinate ε i∈x.asHomogeneousIdeal := by
    intro i
    fin_cases i
    · exact hm
    · exact hu
    · exact hv
    · exact hz
    · exact hr
  have hx : x∈⨆i : Fin 5,Proj.basicOpen (grading ε) (coordinate ε i) := by
    rw [coordinate_opens_cover]
    trivial
  obtain ⟨i,hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  exact hi (hall i)

abbrev zChartRing (ε : Bool) := HomogeneousLocalization.Away (grading ε) (z ε)
abbrev mChartRing (ε : Bool) := HomogeneousLocalization.Away (grading ε) (m ε)
def zChartIso (ε : Bool) : (zOpen ε).toScheme≅Spec (CommRingCat.of (zChartRing ε)) :=
  Proj.basicOpenIsoSpec (grading ε) (z ε) (coordinate_degree ε 3) (by decide : 0<1)
def mChartIso (ε : Bool) : (mOpen ε).toScheme≅Spec (CommRingCat.of (mChartRing ε)) :=
  Proj.basicOpenIsoSpec (grading ε) (m ε) (coordinate_degree ε 0) (by decide : 0<1)

end
end Z2Z4Rank6.TorsionCoverProjective
