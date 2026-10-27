import Z2Z4Rank6.ProjectiveBaseSchemeGrading
import Z2Z4Rank6.ThirdTwistCoverEquationForms
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Mathlib.Tactic

/-!
# Genus-five third-twist projective base

This is the homogeneous quotient Proj in coordinates (m,u,v,z,w),
all of degree 1, with u²=15m²+1210z², v²=10m²+1215z² and
w²=4m²+45z².
-/

namespace Z2Z4Rank6.ThirdTwistCoverProjective
noncomputable section
open scoped Classical
open MvPolynomial AlgebraicGeometry CategoryTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

abbrev PolynomialRing := MvPolynomial (Fin 5) ℚ
def weights : Fin 5→ℕ := ![1,1,1,1,1]
def polynomialGrading : ℕ→Submodule ℚ PolynomialRing :=
  MvPolynomial.weightedHomogeneousSubmodule ℚ weights
instance polynomialGradedAlgebra : GradedAlgebra polynomialGrading :=
  MvPolynomial.weightedGradedAlgebra ℚ weights

open ThirdTwistCoverEquations

def rootIndex : Fin 3→Fin 5 := ![1,2,4]
def relation  (i : Fin 3) : PolynomialRing :=
  MvPolynomial.X (rootIndex i)^2-binary (MvPolynomial.X 3) (MvPolynomial.X 0) i
def relationDegree : Fin 3→ℕ := ![2,2,2]
def definingIdeal  : Ideal PolynomialRing := Ideal.span (Set.range (relation))

private theorem m_homogeneous : (MvPolynomial.X (0:Fin 5) : PolynomialRing).IsWeightedHomogeneous weights 1 := by
  simpa [weights] using isWeightedHomogeneous_X ℚ weights (0:Fin 5)
private theorem z_homogeneous : (MvPolynomial.X (3:Fin 5) : PolynomialRing).IsWeightedHomogeneous weights 1 := by
  simpa [weights] using isWeightedHomogeneous_X ℚ weights (3:Fin 5)

theorem relation_homogeneous (i : Fin 3) :
    (relation i).IsWeightedHomogeneous weights (relationDegree i) := by
  fin_cases i
  · change IsWeightedHomogeneous weights (MvPolynomial.X 1^2-(15*MvPolynomial.X 0^2+1210*MvPolynomial.X 3^2)) 2
    have h := ((isWeightedHomogeneous_X ℚ weights (1:Fin 5)).pow 2).sub
      (((m_homogeneous.pow 2).C_mul 15).add ((z_homogeneous.pow 2).C_mul 1210))
    norm_num only [map_ofNat] at h
    convert h using 1; norm_num [weights]
  · change IsWeightedHomogeneous weights (MvPolynomial.X 2^2-(10*MvPolynomial.X 0^2+1215*MvPolynomial.X 3^2)) 2
    have h := ((isWeightedHomogeneous_X ℚ weights (2:Fin 5)).pow 2).sub
      (((m_homogeneous.pow 2).C_mul 10).add ((z_homogeneous.pow 2).C_mul 1215))
    norm_num only [map_ofNat] at h
    convert h using 1; norm_num [weights]
  · change IsWeightedHomogeneous weights (MvPolynomial.X 4^2-(4*MvPolynomial.X 0^2+45*MvPolynomial.X 3^2)) 2
    have h := ((isWeightedHomogeneous_X ℚ weights (4:Fin 5)).pow 2).sub
      (((m_homogeneous.pow 2).C_mul 4).add ((z_homogeneous.pow 2).C_mul 45))
    norm_num only [map_ofNat] at h
    convert h using 1; norm_num [weights]

theorem definingIdeal_homogeneous  : (definingIdeal).IsHomogeneous polynomialGrading :=
  Ideal.homogeneous_span polynomialGrading _ (by
    rintro _ ⟨i,rfl⟩
    exact ⟨relationDegree i,relation_homogeneous i⟩)

abbrev CoordinateRing  := PolynomialRing⧸definingIdeal
def grading  : ℕ→Submodule ℚ (CoordinateRing) :=
  ProjectiveBaseSchemeGrading.component polynomialGrading (definingIdeal)
instance coordinateRingGradedAlgebra  : GradedAlgebra (grading) :=
  ProjectiveBaseSchemeGrading.quotientGradedAlgebra polynomialGrading (definingIdeal)
    (definingIdeal_homogeneous)

def coordinate  (i : Fin 5) : CoordinateRing := Ideal.Quotient.mk (definingIdeal) (MvPolynomial.X i)
abbrev m  := coordinate 0
abbrev u  := coordinate 1
abbrev v  := coordinate 2
abbrev z  := coordinate 3
abbrev r  := coordinate 4
abbrev w := r

theorem coordinate_degree  (i : Fin 5) : coordinate i∈grading (weights i) :=
  ⟨MvPolynomial.X i,isWeightedHomogeneous_X ℚ weights i,rfl⟩
theorem coordinate_relation  (i : Fin 3) :
    Ideal.Quotient.mk (definingIdeal) (relation i)=0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i,rfl⟩)

theorem root_sq  (i : Fin 3) :
    coordinate (rootIndex i)^2=binary (z) (m) i := by
  have h := coordinate_relation i
  simp only [relation,map_sub,map_pow,ThirdTwistCoverEquations.map_binary] at h
  exact sub_eq_zero.mp h

theorem u_sq  : u^2=binary (z) (m) 0 := root_sq 0
theorem v_sq  : v^2=binary (z) (m) 1 := root_sq 1
theorem r_sq  : r^2=binary (z) (m) 2 := root_sq 2

def scheme  : Scheme := AlgebraicGeometry.Proj (grading)

theorem coordinate_adjoin  :
    Algebra.adjoin (grading 0) (Set.range (coordinate))=⊤ := by
  have hpoly : ∀p : PolynomialRing,Ideal.Quotient.mk (definingIdeal) p∈
      Algebra.adjoin (grading 0) (Set.range (coordinate)) := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C q =>
      have h0 : Ideal.Quotient.mk (definingIdeal) (C q)∈grading 0 :=
        ⟨C q,isWeightedHomogeneous_C weights q,rfl⟩
      exact (Algebra.adjoin (grading 0) (Set.range (coordinate))).algebraMap_mem
        ⟨Ideal.Quotient.mk (definingIdeal) (C q),h0⟩
    | add p q hp hq => simpa only [map_add] using add_mem hp hq
    | mul_X p i hp =>
      simpa only [map_mul,coordinate] using mul_mem hp
        (Algebra.subset_adjoin (show coordinate i∈Set.range (coordinate) from ⟨i,rfl⟩))
  apply top_unique
  intro x _
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective x
  exact hpoly p

theorem coordinate_opens_cover  :
    ⨆i : Fin 5,Proj.basicOpen (grading) (coordinate i)=⊤ :=
  Proj.iSup_basicOpen_eq_top' (grading) (coordinate)
    (fun i => ⟨weights i,coordinate_degree i⟩) (coordinate_adjoin)

def zOpen  : (scheme).Opens := Proj.basicOpen (grading) (z)
def mOpen  : (scheme).Opens := Proj.basicOpen (grading) (m)

theorem two_chart_cover  : zOpen⊔mOpen=⊤ := by
  apply top_unique
  intro x _
  change z∉x.asHomogeneousIdeal ∨ m∉x.asHomogeneousIdeal
  by_contra h
  push Not at h
  have hz : z∈x.asHomogeneousIdeal.toIdeal := h.1
  have hm : m∈x.asHomogeneousIdeal.toIdeal := h.2
  have hm2 : m^2∈x.asHomogeneousIdeal.toIdeal := Ideal.pow_mem_of_mem _ hm 2 (by decide)
  have hz2 : z^2∈x.asHomogeneousIdeal.toIdeal := Ideal.pow_mem_of_mem _ hz 2 (by decide)
  have hu : u∈x.asHomogeneousIdeal.toIdeal := by
    apply x.isPrime.mem_of_pow_mem 2
    rw [u_sq]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hm2) (Ideal.mul_mem_left _ _ hz2)
  have hv : v∈x.asHomogeneousIdeal.toIdeal := by
    apply x.isPrime.mem_of_pow_mem 2
    rw [v_sq]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hm2) (Ideal.mul_mem_left _ _ hz2)
  have hr : r∈x.asHomogeneousIdeal.toIdeal := by
    apply x.isPrime.mem_of_pow_mem 2
    rw [r_sq]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hm2) (Ideal.mul_mem_left _ _ hz2)
  have hall : ∀i : Fin 5,coordinate i∈x.asHomogeneousIdeal := by
    intro i
    fin_cases i
    · exact hm
    · exact hu
    · exact hv
    · exact hz
    · exact hr
  have hx : x∈⨆i : Fin 5,Proj.basicOpen (grading) (coordinate i) := by
    rw [coordinate_opens_cover]
    trivial
  obtain ⟨i,hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  exact hi (hall i)

abbrev zChartRing  := HomogeneousLocalization.Away (grading) (z)
abbrev mChartRing  := HomogeneousLocalization.Away (grading) (m)
def zChartIso  : (zOpen).toScheme≅Spec (CommRingCat.of (zChartRing)) :=
  Proj.basicOpenIsoSpec (grading) (z) (coordinate_degree 3) (by decide : 0<1)
def mChartIso  : (mOpen).toScheme≅Spec (CommRingCat.of (mChartRing)) :=
  Proj.basicOpenIsoSpec (grading) (m) (coordinate_degree 0) (by decide : 0<1)

end
end Z2Z4Rank6.ThirdTwistCoverProjective
