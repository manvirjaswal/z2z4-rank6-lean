module

public import Z2Z4Rank6.ProjectiveBaseSchemeGrading
public import Z2Z4Rank6.SecondTorsionCoverEquationForms
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.Tactic

@[expose] public section

/-!
# Weighted projective square-obstruction covers

Jaswal, Theorem 8.1(c), DOI 10.5281/zenodo.23437117. The two covers have equations
u²=29(m²−βz²), v²=−29β(m²−γz²), r²=∓(m²−z²)(m²−λ²z²), with weights
(m,u,v,z,r)=(1,1,1,1,2). This file constructs their homogeneous
quotient Proj schemes and two-chart cover. Genus is a separate
structure-sheaf cohomology calculation.
-/

namespace Z2Z4Rank6.SecondTorsionCoverProjective
noncomputable section
open scoped Classical
open MvPolynomial AlgebraicGeometry CategoryTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

abbrev PolynomialRing := MvPolynomial (Fin 5) ℚ
def weights : Fin 5→ℕ := ![1,1,1,1,2]
def polynomialGrading : ℕ→Submodule ℚ PolynomialRing :=
  MvPolynomial.weightedHomogeneousSubmodule ℚ weights
instance polynomialGradedAlgebra : GradedAlgebra polynomialGrading :=
  MvPolynomial.weightedGradedAlgebra ℚ weights

open SecondTorsionCoverEquations SecondFamily

def rootIndex : Fin 3→Fin 5 := ![1,2,4]
def relation (ε : Bool) (i : Fin 3) : PolynomialRing :=
  MvPolynomial.X (rootIndex i)^2-binary ε (MvPolynomial.X 3) (MvPolynomial.X 0) i
def relationDegree : Fin 3→ℕ := ![2,2,4]
def definingIdeal (ε : Bool) : Ideal PolynomialRing := Ideal.span (Set.range (relation ε))

private theorem m_homogeneous : (MvPolynomial.X (0:Fin 5) : PolynomialRing).IsWeightedHomogeneous weights 1 := by
  simpa [weights] using isWeightedHomogeneous_X ℚ weights (0:Fin 5)
private theorem z_homogeneous : (MvPolynomial.X (3:Fin 5) : PolynomialRing).IsWeightedHomogeneous weights 1 := by
  simpa [weights] using isWeightedHomogeneous_X ℚ weights (3:Fin 5)

theorem relation_homogeneous (ε : Bool) (i : Fin 3) :
    (relation ε i).IsWeightedHomogeneous weights (relationDegree i) := by
  fin_cases i
  · change IsWeightedHomogeneous weights
      (MvPolynomial.X 1^2-29*(MvPolynomial.X 0^2-C beta*MvPolynomial.X 3^2)) 2
    have h := ((isWeightedHomogeneous_X ℚ weights (1:Fin 5)).pow 2).sub
      (((m_homogeneous.pow 2).sub ((z_homogeneous.pow 2).C_mul beta)).C_mul 29)
    norm_num only [map_ofNat,map_neg] at h
    convert h using 1; norm_num [weights]
  · change IsWeightedHomogeneous weights
      (MvPolynomial.X 2^2-C (-29*beta)*(MvPolynomial.X 0^2-C gamma*MvPolynomial.X 3^2)) 2
    have h := ((isWeightedHomogeneous_X ℚ weights (2:Fin 5)).pow 2).sub
      (((m_homogeneous.pow 2).sub ((z_homogeneous.pow 2).C_mul gamma)).C_mul (-29*beta))
    convert h using 1; norm_num [weights]
  · change IsWeightedHomogeneous weights
      (MvPolynomial.X 4^2-(-C (TorsionHyperelliptic.sign ε)*(MvPolynomial.X 0^2-MvPolynomial.X 3^2)*
        (MvPolynomial.X 0^2-C (lambda^2)*MvPolynomial.X 3^2))) 4
    have h := ((isWeightedHomogeneous_X ℚ weights (4:Fin 5)).pow 2).sub
      ((((m_homogeneous.pow 2).sub (z_homogeneous.pow 2)).C_mul
        (-TorsionHyperelliptic.sign ε)).mul
        ((m_homogeneous.pow 2).sub ((z_homogeneous.pow 2).C_mul (lambda^2))))
    norm_num only [map_ofNat,map_neg] at h
    convert h using 1; norm_num [weights]

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

theorem root_sq (ε : Bool) (i : Fin 3) :
    coordinate ε (rootIndex i)^2=binary ε (z ε) (m ε) i := by
  have h := coordinate_relation ε i
  simp only [relation,map_sub,map_pow,SecondTorsionCoverEquations.map_binary] at h
  exact sub_eq_zero.mp h

theorem u_sq (ε : Bool) : u ε^2=binary ε (z ε) (m ε) 0 := root_sq ε 0
theorem v_sq (ε : Bool) : v ε^2=binary ε (z ε) (m ε) 1 := root_sq ε 1
theorem r_sq (ε : Bool) : r ε^2=binary ε (z ε) (m ε) 2 := root_sq ε 2

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
  have hm2 : m ε^2∈x.asHomogeneousIdeal.toIdeal := Ideal.pow_mem_of_mem _ hm 2 (by decide)
  have hz2 : z ε^2∈x.asHomogeneousIdeal.toIdeal := Ideal.pow_mem_of_mem _ hz 2 (by decide)
  have hu : u ε∈x.asHomogeneousIdeal.toIdeal := by
    apply x.isPrime.mem_of_pow_mem 2
    rw [u_sq]
    exact Ideal.mul_mem_left _ _ (Ideal.sub_mem _ hm2 (Ideal.mul_mem_left _ _ hz2))
  have hv : v ε∈x.asHomogeneousIdeal.toIdeal := by
    apply x.isPrime.mem_of_pow_mem 2
    rw [v_sq]
    exact Ideal.mul_mem_left _ _ (Ideal.sub_mem _ hm2 (Ideal.mul_mem_left _ _ hz2))
  have hr : r ε∈x.asHomogeneousIdeal.toIdeal := by
    apply x.isPrime.mem_of_pow_mem 2
    rw [r_sq]
    exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ (Ideal.sub_mem _ hm2 hz2))
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
end Z2Z4Rank6.SecondTorsionCoverProjective
