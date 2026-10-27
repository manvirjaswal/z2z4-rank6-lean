import Z2Z4Rank6.ProjectiveBaseSchemeGrading
import Z2Z4Rank6.GTorsionCoverEquationForms
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Mathlib.Tactic

/-!
# Weighted projective signed double covers of G

The equations are eta²=99m⁴−9998m²z²+970299z⁴ and
r²=±binaryA(z,m)binaryB(z,m), with weights (m,eta,z,r)=(1,2,1,4).
This constructs the homogeneous quotient Proj schemes and proves
the two-chart cover. Genus is a separate sheaf-cohomology calculation.
-/

namespace Z2Z4Rank6.GTorsionCoverProjective
noncomputable section
open scoped Classical
open MvPolynomial AlgebraicGeometry CategoryTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

abbrev PolynomialRing := MvPolynomial (Fin 4) ℚ
def weights : Fin 4→ℕ := ![1,2,1,4]
def polynomialGrading : ℕ→Submodule ℚ PolynomialRing :=
  MvPolynomial.weightedHomogeneousSubmodule ℚ weights
instance polynomialGradedAlgebra : GradedAlgebra polynomialGrading :=
  MvPolynomial.weightedGradedAlgebra ℚ weights

open GTorsionCoverEquations

def rootIndex : Fin 2→Fin 4 := ![1,3]
def relation (ε : Bool) (i : Fin 2) : PolynomialRing :=
  MvPolynomial.X (rootIndex i)^2-binary ε (MvPolynomial.X 2) (MvPolynomial.X 0) i
def relationDegree : Fin 2→ℕ := ![4,8]
def definingIdeal (ε : Bool) : Ideal PolynomialRing := Ideal.span (Set.range (relation ε))

private theorem m_homogeneous : (MvPolynomial.X (0:Fin 4) : PolynomialRing).IsWeightedHomogeneous weights 1 := by
  simpa [weights] using isWeightedHomogeneous_X ℚ weights (0:Fin 4)
private theorem z_homogeneous : (MvPolynomial.X (2:Fin 4) : PolynomialRing).IsWeightedHomogeneous weights 1 := by
  simpa [weights] using isWeightedHomogeneous_X ℚ weights (2:Fin 4)

theorem relation_homogeneous (ε : Bool) (i : Fin 2) :
    (relation ε i).IsWeightedHomogeneous weights (relationDegree i) := by
  fin_cases i
  · change IsWeightedHomogeneous weights
      (MvPolynomial.X 1^2-(99*MvPolynomial.X 0^4-
        9998*MvPolynomial.X 0^2*MvPolynomial.X 2^2+970299*MvPolynomial.X 2^4)) 4
    have hg := (((m_homogeneous.pow 4).C_mul 99).sub
      (((m_homogeneous.pow 2).mul (z_homogeneous.pow 2)).C_mul 9998)).add
      ((z_homogeneous.pow 4).C_mul 970299)
    have heq : (99*MvPolynomial.X 0^4-9998*(MvPolynomial.X 0^2*MvPolynomial.X 2^2)+
        970299*MvPolynomial.X 2^4 : PolynomialRing)=
        99*MvPolynomial.X 0^4-9998*MvPolynomial.X 0^2*MvPolynomial.X 2^2+
        970299*MvPolynomial.X 2^4 := by ring
    norm_num only [map_ofNat] at hg
    rw [heq] at hg
    have hu : (MvPolynomial.X (1:Fin 4)^2 : PolynomialRing).IsWeightedHomogeneous weights 4 := by
      simpa [weights] using (isWeightedHomogeneous_X ℚ weights (1:Fin 4)).pow 2
    exact hu.sub hg
  · change IsWeightedHomogeneous weights
      (MvPolynomial.X 3^2-C (TorsionHyperelliptic.sign ε)*
        HeightInvariantForms.binaryA (MvPolynomial.X 2) (MvPolynomial.X 0)*
        HeightInvariantForms.binaryB (MvPolynomial.X 2) (MvPolynomial.X 0)) 8
    have hA := ((((m_homogeneous.sub (z_homogeneous.C_mul 99)).mul
      (m_homogeneous.add z_homogeneous)).mul
      (m_homogeneous.sub (z_homogeneous.C_mul 11))).mul
      (m_homogeneous.add (z_homogeneous.C_mul 9))).C_mul 7
    have hB := ((((m_homogeneous.add (z_homogeneous.C_mul 99)).mul
      (m_homogeneous.sub z_homogeneous)).mul
      (m_homogeneous.add (z_homogeneous.C_mul 11))).mul
      (m_homogeneous.sub (z_homogeneous.C_mul 9))).C_mul (-7)
    have h := ((isWeightedHomogeneous_X ℚ weights (3:Fin 4)).pow 2).sub
      ((hA.C_mul (TorsionHyperelliptic.sign ε)).mul hB)
    norm_num only [map_ofNat,map_neg] at h
    convert h using 1 <;> norm_num [weights,HeightInvariantForms.binaryA,HeightInvariantForms.binaryB]
    all_goals ring

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

def coordinate (ε : Bool) (i : Fin 4) : CoordinateRing ε := Ideal.Quotient.mk (definingIdeal ε) (MvPolynomial.X i)
abbrev m (ε : Bool) := coordinate ε 0
abbrev u (ε : Bool) := coordinate ε 1
abbrev z (ε : Bool) := coordinate ε 2
abbrev r (ε : Bool) := coordinate ε 3

theorem coordinate_degree (ε : Bool) (i : Fin 4) : coordinate ε i∈grading ε (weights i) :=
  ⟨MvPolynomial.X i,isWeightedHomogeneous_X ℚ weights i,rfl⟩
theorem coordinate_relation (ε : Bool) (i : Fin 2) :
    Ideal.Quotient.mk (definingIdeal ε) (relation ε i)=0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i,rfl⟩)

theorem root_sq (ε : Bool) (i : Fin 2) :
    coordinate ε (rootIndex i)^2=binary ε (z ε) (m ε) i := by
  have h := coordinate_relation ε i
  simp only [relation,map_sub,map_pow,GTorsionCoverEquations.map_binary] at h
  exact sub_eq_zero.mp h

theorem u_sq (ε : Bool) : u ε^2=binary ε (z ε) (m ε) 0 := root_sq ε 0
theorem r_sq (ε : Bool) : r ε^2=binary ε (z ε) (m ε) 1 := root_sq ε 1

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
    ⨆i : Fin 4,Proj.basicOpen (grading ε) (coordinate ε i)=⊤ :=
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
  have hm4 : m ε^4∈x.asHomogeneousIdeal.toIdeal := Ideal.pow_mem_of_mem _ hm 4 (by decide)
  have hz4 : z ε^4∈x.asHomogeneousIdeal.toIdeal := Ideal.pow_mem_of_mem _ hz 4 (by decide)
  have hu : u ε∈x.asHomogeneousIdeal.toIdeal := by
    apply x.isPrime.mem_of_pow_mem 2
    rw [u_sq]
    change 99*m ε^4-9998*m ε^2*z ε^2+970299*z ε^4∈x.asHomogeneousIdeal.toIdeal
    exact Ideal.add_mem _
      (Ideal.sub_mem _ (Ideal.mul_mem_left _ _ hm4)
        (Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ hm2)))
      (Ideal.mul_mem_left _ _ hz4)
  have hr : r ε∈x.asHomogeneousIdeal.toIdeal := by
    apply x.isPrime.mem_of_pow_mem 2
    rw [r_sq]
    change algebraMap ℚ _ (TorsionHyperelliptic.sign ε)*
      HeightInvariantForms.binaryA (z ε) (m ε)*
      HeightInvariantForms.binaryB (z ε) (m ε)∈x.asHomogeneousIdeal.toIdeal
    have hA : HeightInvariantForms.binaryA (z ε) (m ε)∈x.asHomogeneousIdeal.toIdeal := by
      exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _
        (Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _
          (Ideal.sub_mem _ hm (Ideal.mul_mem_left _ _ hz)))))
    exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ hA)
  have hall : ∀i : Fin 4,coordinate ε i∈x.asHomogeneousIdeal := by
    intro i
    fin_cases i
    · exact hm
    · exact hu
    · exact hz
    · exact hr
  have hx : x∈⨆i : Fin 4,Proj.basicOpen (grading ε) (coordinate ε i) := by
    rw [coordinate_opens_cover]
    trivial
  obtain ⟨i,hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  exact hi (hall i)

abbrev zChartRing (ε : Bool) := HomogeneousLocalization.Away (grading ε) (z ε)
abbrev mChartRing (ε : Bool) := HomogeneousLocalization.Away (grading ε) (m ε)
def zChartIso (ε : Bool) : (zOpen ε).toScheme≅Spec (CommRingCat.of (zChartRing ε)) :=
  Proj.basicOpenIsoSpec (grading ε) (z ε) (coordinate_degree ε 2) (by decide : 0<1)
def mChartIso (ε : Bool) : (mOpen ε).toScheme≅Spec (CommRingCat.of (mChartRing ε)) :=
  Proj.basicOpenIsoSpec (grading ε) (m ε) (coordinate_degree ε 0) (by decide : 0<1)

end
end Z2Z4Rank6.GTorsionCoverProjective
