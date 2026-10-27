import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.LinearAlgebra.Finsupp.Supported
import Mathlib.LinearAlgebra.Finsupp.Pi
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Tactic

/-!
# The Laurent coefficient quotient in the two-chart genus calculation

Algebraic component of Jaswal Section 3 and Lemma 4.1(a),
DOI 10.5281/zenodo.23437117. Four Laurent components use basis 1,u,v,uv.
The first chart allows all nonnegative exponents. The second allows
exponents at most 0,−1,−1,−2 respectively, corresponding to 1,u/m,v/m,uv/m².
Their quotient has precisely the uv/m coefficient left over.

This file proves that the coefficient-module quotient is one-dimensional.
The chart restriction and structure-sheaf comparisons are proved in separate
modules.
-/

namespace Z2Z4Rank6.LaurentCechQuotient
noncomputable section
open scoped Classical

abbrev Index := Fin 4×ℤ
abbrev Coefficients := Index→₀ℚ
abbrev FourLaurent := Fin 4→LaurentPolynomial ℚ

def weights : Fin 4→ℤ := ![0,1,1,2]
def missing : Index := (3,-1)
def positiveIndices : Set Index := {p | 0≤p.2}
def negativeIndices : Set Index := {p | p.2≤-weights p.1}

/-- Four Laurent polynomials, with their finite coefficient support. -/
def coordinatesEquiv : Coefficients≃ₗ[ℚ]FourLaurent :=
  ((Finsupp.curryLinearEquiv ℚ).trans
    (Finsupp.linearEquivFunOnFinite ℚ (ℤ→₀ℚ) (Fin 4))).trans
      (LinearEquiv.piCongrRight fun _ : Fin 4 =>
        (AddMonoidAlgebra.coeffLinearEquiv ℚ : LaurentPolynomial ℚ≃ₗ[ℚ](ℤ→₀ℚ)).symm)

@[simp] theorem coordinatesEquiv_coeff (f : Coefficients) (i : Fin 4) (n : ℤ) :
    (coordinatesEquiv f i).coeff n=f (i,n) := rfl

def positivePart : Submodule ℚ Coefficients := Finsupp.supported ℚ ℚ positiveIndices
def negativePart : Submodule ℚ Coefficients := Finsupp.supported ℚ ℚ negativeIndices
def boundary : Submodule ℚ Coefficients := positivePart⊔negativePart

/-- The coefficient conditions are exactly the monomial spans. -/
theorem positivePart_eq_span : positivePart=
    Submodule.span ℚ ((fun p : Index => Finsupp.single p (1:ℚ)) '' positiveIndices) :=
  Finsupp.supported_eq_span_single ℚ positiveIndices

theorem negativePart_eq_span : negativePart=
    Submodule.span ℚ ((fun p : Index => Finsupp.single p (1:ℚ)) '' negativeIndices) :=
  Finsupp.supported_eq_span_single ℚ negativeIndices

/-- Only component uv at exponent−1 is excluded by both chart spans. -/
theorem allowed_union : positiveIndices∪negativeIndices={p : Index | p≠missing} := by
  ext p
  obtain ⟨i,n⟩ := p
  fin_cases i <;> simp [positiveIndices,negativeIndices,weights,missing] <;> omega

def residue : Coefficients→ₗ[ℚ]ℚ := Finsupp.lapply missing

@[simp] theorem residue_apply (f : Coefficients) : residue f=f (3,-1) := rfl

theorem residue_surjective : Function.Surjective residue := by
  intro q
  exact ⟨Finsupp.single missing q,by simp [residue]⟩

/-- The sum of the two coefficient spans is precisely the kernel
of the uv/m coefficient functional. -/
theorem boundary_eq_ker : boundary=LinearMap.ker residue := by
  rw [boundary,positivePart,negativePart,←Finsupp.supported_union,allowed_union]
  ext f
  rw [Finsupp.mem_supported',LinearMap.mem_ker]
  change (∀p : Index,¬p≠missing→f p=0)↔f missing=0
  simp only [not_not]
  constructor
  · intro h
    exact h missing rfl
  · intro h p hp
    subst p
    exact h

def quotientEquiv : (Coefficients⧸boundary)≃ₗ[ℚ]ℚ :=
  (Submodule.quotEquivOfEq _ _ boundary_eq_ker).trans
    (residue.quotKerEquivOfSurjective residue_surjective)

theorem finrank_quotient : Module.finrank ℚ (Coefficients⧸boundary)=1 := by
  simpa using quotientEquiv.finrank_eq

/-- The discarded part of every coefficient vector belongs to the
sum of chart spans; this also identifies the unique remaining generator. -/
theorem normal_form (f : Coefficients) :
    f-residue f • Finsupp.single missing (1:ℚ)∈boundary := by
  rw [boundary_eq_ker,LinearMap.mem_ker]
  simp [residue,map_sub]

def positiveFour : Submodule ℚ FourLaurent := positivePart.map coordinatesEquiv.toLinearMap
def negativeFour : Submodule ℚ FourLaurent := negativePart.map coordinatesEquiv.toLinearMap
def boundaryFour : Submodule ℚ FourLaurent := positiveFour⊔negativeFour
def residueFour : FourLaurent→ₗ[ℚ]ℚ := residue.comp coordinatesEquiv.symm.toLinearMap

@[simp] theorem residueFour_apply (f : FourLaurent) : residueFour f=(f 3).coeff (-1) := by
  change (coordinatesEquiv.symm f) (3,-1)=(f 3).coeff (-1)
  exact (coordinatesEquiv_coeff (coordinatesEquiv.symm f) 3 (-1)).symm.trans
    (congrArg (fun x : FourLaurent => (x 3).coeff (-1)) (coordinatesEquiv.apply_symm_apply f))

theorem boundaryFour_eq_map : boundaryFour=boundary.map coordinatesEquiv.toLinearMap := by
  rw [boundaryFour,positiveFour,negativeFour,boundary,Submodule.map_sup]

theorem boundaryFour_eq_ker : boundaryFour=LinearMap.ker residueFour := by
  rw [boundaryFour_eq_map]
  ext f
  rw [Submodule.mem_map,LinearMap.mem_ker]
  constructor
  · rintro ⟨g,hg,rfl⟩
    change residue (coordinatesEquiv.symm (coordinatesEquiv g))=0
    rw [coordinatesEquiv.symm_apply_apply]
    exact (LinearMap.mem_ker.mp (boundary_eq_ker ▸ hg))
  · intro hf
    refine ⟨coordinatesEquiv.symm f,?_,coordinatesEquiv.apply_symm_apply f⟩
    rw [boundary_eq_ker,LinearMap.mem_ker]
    exact hf

theorem residueFour_surjective : Function.Surjective residueFour := by
  intro q
  obtain ⟨g,hg⟩ := residue_surjective q
  refine ⟨coordinatesEquiv g,?_⟩
  change residue (coordinatesEquiv.symm (coordinatesEquiv g))=q
  simpa only [coordinatesEquiv.symm_apply_apply] using hg

/-- The quotient of the four Laurent-polynomial module by the
two specified chart coefficient spans is a one-dimensional rational space. -/
def quotientFourEquiv : (FourLaurent⧸boundaryFour)≃ₗ[ℚ]ℚ :=
  (Submodule.quotEquivOfEq _ _ boundaryFour_eq_ker).trans
    (residueFour.quotKerEquivOfSurjective residueFour_surjective)

theorem finrank_four_quotient : Module.finrank ℚ (FourLaurent⧸boundaryFour)=1 := by
  simpa using quotientFourEquiv.finrank_eq

end
end Z2Z4Rank6.LaurentCechQuotient
