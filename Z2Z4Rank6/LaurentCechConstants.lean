module

public import Z2Z4Rank6.LaurentCechQuotient

@[expose] public section

/-!
# Constants in the two-chart Laurent intersection

Algebraic component of Jaswal, Lemma 4.1(a), DOI 10.5281/zenodo.23437117.
The intersection of the two chart coefficient submodules consists exactly
of constants in the component 1. This is a rational linear equivalence. The global-section
identification
uses the sheaf-gluing and projective-base global-section modules.
-/

namespace Z2Z4Rank6.LaurentCechConstants
noncomputable section
open LaurentCechQuotient
open scoped Classical

def constantIndex : Index := (0,0)

theorem allowed_intersection : positiveIndices∩negativeIndices={constantIndex} := by
  ext p
  obtain ⟨i,n⟩ := p
  fin_cases i <;> simp [positiveIndices,negativeIndices,weights,constantIndex] <;> omega

theorem intersection_coefficients :
    positivePart⊓negativePart=Finsupp.supported ℚ ℚ {constantIndex} := by
  rw [positivePart,negativePart,←Finsupp.supported_inter,allowed_intersection]

theorem coefficient_normal_form (f : Coefficients) (hf : f∈positivePart⊓negativePart) :
    f=Finsupp.single constantIndex (f constantIndex) := by
  rw [intersection_coefficients,Finsupp.mem_supported'] at hf
  ext p
  by_cases hp : p=constantIndex
  · subst p
    simp
  · have hz : f p=0 := hf p (by simpa using hp)
    simp [hp,hz]

def constantFour : ℚ→ₗ[ℚ]FourLaurent :=
  coordinatesEquiv.toLinearMap.comp (Finsupp.lsingle constantIndex)

@[simp] theorem constantFour_coeff (q : ℚ) (i : Fin 4) (n : ℤ) :
    (constantFour q i).coeff n=Finsupp.single constantIndex q (i,n) := rfl

theorem constantFour_mem (q : ℚ) : constantFour q∈positiveFour⊓negativeFour := by
  constructor
  · exact ⟨Finsupp.single constantIndex q,
      Finsupp.single_mem_supported ℚ q (by simp [positiveIndices,constantIndex]),rfl⟩
  · exact ⟨Finsupp.single constantIndex q,
      Finsupp.single_mem_supported ℚ q (by simp [negativeIndices,constantIndex,weights]),rfl⟩

theorem four_normal_form (f : FourLaurent) (hf : f∈positiveFour⊓negativeFour) :
    f=constantFour ((f 0).coeff 0) := by
  obtain ⟨g,hgp,hgf⟩ := hf.1
  obtain ⟨h,hhn,hhf⟩ := hf.2
  have hgh : g=h := coordinatesEquiv.injective (hgf.trans hhf.symm)
  subst h
  have hn := coefficient_normal_form g ⟨hgp,hhn⟩
  have hc : (f 0).coeff 0=g constantIndex := by
    rw [←hgf]
    rfl
  rw [hc,←hgf]
  exact congrArg coordinatesEquiv hn

/-- The intersection of both Laurent chart coefficient submodules
is precisely the one-dimensional space of rational constants. -/
def intersectionFourEquiv : ↥(positiveFour⊓negativeFour)≃ₗ[ℚ]ℚ where
  toFun f := (f.1 0).coeff 0
  invFun q := ⟨constantFour q,constantFour_mem q⟩
  left_inv f := Subtype.ext (four_normal_form f.1 f.2).symm
  right_inv q := by simp [constantFour_coeff,constantIndex]
  map_add' f g := by simp
  map_smul' q f := by simp

theorem finrank_four_intersection : Module.finrank ℚ ↥(positiveFour⊓negativeFour)=1 := by
  simpa using intersectionFourEquiv.finrank_eq

end
end Z2Z4Rank6.LaurentCechConstants
