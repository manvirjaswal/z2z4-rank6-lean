import Z2Z4Rank6.SurfaceComplexData
import Common.AlgebraicGeometry.ProjectiveLinePoints

/-! The nine distinct complex bad parameters of Lemma 3.1(b). -/
namespace Z2Z4Rank6.SurfaceBadParameters
noncomputable section
open AlgebraicGeometry CategoryTheory
open SurfaceComplexData SurfaceLocalInvariants
open scoped Classical

/-- Four I4 parameters, three I2 parameters, and two I1 parameters. -/
def parameter : Fin 9 → Option ℂ :=
  ![some 1,some 81,some 121,some 9801,some 99,some 0,
    some (quadraticRoot 0),some (quadraticRoot 1),none]
def order : Fin 9 → ℕ := ![4,4,4,4,2,1,2,2,1]

theorem parameter_injective : Function.Injective parameter := by
  have hn (i : Fin 2) : quadraticRoot i≠1 ∧ quadraticRoot i≠81 ∧
      quadraticRoot i≠121 ∧ quadraticRoot i≠9801 ∧ quadraticRoot i≠99 ∧ quadraticRoot i≠0 := by
    have h0 := quadratic_root_ne_rational_bad (quadraticRoot i) (quadraticRoot_root i) 0
    have h1 := quadratic_root_ne_rational_bad (quadraticRoot i) (quadraticRoot_root i) 1
    have h2 := quadratic_root_ne_rational_bad (quadraticRoot i) (quadraticRoot_root i) 2
    have h3 := quadratic_root_ne_rational_bad (quadraticRoot i) (quadraticRoot_root i) 3
    have h4 := quadratic_root_ne_rational_bad (quadraticRoot i) (quadraticRoot_root i) 4
    have h5 := quadratic_root_ne_rational_bad (quadraticRoot i) (quadraticRoot_root i) 5
    simpa [rationalBadParameter] using
      ⟨h0,h1,h2,h3,h4,h5⟩
  have hn0 := hn 0
  have hn1 := hn 1
  have hq : quadraticRoot 0≠quadraticRoot 1 := by
    intro h
    have he := quadraticRoot_injective h
    norm_num at he
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [parameter]

def support : Finset (Option ℂ) := Finset.univ.image parameter

theorem support_card : support.card=9 := by
  rw [support,Finset.card_image_of_injective _ parameter_injective]
  simp

theorem orders_sum : (∑ i : Fin 9,order i)=24 := by norm_num [order,Fin.sum_univ_succ]

def point (i : Fin 9) := ProjectiveLine.parameterPoint ℂ (parameter i)

theorem point_injective : Function.Injective point :=
  (ProjectiveLine.parameterPoint_injective ℂ).comp parameter_injective

theorem none_mem_support : (none : Option ℂ)∈support :=
  Finset.mem_image.mpr ⟨8,Finset.mem_univ _,rfl⟩

theorem rational_mem_support (i : Fin 6) :
    some (rationalBadParameter (K:=ℂ) i)∈support := by
  fin_cases i
  · exact Finset.mem_image.mpr ⟨0,Finset.mem_univ _,rfl⟩
  · exact Finset.mem_image.mpr ⟨1,Finset.mem_univ _,rfl⟩
  · exact Finset.mem_image.mpr ⟨2,Finset.mem_univ _,rfl⟩
  · exact Finset.mem_image.mpr ⟨3,Finset.mem_univ _,rfl⟩
  · exact Finset.mem_image.mpr ⟨4,Finset.mem_univ _,rfl⟩
  · exact Finset.mem_image.mpr ⟨5,Finset.mem_univ _,rfl⟩

theorem quadratic_mem_support (i : Fin 2) : some (quadraticRoot i)∈support := by
  fin_cases i
  · exact Finset.mem_image.mpr ⟨6,Finset.mem_univ _,rfl⟩
  · exact Finset.mem_image.mpr ⟨7,Finset.mem_univ _,rfl⟩

end
end Z2Z4Rank6.SurfaceBadParameters
