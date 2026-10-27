import Common.AlgebraicGeometry.ProjectiveLine
import Common.AlgebraicGeometry.ProjGradedIsomorphism
import Mathlib.RingTheory.MvPolynomial.Ideal

/-!
# The coefficient map of projective lines

The map P1_K -> P1_k is the contravariant Proj map of the coefficient
homomorphism k[U,V] -> K[U,V].
-/
namespace AlgebraicGeometry.ProjectiveLine
noncomputable section
open CategoryTheory MvPolynomial HomogeneousIdeal
set_option backward.isDefEq.respectTransparency false
variable (k K : Type) [Field k] [Field K] [Algebra k K]

def coefficientHom : grading k →+*ᵍ grading K where
  toRingHom := MvPolynomial.map (algebraMap k K)
  map_mem := by
    intro n p hp
    exact MvPolynomial.IsHomogeneous.map hp (algebraMap k K)

theorem irrelevant_le_coefficientHom :
    irrelevant (grading K) ≤
      (irrelevant (grading k)).map (coefficientHom k K) := by
  apply (irrelevant_le (grading K)).mpr
  intro n hn p hp
  have hp0 : p.coeff 0=0 := by
    exact hp.coeff_eq_zero (by simpa using hn.ne)
  have hspan : p∈Ideal.span (Set.range (X : Fin 2 → Ring K)) := by
    rw [←Set.image_univ,MvPolynomial.mem_ideal_span_X_image]
    intro m hm
    have hm0 : m≠0 := by
      intro h
      subst m
      simp [MvPolynomial.mem_support_iff,hp0] at hm
    obtain ⟨i,hi⟩ : ∃ i,m i≠0 := by
      by_contra! h
      apply hm0
      ext i
      exact h i
    exact ⟨i,Set.mem_univ i,hi⟩
  apply Ideal.span_le.mpr ?_ hspan
  rintro _ ⟨i,rfl⟩
  have h := Ideal.mem_map_of_mem (coefficientHom k K)
    (mem_irrelevant_of_mem (grading k) (by decide : 0<1) (coordinate_degree k i))
  simpa [coefficientHom,coordinate] using h

def coefficientMap : scheme K ⟶ scheme k :=
  Proj.map (coefficientHom k K) (irrelevant_le_coefficientHom k K)

theorem coefficientMap_over :
    coefficientMap k K≫structureMap k =
      structureMap K≫Spec.map (CommRingCat.ofHom (algebraMap k K)) := by
  dsimp only [coefficientMap,structureMap,ProjFieldPoint.structureMap]
  rw [←Category.assoc,Proj.map_toSpecZero,Category.assoc,←Spec.map_comp,Category.assoc,
    ←Spec.map_comp]
  congr 2
  apply CommRingCat.hom_ext
  ext a
  simp [coefficientHom]

end
end AlgebraicGeometry.ProjectiveLine
