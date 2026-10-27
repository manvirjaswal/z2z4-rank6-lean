module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction

@[expose] public section

/-!
# Rational scheme points from homogeneous coordinate evaluations

A rational evaluation of a graded coordinate ring defines a point of
Proj whenever a homogeneous element of positive degree evaluates to one.
This is Mathlib's Proj construction from global sections, with its
structure-map compatibility proved.
-/

namespace AlgebraicGeometry.ProjRationalPoint
noncomputable section
open CategoryTheory
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable {A : Type} [CommRing A] [Algebra ℚ A]
variable (𝒜 : ℕ → Submodule ℚ A) [GradedAlgebra 𝒜]

abbrev Source := Spec (CommRingCat.of ℚ)
def structureMap : Proj 𝒜 ⟶ Source :=
  Proj.toSpecZero 𝒜 ≫ Spec.map (CommRingCat.ofHom (algebraMap ℚ (𝒜 0)))

def globalEvaluation (e : A →ₐ[ℚ] ℚ) : A →+* Γ(Source, ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of ℚ)).inv.hom.comp e.toRingHom

theorem irrelevant_map_eq_top (e : A →ₐ[ℚ] ℚ) {n : ℕ} (hn : 0 < n)
    (r : A) (hr : r ∈ 𝒜 n) (he : e r = 1) :
    (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map (globalEvaluation e) = ⊤ := by
  have hmem : r ∈ (HomogeneousIdeal.irrelevant 𝒜).toIdeal := by
    exact HomogeneousIdeal.mem_irrelevant_of_mem 𝒜 hn hr
  apply (Ideal.eq_top_iff_one _).mpr
  have h := Ideal.mem_map_of_mem (globalEvaluation e) hmem
  have hm : globalEvaluation e r = 1 := by simp [globalEvaluation,he]
  rwa [hm] at h

def point (e : A →ₐ[ℚ] ℚ) {n : ℕ} (hn : 0 < n)
    (r : A) (hr : r ∈ 𝒜 n) (he : e r = 1) : Source ⟶ Proj 𝒜 :=
  Proj.fromOfGlobalSections 𝒜 (globalEvaluation e)
    (irrelevant_map_eq_top 𝒜 e hn r hr he)

theorem point_over (e : A →ₐ[ℚ] ℚ) {n : ℕ} (hn : 0 < n)
    (r : A) (hr : r ∈ 𝒜 n) (he : e r = 1) :
    point 𝒜 e hn r hr he ≫ structureMap 𝒜 = 𝟙 Source := by
  rw [point,structureMap,← Category.assoc,Proj.fromOfGlobalSections_toSpecZero,
    Category.assoc,← Spec.map_comp]
  have h : CommRingCat.ofHom (algebraMap ℚ (𝒜 0)) ≫
      CommRingCat.ofHom ((globalEvaluation e).comp (algebraMap (𝒜 0) A)) =
      (Scheme.ΓSpecIso (CommRingCat.of ℚ)).inv := by
    apply CommRingCat.hom_ext
    exact RingHom.ext_rat _ _
  rw [h]
  exact toSpecΓ_SpecMap_ΓSpecIso_inv _

end
end AlgebraicGeometry.ProjRationalPoint
