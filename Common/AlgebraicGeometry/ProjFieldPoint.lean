module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction

@[expose] public section

/-!
# Field-valued scheme points from homogeneous evaluations

A homogeneous coordinate evaluation which sends a positive-degree
coordinate to one defines a Proj point over the coefficient
field. This is the Proj universal construction in Mathlib.
-/

namespace AlgebraicGeometry.ProjFieldPoint
noncomputable section
open CategoryTheory
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable {k A : Type} [Field k] [CommRing A] [Algebra k A]
variable (𝒜 : ℕ → Submodule k A) [GradedAlgebra 𝒜]
variable [IsScalarTower k (𝒜 0) A]

abbrev Source (k : Type) [Field k] := Spec (CommRingCat.of k)

def structureMap : Proj 𝒜 ⟶ Source k :=
  Proj.toSpecZero 𝒜 ≫ Spec.map (CommRingCat.ofHom (algebraMap k (𝒜 0)))

def globalEvaluation (e : A →ₐ[k] k) : A →+* Γ(Source k, ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom.comp e.toRingHom

omit [IsScalarTower k (𝒜 0) A] in
theorem irrelevant_map_eq_top (e : A →ₐ[k] k) {n : ℕ} (hn : 0 < n)
    (r : A) (hr : r ∈ 𝒜 n) (he : e r = 1) :
    (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map (globalEvaluation e) = ⊤ := by
  have hmem : r ∈ (HomogeneousIdeal.irrelevant 𝒜).toIdeal :=
    HomogeneousIdeal.mem_irrelevant_of_mem 𝒜 hn hr
  apply (Ideal.eq_top_iff_one _).mpr
  have h := Ideal.mem_map_of_mem (globalEvaluation e) hmem
  have hm : globalEvaluation e r = 1 := by simp [globalEvaluation,he]
  rwa [hm] at h

def point (e : A →ₐ[k] k) {n : ℕ} (hn : 0 < n)
    (r : A) (hr : r ∈ 𝒜 n) (he : e r = 1) : Source k ⟶ Proj 𝒜 :=
  Proj.fromOfGlobalSections 𝒜 (globalEvaluation e)
    (irrelevant_map_eq_top 𝒜 e hn r hr he)

theorem point_over (e : A →ₐ[k] k) {n : ℕ} (hn : 0 < n)
    (r : A) (hr : r ∈ 𝒜 n) (he : e r = 1) :
    point 𝒜 e hn r hr he ≫ structureMap 𝒜 = 𝟙 (Source k) := by
  rw [point,structureMap,←Category.assoc,Proj.fromOfGlobalSections_toSpecZero,
    Category.assoc,←Spec.map_comp]
  have h : CommRingCat.ofHom (algebraMap k (𝒜 0)) ≫
      CommRingCat.ofHom ((globalEvaluation e).comp (algebraMap (𝒜 0) A)) =
      (Scheme.ΓSpecIso (CommRingCat.of k)).inv := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    change (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
      (e (algebraMap (𝒜 0) A (algebraMap k (𝒜 0) a))) = _
    rw [←IsScalarTower.algebraMap_apply,e.commutes]
    rfl
  rw [h]
  exact toSpecΓ_SpecMap_ΓSpecIso_inv _

end
end AlgebraicGeometry.ProjFieldPoint
