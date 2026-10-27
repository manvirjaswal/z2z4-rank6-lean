import Common.AlgebraicGeometry.ProjFieldPoint

/-!
# Points of Proj valued in an extension field

Homogeneous evaluation over k with values in an extension field K.
The resulting scheme map retains its compatibility with Spec K -> Spec k.
This is the Proj construction from global sections.
-/
namespace AlgebraicGeometry.ProjValuedPoint
noncomputable section
open CategoryTheory
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {k K A : Type} [Field k] [Field K] [Algebra k K] [CommRing A] [Algebra k A]
variable (𝒜 : ℕ → Submodule k A) [GradedAlgebra 𝒜]
variable [IsScalarTower k (𝒜 0) A]

abbrev Source (K : Type) [Field K] := Spec (CommRingCat.of K)
def globalEvaluation (e : A →ₐ[k] K) : A →+* Γ(Source K, ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom.comp e.toRingHom

omit [IsScalarTower k (𝒜 0) A] in
theorem irrelevant_map_eq_top (e : A →ₐ[k] K) {n : ℕ} (hn : 0<n)
    (r : A) (hr : r∈𝒜 n) (he : e r=1) :
    (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map (globalEvaluation e)=⊤ := by
  apply (Ideal.eq_top_iff_one _).mpr
  have h := Ideal.mem_map_of_mem (globalEvaluation e)
    (HomogeneousIdeal.mem_irrelevant_of_mem 𝒜 hn hr)
  have hm : globalEvaluation e r=1 := by simp [globalEvaluation,he]
  rwa [hm] at h

def point (e : A →ₐ[k] K) {n : ℕ} (hn : 0<n)
    (r : A) (hr : r∈𝒜 n) (he : e r=1) : Source K ⟶ Proj 𝒜 :=
  Proj.fromOfGlobalSections 𝒜 (globalEvaluation e) (irrelevant_map_eq_top 𝒜 e hn r hr he)

def sourcePoint : Source K := ⟨⊥,inferInstance⟩

omit [IsScalarTower k (𝒜 0) A] in
theorem point_mem_basicOpen (e : A →ₐ[k] K) {n : ℕ} (hn : 0<n)
    (r : A) (hr : r∈𝒜 n) (he : e r=1) {m : ℕ} (hm : 0<m)
    (x : A) (hx : x∈𝒜 m) :
    point 𝒜 e hn r hr he sourcePoint∈Proj.basicOpen 𝒜 x ↔ e x≠0 := by
  change sourcePoint∈point 𝒜 e hn r hr he ⁻¹ᵁ Proj.basicOpen 𝒜 x ↔ _
  rw [point,Proj.fromOfGlobalSections_preimage_basicOpen _ _ _ hm hx]
  change sourcePoint∈(Spec (CommRingCat.of K)).basicOpen
    ((Scheme.ΓSpecIso (CommRingCat.of K)).inv (e x)) ↔ _
  rw [basicOpen_eq_of_affine]
  change e x∉(⊥ : Ideal K) ↔ _
  simp

theorem point_over (e : A →ₐ[k] K) {n : ℕ} (hn : 0<n)
    (r : A) (hr : r∈𝒜 n) (he : e r=1) :
    point 𝒜 e hn r hr he ≫ ProjFieldPoint.structureMap 𝒜=
      Spec.map (CommRingCat.ofHom (algebraMap k K)) := by
  rw [point,ProjFieldPoint.structureMap,←Category.assoc,Proj.fromOfGlobalSections_toSpecZero,
    Category.assoc,←Spec.map_comp]
  have h : CommRingCat.ofHom (algebraMap k (𝒜 0)) ≫
      CommRingCat.ofHom ((globalEvaluation e).comp (algebraMap (𝒜 0) A))=
      CommRingCat.ofHom (algebraMap k K) ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).inv := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    change (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
      (e (algebraMap (𝒜 0) A (algebraMap k (𝒜 0) a))) = _
    rw [←IsScalarTower.algebraMap_apply,e.commutes]
    rfl
  rw [h,Spec.map_comp,←Category.assoc,toSpecΓ_SpecMap_ΓSpecIso_inv,Category.id_comp]

end
end AlgebraicGeometry.ProjValuedPoint
