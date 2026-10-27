module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor

@[expose] public section

/-!
# Isomorphisms of Proj from inverse graded ring homomorphisms

The irrelevant-ideal conditions required by Mathlib's Proj functor follow
from graded inverses. All scheme maps and inverse identities are
Proj functor maps.
-/

namespace AlgebraicGeometry.Proj
noncomputable section
open HomogeneousIdeal CategoryTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {A B σ τ : Type u} [CommRing A] [CommRing B]
  [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]

theorem gradedHom_mem_irrelevant (f : 𝒜 →+*ᵍ ℬ) {x : A}
    (hx : x ∈ 𝒜₊) : f x ∈ ℬ₊ := by
  have hle : 𝒜₊ ≤ (ℬ₊).comap f := by
    apply (irrelevant_le 𝒜).mpr
    intro i hi x hx
    exact mem_irrelevant_of_mem ℬ hi (f.map_mem hx)
  exact hle hx

theorem irrelevant_le_map_of_inverse (f : 𝒜 →+*ᵍ ℬ) (g : ℬ →+*ᵍ 𝒜)
    (hfg : f.comp g = GradedRingHom.id ℬ) : ℬ₊ ≤ (𝒜₊).map f := by
  intro x hx
  have hgx : g x ∈ 𝒜₊ := gradedHom_mem_irrelevant g hx
  have hm : f (g x) ∈ (𝒜₊).map f := Ideal.mem_map_of_mem f hgx
  have he : f (g x) = x := DFunLike.congr_fun hfg x
  rwa [he] at hm

/-- Projective-scheme isomorphism induced by inverse graded maps.
Its direction is contravariant in the graded ring maps. -/
def isoOfInverse (f : 𝒜 →+*ᵍ ℬ) (g : ℬ →+*ᵍ 𝒜)
    (hgf : g.comp f = GradedRingHom.id 𝒜)
    (hfg : f.comp g = GradedRingHom.id ℬ) : Proj ℬ ≅ Proj 𝒜 where
  hom := map f (irrelevant_le_map_of_inverse f g hfg)
  inv := map g (irrelevant_le_map_of_inverse g f hgf)
  hom_inv_id := by
    rw [←map_comp]
    simp only [hfg, map_id]
  inv_hom_id := by
    rw [←map_comp]
    simp only [hgf, map_id]

/-- The Proj map is compatible with the induced map of degree-zero rings. -/
theorem map_toSpecZero (f : 𝒜 →+*ᵍ ℬ) (hf : ℬ₊ ≤ (𝒜₊).map f) :
    map f hf ≫ toSpecZero 𝒜 =
      toSpecZero ℬ ≫ Spec.map (CommRingCat.ofHom f.gradedZeroRingHom) := by
  refine (mapAffineOpenCover f hf).openCover.hom_ext _ _ fun s => ?_
  simp only [Scheme.AffineOpenCover.openCover_f, mapAffineOpenCover_f]
  rw [awayι_comp_map_assoc f hf s.1.2 s.2.1 s.2.2]
  simp only [awayι_toSpecZero, ←Category.assoc, ←Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  ext x
  simp [HomogeneousLocalization.fromZeroRingHom, HomogeneousLocalization.Away.map,
    HomogeneousLocalization.map_mk]

end
end AlgebraicGeometry.Proj
