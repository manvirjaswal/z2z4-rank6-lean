import Common.AlgebraicGeometry.ProjGradedIsomorphism

/-! Maps of Proj charts with an explicit denominator identity. -/
namespace AlgebraicGeometry.Proj
noncomputable section
open CategoryTheory HomogeneousLocalization
set_option backward.isDefEq.respectTransparency false
universe u
variable {A B σ τ : Type u} [CommRing A] [CommRing B]
  [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]

def chartRingHom (f : 𝒜 →+*ᵍ ℬ) (r : A) (s : B) (h : f r=s) :
    Away 𝒜 r →+* Away ℬ s := h ▸ Away.map f r

theorem chartRingHom_fromZero (f : 𝒜 →+*ᵍ ℬ) (r : A) (s : B) (h : f r=s)
    (a : 𝒜 0) :
    chartRingHom f r s h (fromZeroRingHom 𝒜 (Submonoid.powers r) a)=
      fromZeroRingHom ℬ (Submonoid.powers s) (f.gradedZeroRingHom a) := by
  subst s
  apply HomogeneousLocalization.val_injective
  simp [chartRingHom,HomogeneousLocalization.Away.map,HomogeneousLocalization.fromZeroRingHom,
    HomogeneousLocalization.map_mk,HomogeneousLocalization.val_mk]

theorem chartRingHom_mk (f : 𝒜 →+*ᵍ ℬ) (r : A) (s : B) (h : f r=s)
    {d : ℕ} (hr : r∈𝒜 d) (hs : s∈ℬ d) (n : ℕ) (a : A) (ha : a∈𝒜 (n • d)) :
    chartRingHom f r s h (Away.mk 𝒜 hr n a ha)=
      Away.mk ℬ hs n (f a) (f.map_mem ha) := by
  subst s
  exact Away.map_mk f r hr n a ha

theorem chartRingHom_awayι (f : 𝒜 →+*ᵍ ℬ)
    (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f)
    (r : A) (s : B) (h : f r=s) {d : ℕ} (hr : r∈𝒜 d) (hs : s∈ℬ d) (hd : 0<d) :
    awayι ℬ s hs hd ≫ map f hf=
      Spec.map (CommRingCat.ofHom (chartRingHom f r s h)) ≫ awayι 𝒜 r hr hd := by
  subst s
  exact awayι_comp_map f hf hd r hr

end
end AlgebraicGeometry.Proj
