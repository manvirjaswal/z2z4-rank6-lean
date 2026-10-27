import Z2Z4Rank6.AffineCoverModuleQuotient

/-! A commuting square of restrictions and two linear equivalences
transports restriction images. This is generic module algebra. -/
namespace Z2Z4Rank6.RestrictionRangeTransport
noncomputable section
variable {A B V W : Type*} [AddCommGroup A] [Module ℚ A]
  [AddCommGroup B] [Module ℚ B] [AddCommGroup V] [Module ℚ V]
  [AddCommGroup W] [Module ℚ W]

theorem map_range_of_intertwining (f : A→ₗ[ℚ]V) (g : B→ₗ[ℚ]W)
    (a : A≃ₗ[ℚ]B) (e : V≃ₗ[ℚ]W) (h : e.toLinearMap.comp f=g.comp a.toLinearMap) :
    (LinearMap.range f).map e.toLinearMap=LinearMap.range g := by
  rw [←LinearMap.range_comp,h]
  ext w
  constructor
  · rintro ⟨x,rfl⟩
    exact ⟨a x,rfl⟩
  · rintro ⟨x,rfl⟩
    refine ⟨a.symm x,?_⟩
    change g (a (a.symm x))=g x
    rw [a.apply_symm_apply]
end
end Z2Z4Rank6.RestrictionRangeTransport
