module

public import Z2Z4Rank6.ProjectiveBaseSchemeCharts

@[expose] public section

/-! Coordinate-ratio generation determines ring maps from a chart. -/
namespace Z2Z4Rank6.ProjectiveBaseSchemeCharts
noncomputable section

theorem chartRingHom_ext {S : Type*} [CommRing S] (k : Fin 4)
    (f g : ChartRing k →+* S) (h : ∀i,f (ratio k i)=g (ratio k i)) : f=g := by
  let : Algebra ℚ S := (f.comp (algebraMap ℚ (ChartRing k))).toAlgebra
  have he : rationalAlgHom f=rationalAlgHom g := chartAlgHom_ext k _ _ h
  exact congrArg AlgHom.toRingHom he

end
end Z2Z4Rank6.ProjectiveBaseSchemeCharts
