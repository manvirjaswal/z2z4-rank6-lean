import Z2Z4Rank6.PrintedModelConductorData
import Common.Elliptic.MulhollandModelTheorems

/-!
# Geometric component counts for the printed equations

All coefficient tests are proved. Published Mulholland component formulas
are applied only after constructing the translated generic-fiber
scheme isomorphism and transporting minimal regular proper models.
The transported models have the same total scheme and geometric special
fiber, so their component counts agree by definition.
-/

namespace Z2Z4Rank6.PrintedModelConductorComponents
noncomputable section
open AlgebraicGeometry CategoryTheory
open Common.Elliptic GeometricConductor MulhollandTwoAdic MulhollandModelTheorems
open PrintedModelMinimality PrintedModelRootTranslations PrintedModelConductorData
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

def translatedModel (i : Fin 3) (D : Data (integerModel i)) (p : ℕ) [Fact p.Prime] :
    LocalModel (equation (translatedA i) (translatedB i)) p :=
  (D.model p).transport (translatedIso i p).symm (translatedIso_inv_over i p)

theorem translatedModel_minimal (i : Fin 3) (D : Data (integerModel i))
    (p : ℕ) [Fact p.Prime] : (translatedModel i D p).IsMinimal :=
  RegularProperModel.transport_isMinimal (D.model p) (D.model_minimal p)
    (translatedIso i p).symm (translatedIso_inv_over i p)

theorem translatedModel_componentCount (i : Fin 3) (D : Data (integerModel i))
    (p : ℕ) [Fact p.Prime] :
    (translatedModel i D p).geometricComponentCount = (D.model p).geometricComponentCount :=
  RegularProperModel.transport_geometricComponentCount (D.model p)
    (translatedIso i p).symm (translatedIso_inv_over i p)

theorem translated_discriminant_ne_zero (i : Fin 3) :
    (equation (translatedA i) (translatedB i)).Δ ≠ 0 := by
  rw [translated_discriminant]
  exact PrintedModelConductorData.discriminant_ne_zero i

theorem translated_coprime (i : Fin 3) : IsCoprime (translatedA i) (translatedB i) := by
  fin_cases i <;> norm_num [translatedA,translatedB,Int.isCoprime_iff_gcd_eq_one]

theorem componentCount_two (h21 : Theorem21Components) (i : Fin 3)
    (D : Data (integerModel i)) : (D.model 2).geometricComponentCount = starIndex i+5 := by
  have h := h21 (translatedA i) (translatedB i) (starIndex i)
    (translated_discriminant_ne_zero i) (mulholland_row i)
    (translatedModel i D 2) (translatedModel_minimal i D 2)
  rwa [translatedModel_componentCount] at h

theorem componentCount_odd (hOdd : Theorems23And24SemistableComponents)
    (i : Fin 3) (D : Data (integerModel i)) (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    (D.model p).geometricComponentCount =
      if p ∣ (integerModel i).Δ.natAbs then padicValNat p (integerModel i).Δ.natAbs else 1 := by
  have h := hOdd p hp (translatedA i) (translatedB i) (translated_discriminant_ne_zero i)
    (translated_coprime i) (translatedModel i D p) (translatedModel_minimal i D p)
  rwa [translatedModel_componentCount,translated_discriminant] at h

end
end Z2Z4Rank6.PrintedModelConductorComponents
