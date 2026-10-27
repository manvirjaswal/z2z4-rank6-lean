import Common.Elliptic.GeometricConductor
import Common.Elliptic.WeierstrassSchemeVariableChange
import Z2Z4Rank6.PrintedModelDiscriminantValues
import Z2Z4Rank6.PrintedModelRootTranslations

/-!
# Geometric conductor data for the printed equations

The integral equations, local minimality and exact discriminants were
proved separately. The new hypothesis supplies minimal regular proper models of arbitrary elliptic
curves over p-adic fields (Conrad, Minimal models
for elliptic curves, Theorem 3.10 p. 8). The conductor is the geometric
definition, using those models' geometric special-fiber components.
-/

namespace Z2Z4Rank6.PrintedModelConductorData
noncomputable section
open AlgebraicGeometry CategoryTheory WeierstrassCurve
open Common.Elliptic Common.Elliptic.GeometricConductor
open PrintedModelMinimality PrintedModelRootTranslations
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

theorem discriminant_ne_zero (i : Fin 3) : (integerModel i).Δ ≠ 0 := by
  rw [PrintedModelReduction.discriminant_factorization]
  fin_cases i <;> norm_num [PrintedModelReduction.discriminantProduct]

theorem localEquation_eq (i : Fin 3) (p : ℕ) [Fact p.Prime] :
    localEquation (integerModel i) p = PrintedModelMinimality.localModel i p := by
  ext <;> simp [localEquation,PrintedModelMinimality.localModel,WeierstrassCurve.baseChange]

theorem local_minimal (i : Fin 3) (p : ℕ) [Fact p.Prime] :
    IsMinimal (PadicInt p) (localEquation (integerModel i) p) := by
  rw [localEquation_eq]
  exact PrintedModelReduction.model_minimal i p

theorem local_elliptic (i : Fin 3) (p : ℕ) [Fact p.Prime] :
    (localEquation (integerModel i) p).IsElliptic := by
  have hn : ((integerModel i).Δ : Padic p) ≠ 0 := by
    exact_mod_cast discriminant_ne_zero i
  exact ⟨isUnit_iff_ne_zero.mpr (by simpa [localEquation] using hn)⟩

theorem data (hModels : EllipticMinimalModelsTheorem) (i : Fin 3) : Data (integerModel i) :=
  dataOfMinimalEquation hModels (integerModel i) (discriminant_ne_zero i)
    (local_minimal i) (local_elliptic i)

def conductor (hModels : EllipticMinimalModelsTheorem) (i : Fin 3) : ℕ :=
  (data hModels i).conductor

def translatedLocalEquation (i : Fin 3) (p : ℕ) [Fact p.Prime] : WeierstrassCurve (Padic p) :=
  localEquation (Common.Elliptic.MulhollandTwoAdic.equation (translatedA i) (translatedB i)) p

def localTranslation (i : Fin 3) (p : ℕ) [Fact p.Prime] : VariableChange (Padic p) :=
  (Common.Elliptic.MulhollandTwoAdic.translation (root i)).map (Int.castRingHom (Padic p))

theorem localTranslation_eq (i : Fin 3) (p : ℕ) [Fact p.Prime] :
    localTranslation i p • localEquation (integerModel i) p = translatedLocalEquation i p := by
  rw [localTranslation,localEquation,WeierstrassCurve.map_variableChange,translation_eq]
  rfl

/-- A scheme isomorphism over the p-adic field. -/
def translatedOverIso (i : Fin 3) (p : ℕ) [Fact p.Prime] :
    Over.mk (WeierstrassScheme.structureMap (translatedLocalEquation i p)) ≅
      Over.mk (WeierstrassScheme.structureMap (localEquation (integerModel i) p)) := by
  let e := WeierstrassScheme.VariableChange.overBaseIso
    (localEquation (integerModel i) p) (localTranslation i p)
  have h : Over.mk (WeierstrassScheme.structureMap
      (localTranslation i p • localEquation (integerModel i) p)) ≅
      Over.mk (WeierstrassScheme.structureMap (localEquation (integerModel i) p)) :=
    Over.isoMk e.val e.property
  exact eqToIso (congrArg (fun W : WeierstrassCurve (Padic p) =>
    Over.mk (WeierstrassScheme.structureMap W)) (localTranslation_eq i p).symm) ≪≫ h

def translatedIso (i : Fin 3) (p : ℕ) [Fact p.Prime] :=
  (Over.forget _).mapIso (translatedOverIso i p)

theorem translatedIso_inv_over (i : Fin 3) (p : ℕ) [Fact p.Prime] :
    (translatedIso i p).inv ≫ WeierstrassScheme.structureMap (translatedLocalEquation i p) =
      WeierstrassScheme.structureMap (localEquation (integerModel i) p) :=
  (translatedOverIso i p).inv.w

end
end Z2Z4Rank6.PrintedModelConductorData
