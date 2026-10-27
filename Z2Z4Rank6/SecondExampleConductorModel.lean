module

public import Z2Z4Rank6.SecondExampleRankSevenData
public import Z2Z4Rank6.Minimality
public import Common.Elliptic.SemistableConductor
public import Common.Elliptic.WeierstrassSchemeVariableChange

@[expose] public section

/-!
# A globally minimal semistable model of the printed second example

Jaswal, after Theorem 8.1(d), DOI 10.5281/zenodo.23437117. The
change x=4x', y=8y'+4x' gives the displayed integral equation below.
Its c4 and discriminant are coprime, proving local minimality at
every prime by the invariant-weight argument.
-/
namespace Z2Z4Rank6.SecondExampleConductor
noncomputable section
open AlgebraicGeometry CategoryTheory WeierstrassCurve
open Common.Elliptic.GeometricConductor

/-- The integral minimal equation, including its nonzero a1. -/
def integerModel : WeierstrassCurve ℤ :=
  ⟨1,31302730011424384680,0,1653253776102887599555230810531840000,0⟩

def rationalModel : WeierstrassCurve ℚ := integerModel.map (Int.castRingHom ℚ)
def modelChange : VariableChange ℚ := ⟨Units.mk0 2 (by norm_num),0,1,0⟩

theorem modelChange_eq : modelChange • SecondExampleRankSeven.curve=rationalModel := by
  ext <;> norm_num [modelChange,rationalModel,integerModel,SecondExampleRankSeven.curve,
    SecondExampleRankSeven.A,SecondExampleRankSeven.B,E,WeierstrassCurve.variableChange_def]

/-- Complete over-Q scheme isomorphism with the example E_(a,b). -/
def overIso : Over.mk (WeierstrassScheme.structureMap rationalModel) ≅
    Over.mk (WeierstrassScheme.structureMap SecondExampleRankSeven.curve) := by
  let e := WeierstrassScheme.VariableChange.overBaseIso SecondExampleRankSeven.curve modelChange
  have h : Over.mk (WeierstrassScheme.structureMap (modelChange • SecondExampleRankSeven.curve)) ≅
      Over.mk (WeierstrassScheme.structureMap SecondExampleRankSeven.curve) :=
    Over.isoMk e.val e.property
  exact eqToIso (congrArg (fun W : WeierstrassCurve ℚ=>
    Over.mk (WeierstrassScheme.structureMap W)) modelChange_eq.symm) ≪≫ h

theorem invariant_coprime : IsCoprime integerModel.c₄ integerModel.Δ := by
  norm_num [integerModel,WeierstrassCurve.c₄,WeierstrassCurve.Δ,
    WeierstrassCurve.b₂,WeierstrassCurve.b₄,WeierstrassCurve.b₆,WeierstrassCurve.b₈,
    Int.isCoprime_iff_gcd_eq_one]

theorem discriminant_ne_zero : integerModel.Δ≠0 := by
  norm_num [integerModel,WeierstrassCurve.Δ,WeierstrassCurve.b₂,
    WeierstrassCurve.b₄,WeierstrassCurve.b₆,WeierstrassCurve.b₈]

theorem local_minimal (p : ℕ) [Fact p.Prime] :
    IsMinimal (PadicInt p) (localEquation integerModel p) := by
  let V := integerModel.map (Int.castRingHom (PadicInt p))
  have hcop : IsCoprime V.c₄ V.Δ := by
    simpa only [V,WeierstrassCurve.map_c₄,WeierstrassCurve.map_Δ] using
      invariant_coprime.map (Int.castRingHom (PadicInt p))
  have hm := Minimality.baseChange_isMinimal_of_isCoprime (K:=Padic p) (PadicInt p) V hcop
  have he : V.baseChange (Padic p)=localEquation integerModel p := by
    ext <;> norm_num [V,integerModel,localEquation,WeierstrassCurve.baseChange]
    all_goals norm_cast
  rwa [he] at hm

theorem local_elliptic (p : ℕ) [Fact p.Prime] : (localEquation integerModel p).IsElliptic := by
  have hn : (integerModel.Δ : Padic p)≠0 := by exact_mod_cast discriminant_ne_zero
  exact ⟨isUnit_iff_ne_zero.mpr (by simpa [localEquation] using hn)⟩

theorem data (hModels : EllipticMinimalModelsTheorem) : Data integerModel :=
  dataOfMinimalEquation hModels integerModel discriminant_ne_zero local_minimal local_elliptic

def conductor (hModels : EllipticMinimalModelsTheorem) : ℕ := (data hModels).conductor

end
end Z2Z4Rank6.SecondExampleConductor
