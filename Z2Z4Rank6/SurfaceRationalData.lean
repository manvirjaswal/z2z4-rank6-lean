module

public import Z2Z4Rank6.SurfaceComplexData
public import Common.Elliptic.SurfaceConstantExtension

@[expose] public section

/-!
# Rational generic equation and its complex coefficient extension

The rational model has the printed equation over Q(n). The complex
generic equation used by the local and Euler proofs is its
constant extension. Existence of a rational minimal regular proper
model uses the same published model theorem as over C.
This file does not assume that the two total spaces are base changes.
-/
namespace Z2Z4Rank6.SurfaceRationalData
noncomputable section
open AlgebraicGeometry CategoryTheory Polynomial
open Common.Elliptic.SurfaceModel Common.Elliptic.SurfaceWeierstrassData
open SurfaceWeierstrassCharts SurfaceLocalInvariants

abbrev finiteEquation : WeierstrassCurve ℚ[X] := affineModel (R:=ℚ)
abbrev infinityEquation : WeierstrassCurve ℚ[X] := infinityModel (R:=ℚ)
abbrev curve : WeierstrassCurve (RatFunc ℚ) := genericCurve finiteEquation

theorem generic_discriminant_ne_zero : curve.Δ≠0 := by
  intro hz
  apply (affine_multiplicativeData_at_rational_bad (K:=ℚ) 0).1
  apply IsFractionRing.injective ℚ[X] (RatFunc ℚ)
  simpa only [curve,genericCurve,WeierstrassCurve.map_Δ,map_zero] using hz

instance curveElliptic : curve.IsElliptic :=
  ⟨isUnit_iff_ne_zero.mpr generic_discriminant_ne_zero⟩

theorem finiteEquation_complex :
    finiteEquation.map (Polynomial.mapRingHom (algebraMap ℚ ℂ))=
      SurfaceComplexData.finiteEquation := by
  ext <;> simp [finiteEquation,SurfaceComplexData.finiteEquation,affineModel,
    WeierstrassCurve.map,surfaceS,surfaceW]

theorem infinityEquation_complex :
    infinityEquation.map (Polynomial.mapRingHom (algebraMap ℚ ℂ))=
      SurfaceComplexData.infinityEquation := by
  ext <;> simp [infinityEquation,SurfaceComplexData.infinityEquation,infinityModel,
    WeierstrassCurve.map,infinityS,infinityW]

theorem curve_complex : curve.map (constantExtension ℚ ℂ)=SurfaceComplexData.curve := by
  rw [curve,genericCurve_constantExtension,finiteEquation_complex]


end
end Z2Z4Rank6.SurfaceRationalData
