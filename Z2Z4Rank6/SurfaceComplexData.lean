module

public import Z2Z4Rank6.SurfaceLocalInvariants
public import Common.Elliptic.ComplexEllipticSurfaceTheorems
public import Mathlib.Analysis.RCLike.Sqrt

@[expose] public section

/-!
# Complex local data of the surface equation

Jaswal, DOI 10.5281/zenodo.23437117, Lemma 3.1(b). The generic curve is
exactly the printed Weierstrass equation over C(n). Its infinity chart
uses the reciprocal coefficient identities. The quadratic roots
are complex numbers, with square and distinctness proofs.
-/
namespace Z2Z4Rank6.SurfaceComplexData
noncomputable section
open Polynomial AlgebraicGeometry CategoryTheory
open Common.Elliptic.SurfaceWeierstrassData
open SurfaceWeierstrassCharts SurfaceLocalInvariants

abbrev finiteEquation : WeierstrassCurve ℂ[X] := affineModel (R:=ℂ)
abbrev infinityEquation : WeierstrassCurve ℂ[X] := infinityModel (R:=ℂ)
abbrev curve : WeierstrassCurve (RatFunc ℂ) := genericCurve finiteEquation

theorem generic_discriminant_ne_zero : curve.Δ≠0 := by
  intro hz
  apply (affine_multiplicativeData_at_rational_bad (K:=ℂ) 0).1
  apply IsFractionRing.injective ℂ[X] (RatFunc ℂ)
  simpa only [curve,genericCurve,WeierstrassCurve.map_Δ,map_zero] using hz

instance curveElliptic : curve.IsElliptic := ⟨isUnit_iff_ne_zero.mpr generic_discriminant_ne_zero⟩

theorem reciprocal_compatibility : ReciprocalCompatibility finiteEquation infinityEquation 2 := by
  intro i s hs
  fin_cases i
  · simp [coefficient,coefficientWeight,affineModel,infinityModel]
  · change (infinityS (Polynomial.X : ℂ[X])).eval s=
      s^4*(surfaceS (Polynomial.X : ℂ[X])).eval (1/s)
    simpa [infinityS,surfaceS] using infinityS_eq s hs
  · simp [coefficient,coefficientWeight,affineModel,infinityModel]
  · change ((infinityW (Polynomial.X : ℂ[X]))^2).eval s=
      s^8*((surfaceW (Polynomial.X : ℂ[X]))^2).eval (1/s)
    simp only [eval_pow]
    have h := infinityW_eq s hs
    have e1 : (infinityW (Polynomial.X : ℂ[X])).eval s=infinityW s := by simp [infinityW]
    have e2 : (surfaceW (Polynomial.X : ℂ[X])).eval (1/s)=surfaceW (1/s) := by simp [surfaceW]
    rw [e1,e2,h]
    ring
  · simp [coefficient,coefficientWeight,affineModel,infinityModel]

def quadraticSquareRoot : ℂ := Complex.sqrt (-9800)
def quadraticRoot : Fin 2 → ℂ := ![1+quadraticSquareRoot,1-quadraticSquareRoot]

theorem quadraticSquareRoot_sq : quadraticSquareRoot^2=(-9800 : ℂ) := by
  simp [quadraticSquareRoot,Complex.sqrt]

theorem quadraticSquareRoot_ne_zero : quadraticSquareRoot≠0 := by
  intro h
  have hs := quadraticSquareRoot_sq
  rw [h] at hs
  norm_num at hs

theorem quadraticRoot_root (i : Fin 2) : twistN (quadraticRoot i)=0 := by
  fin_cases i <;> dsimp [quadraticRoot,twistN] <;> linear_combination quadraticSquareRoot_sq

theorem quadraticRoot_injective : Function.Injective quadraticRoot := by
  intro i j h
  fin_cases i <;> fin_cases j
  · rfl
  · have he : 1+quadraticSquareRoot=1-quadraticSquareRoot := h
    have hz : quadraticSquareRoot=0 := by linear_combination he/2
    exact False.elim (quadraticSquareRoot_ne_zero hz)
  · have he : 1-quadraticSquareRoot=1+quadraticSquareRoot := h
    have hz : quadraticSquareRoot=0 := by linear_combination -he/2
    exact False.elim (quadraticSquareRoot_ne_zero hz)
  · rfl

theorem quadraticRoot_complete (t : ℂ) : twistN t=0 ↔ t∈Set.range quadraticRoot := by
  have he : twistN t=(t-quadraticRoot 0)*(t-quadraticRoot 1) := by
    dsimp [twistN,quadraticRoot]
    linear_combination quadraticSquareRoot_sq
  rw [he,mul_eq_zero]
  constructor
  · rintro (h|h)
    · exact ⟨0,(sub_eq_zero.mp h).symm⟩
    · exact ⟨1,(sub_eq_zero.mp h).symm⟩
  · rintro ⟨i,rfl⟩
    fin_cases i <;> simp

end
end Z2Z4Rank6.SurfaceComplexData
