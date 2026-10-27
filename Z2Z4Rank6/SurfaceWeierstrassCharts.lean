module

public import Z2Z4Rank6.FamilyIdentities
public import Common.Elliptic.SurfaceLocalData

@[expose] public section

/-!
# The two integral Weierstrass charts of the surface in Lemma 3.1

The infinity chart is the admissible transformation
`n = 1/s`, `x = x'/s^4`, `y = y'/s^6`. Its discriminant is an
explicit polynomial with a simple zero at `s=0`. These statements
concern the Weierstrass equations; they do not assert that a
minimal regular elliptic surface has been constructed.

Source: Jaswal, DOI 10.5281/zenodo.23437117, Lemma 3.1(b).
-/

namespace Z2Z4Rank6.SurfaceWeierstrassCharts

open Polynomial
noncomputable section

variable {R : Type*} [CommRing R]

def affineModel : WeierstrassCurve R[X] where
  a₁ := 0
  a₂ := surfaceS Polynomial.X
  a₃ := 0
  a₄ := (surfaceW Polynomial.X)^2
  a₆ := 0

def infinityS (s : R) : R :=
  98*(1+9996*s-1960394*s^2+97970796*s^3+96059601*s^4)

def infinityW (s : R) : R :=
  -49*(1-s)*(1-81*s)*(1-121*s)*(1-9801*s)

def infinityN (s : R) : R := 1-2*s+9801*s^2

def infinityModel : WeierstrassCurve R[X] where
  a₁ := 0
  a₂ := infinityS Polynomial.X
  a₃ := 0
  a₄ := (infinityW Polynomial.X)^2
  a₆ := 0

def deltaConstant : R := 16*49^4*196*1960000

theorem affine_c4 :
    (affineModel (R:=R)).c₄ = 16*((surfaceS Polynomial.X)^2-3*(surfaceW Polynomial.X)^2) := by
  simp only [affineModel,WeierstrassCurve.c₄,WeierstrassCurve.b₂,
    WeierstrassCurve.b₄]
  ring

theorem affine_delta :
    (affineModel (R:=R)).Δ =
      16*(surfaceW Polynomial.X)^4*((surfaceS Polynomial.X)^2-4*(surfaceW Polynomial.X)^2) := by
  simp only [affineModel,WeierstrassCurve.Δ,WeierstrassCurve.b₂,
    WeierstrassCurve.b₄,WeierstrassCurve.b₆,WeierstrassCurve.b₈]
  ring

theorem affine_delta_factorization :
    (affineModel (R:=R)).Δ = C (deltaConstant (R:=R)) *
      (Polynomial.X-1)^4*(Polynomial.X-81)^4*(Polynomial.X-121)^4*(Polynomial.X-9801)^4*
      Polynomial.X*(Polynomial.X-99)^2*(twistN Polynomial.X)^2 := by
  rw [affine_delta,surface_discriminant_factorization]
  norm_num [deltaConstant,Polynomial.C_ofNat]

theorem infinity_c4 :
    (infinityModel (R:=R)).c₄ = 16*((infinityS Polynomial.X)^2-3*(infinityW Polynomial.X)^2) := by
  simp only [infinityModel,WeierstrassCurve.c₄,WeierstrassCurve.b₂,
    WeierstrassCurve.b₄]
  ring

theorem infinity_delta :
    (infinityModel (R:=R)).Δ =
      16*(infinityW Polynomial.X)^4*((infinityS Polynomial.X)^2-4*(infinityW Polynomial.X)^2) := by
  simp only [infinityModel,WeierstrassCurve.Δ,WeierstrassCurve.b₂,
    WeierstrassCurve.b₄,WeierstrassCurve.b₆,WeierstrassCurve.b₈]
  ring

theorem infinity_S_sub_twoW (s : R) :
    infinityS s-2*infinityW s=196*(infinityN s)^2 := by
  unfold infinityS infinityW infinityN
  ring

theorem infinity_S_add_twoW (s : R) :
    infinityS s+2*infinityW s=1960000*s*(1-99*s)^2 := by
  unfold infinityS infinityW
  ring

theorem infinity_delta_factorization :
    (infinityModel (R:=R)).Δ = C (deltaConstant (R:=R)) *
      (1-Polynomial.X)^4*(1-81*Polynomial.X)^4*(1-121*Polynomial.X)^4*(1-9801*Polynomial.X)^4*
      Polynomial.X*(1-99*Polynomial.X)^2*(infinityN Polynomial.X)^2 := by
  rw [infinity_delta]
  have h : (infinityS (Polynomial.X:R[X]))^2-4*(infinityW Polynomial.X)^2 =
      196*1960000*Polynomial.X*(1-99*Polynomial.X)^2*(infinityN Polynomial.X)^2 := by
    calc
      _ = (infinityS Polynomial.X-2*infinityW Polynomial.X)*(infinityS Polynomial.X+2*infinityW Polynomial.X) := by ring
      _ = _ := by rw [infinity_S_sub_twoW,infinity_S_add_twoW]; ring
  rw [h]
  simp only [deltaConstant,map_mul,map_pow,map_ofNat]
  unfold infinityW
  ring

section Field

variable {K : Type*} [Field K]

theorem infinityS_eq (s : K) (hs : s ≠ 0) :
    infinityS s=s^4*surfaceS (1/s) := by
  unfold infinityS surfaceS
  field_simp

theorem infinityW_eq (s : K) (hs : s ≠ 0) :
    infinityW s=s^4*surfaceW (1/s) := by
  unfold infinityW surfaceW
  field_simp

/-- The equation after the printed substitution. -/
theorem infinity_equation (s x y : K) (hs : s ≠ 0) :
    (y/s^6)^2=(x/s^4)*((x/s^4)^2+surfaceS (1/s)*(x/s^4)+(surfaceW (1/s))^2) ↔
      y^2=x*(x^2+infinityS s*x+(infinityW s)^2) := by
  rw [infinityS_eq s hs,infinityW_eq s hs]
  field_simp

end Field
end
end Z2Z4Rank6.SurfaceWeierstrassCharts
