module

public import Z2Z4Rank6.SurfaceWeierstrassCharts
public import Mathlib.Data.Fin.VecNotation

@[expose] public section

/-!
# Exact local invariants of the surface in Lemma 3.1(b)

These are orders of the polynomial discriminants and
nonvanishing c4 values. The numerical data are inputs to, and not a
definition of, the Kodaira type of a minimal regular fiber.

Source: Jaswal, DOI 10.5281/zenodo.23437117, Lemma 3.1(b).
-/

namespace Z2Z4Rank6.SurfaceLocalInvariants

noncomputable section
open Polynomial
open SurfaceWeierstrassCharts Common.Elliptic.SurfaceLocalData

variable {K : Type*} [Field K] [CharZero K]

def rationalBadParameter : Fin 6 → K := ![1,81,121,9801,99,0]
def rationalBadOrder : Fin 6 → ℕ := ![4,4,4,4,2,1]

private theorem N_ne_zero_polynomial : twistN (Polynomial.X : K[X]) ≠ 0 := by
  intro h
  have h1 := congrArg (Polynomial.eval 1) h
  norm_num [twistN] at h1

private theorem affine_delta_ne_zero : (affineModel (R:=K)).Δ ≠ 0 := by
  intro h
  have he := congrArg (Polynomial.eval 2) h
  norm_num [affine_delta_factorization,deltaConstant,twistN] at he

private theorem infinity_delta_ne_zero : (infinityModel (R:=K)).Δ ≠ 0 := by
  intro h
  have he := congrArg (Polynomial.eval 2) h
  norm_num [infinity_delta_factorization,deltaConstant,infinityN] at he

theorem affine_discriminantOrder_formula [DecidableEq K] (t : K) :
    discriminantOrder (affineModel (R:=K)) t =
      4*(if t=1 then 1 else 0) + 4*(if t=81 then 1 else 0) +
      4*(if t=121 then 1 else 0) + 4*(if t=9801 then 1 else 0) +
      (if t=0 then 1 else 0) + 2*(if t=99 then 1 else 0) +
      2*(twistN (Polynomial.X : K[X])).rootMultiplicity t := by
  have hlin (a : K) : (Polynomial.X-C a : K[X]) ≠ 0 := X_sub_C_ne_zero a
  have hn := N_ne_zero_polynomial (K:=K)
  have hc : (C (deltaConstant (R:=K)) : K[X]) ≠ 0 := by
    simp [deltaConstant]
  unfold discriminantOrder
  rw [affine_delta_factorization]
  have hprod : C (deltaConstant (R:=K)) *
      (Polynomial.X-1)^4*(Polynomial.X-81)^4*(Polynomial.X-121)^4*(Polynomial.X-9801)^4*
      Polynomial.X*(Polynomial.X-99)^2*(twistN Polynomial.X)^2 ≠ (0:K[X]) := by
    rw [←affine_delta_factorization]
    exact affine_delta_ne_zero
  obtain ⟨h6,hN⟩ := mul_ne_zero_iff.mp hprod
  obtain ⟨h5,h99⟩ := mul_ne_zero_iff.mp h6
  obtain ⟨h4,hX⟩ := mul_ne_zero_iff.mp h5
  obtain ⟨h3,h9801⟩ := mul_ne_zero_iff.mp h4
  obtain ⟨h2,h121⟩ := mul_ne_zero_iff.mp h3
  obtain ⟨h1,h81⟩ := mul_ne_zero_iff.mp h2
  obtain ⟨h0,h1p⟩ := mul_ne_zero_iff.mp h1
  rw [rootMultiplicity_mul hprod,rootMultiplicity_mul h6,rootMultiplicity_mul h5,
    rootMultiplicity_mul h4,rootMultiplicity_mul h3,rootMultiplicity_mul h2,
    rootMultiplicity_mul h1]
  simp only [rootMultiplicity_C]
  rw [rootMultiplicity_pow (twistN Polynomial.X) hn t 2,
    rootMultiplicity_pow (Polynomial.X-99) (by intro h; simp [h] at h99) t 2,
    rootMultiplicity_pow (Polynomial.X-9801) (by intro h; simp [h] at h9801) t 4,
    rootMultiplicity_pow (Polynomial.X-121) (by intro h; simp [h] at h121) t 4,
    rootMultiplicity_pow (Polynomial.X-81) (by intro h; simp [h] at h81) t 4,
    rootMultiplicity_pow (Polynomial.X-1) (by intro h; simp [h] at h1p) t 4]
  have hl (a : ℕ) : (Polynomial.X-(a:K[X])).rootMultiplicity t =
      if t=(a:K) then 1 else 0 := by
    simpa only [Polynomial.C_eq_natCast] using
      (rootMultiplicity_X_sub_C (x:=t) (y:=(a:K)))
  have hx : (Polynomial.X : K[X]).rootMultiplicity t = if t=0 then 1 else 0 := by
    simpa only [Nat.cast_zero,sub_zero] using hl 0
  have hl1 := hl 1
  have hl81 := hl 81
  have hl121 := hl 121
  have hl9801 := hl 9801
  have hl99 := hl 99
  norm_num only [Nat.cast_one,Nat.cast_ofNat] at hl1 hl81 hl121 hl9801 hl99
  rw [hl1,hl81,hl121,hl9801,hl99,hx]
  simp

theorem affine_c4_at_rational_bad (i : Fin 6) :
    (affineModel (R:=K)).c₄.eval (rationalBadParameter i) ≠ 0 := by
  fin_cases i <;> norm_num [rationalBadParameter,affine_c4,surfaceS,surfaceW]

theorem affine_discriminantOrder_at_rational_bad (i : Fin 6) :
    discriminantOrder (affineModel (R:=K)) (rationalBadParameter i)=rationalBadOrder i := by
  classical
  rw [affine_discriminantOrder_formula]
  have hn : (twistN (Polynomial.X:K[X])).rootMultiplicity (rationalBadParameter i)=0 := by
    apply rootMultiplicity_eq_zero
    fin_cases i <;> norm_num [IsRoot,rationalBadParameter,twistN]
  rw [hn]
  fin_cases i <;> norm_num [rationalBadParameter,rationalBadOrder]

theorem affine_multiplicativeData_at_rational_bad (i : Fin 6) :
    MultiplicativeData (affineModel (R:=K)) (rationalBadParameter i) (rationalBadOrder i) := by
  refine ⟨affine_delta_ne_zero,affine_c4_at_rational_bad i,?_,
    affine_discriminantOrder_at_rational_bad i⟩
  fin_cases i <;> decide

theorem quadratic_root_ne_rational_bad (t : K) (hN : twistN t = 0) (i : Fin 6) :
    t ≠ rationalBadParameter i := by
  intro ht
  rw [ht] at hN
  fin_cases i <;> norm_num [rationalBadParameter,twistN] at hN

theorem quadratic_root_ne_one (t : K) (hN : twistN t = 0) : t ≠ 1 := by
  exact quadratic_root_ne_rational_bad t hN 0

theorem quadratic_root_multiplicity (t : K) (hN : twistN t = 0) :
    (twistN (Polynomial.X : K[X])).rootMultiplicity t = 1 := by
  have hn := N_ne_zero_polynomial (K:=K)
  have hp : 0 < (twistN (Polynomial.X : K[X])).rootMultiplicity t := by
    apply (rootMultiplicity_pos hn).mpr
    simpa [IsRoot,twistN] using hN
  have hle : (twistN (Polynomial.X : K[X])).rootMultiplicity t ≤ 1 := by
    by_contra h
    have hd := ((one_lt_rootMultiplicity_iff_isRoot (t:=t) hn).mp (by omega)).2
    have hd' : 2*t-2=0 := by
      simpa [IsRoot,twistN,Polynomial.derivative_sub,Polynomial.derivative_add,
        Polynomial.derivative_pow] using hd
    have ht : t=1 := by linear_combination hd'/2
    exact quadratic_root_ne_one t hN ht
  omega

theorem affine_discriminantOrder_at_quadratic_root (t : K) (hN : twistN t=0) :
    discriminantOrder (affineModel (R:=K)) t = 2 := by
  classical
  rw [affine_discriminantOrder_formula,quadratic_root_multiplicity t hN]
  have h0 := quadratic_root_ne_rational_bad t hN 0
  have h1 := quadratic_root_ne_rational_bad t hN 1
  have h2 := quadratic_root_ne_rational_bad t hN 2
  have h3 := quadratic_root_ne_rational_bad t hN 3
  have h4 := quadratic_root_ne_rational_bad t hN 4
  have h5 := quadratic_root_ne_rational_bad t hN 5
  norm_num [rationalBadParameter] at h0 h1 h2 h3 h4 h5
  simp [h0,h1,h2,h3,h4,h5]

theorem affine_c4_at_quadratic_root (t : K) (hN : twistN t=0) :
    (affineModel (R:=K)).c₄.eval t ≠ 0 := by
  have hw : surfaceW t ≠ 0 := by
    have h0 := quadratic_root_ne_rational_bad t hN 0
    have h1 := quadratic_root_ne_rational_bad t hN 1
    have h2 := quadratic_root_ne_rational_bad t hN 2
    have h3 := quadratic_root_ne_rational_bad t hN 3
    norm_num [rationalBadParameter] at h0 h1 h2 h3
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
      (sub_ne_zero.mpr h0)) (sub_ne_zero.mpr h1)) (sub_ne_zero.mpr h2))
      (sub_ne_zero.mpr h3)
  have hs := surfaceS_sub_twoW t
  rw [hN] at hs
  have hsw : surfaceS t=2*surfaceW t := by linear_combination hs
  simp only [affine_c4,eval_mul,eval_ofNat,eval_sub,eval_pow]
  have heS : (surfaceS (Polynomial.X:K[X])).eval t=surfaceS t := by simp [surfaceS]
  have heW : (surfaceW (Polynomial.X:K[X])).eval t=surfaceW t := by simp [surfaceW]
  rw [heS,heW,hsw]
  rw [show 16*((2*surfaceW t)^2-3*(surfaceW t)^2)=16*(surfaceW t)^2 by ring]
  exact mul_ne_zero (show (16:K) ≠ 0 by norm_num) (pow_ne_zero 2 hw)

theorem affine_multiplicativeData_at_quadratic_root (t : K) (hN : twistN t=0) :
    MultiplicativeData (affineModel (R:=K)) t 2 :=
  ⟨affine_delta_ne_zero,affine_c4_at_quadratic_root t hN,by decide,
    affine_discriminantOrder_at_quadratic_root t hN⟩

/-- Away from the listed rational parameters and the two quadratic
roots, the discriminant is nonzero. -/
theorem affine_goodData_elsewhere (t : K) (hr : ∀i : Fin 6,t ≠ rationalBadParameter i)
    (hN : twistN t ≠ 0) : GoodData (affineModel (R:=K)) t := by
  have h0 := hr 0
  have h1 := hr 1
  have h2 := hr 2
  have h3 := hr 3
  have h4 := hr 4
  have h5 := hr 5
  norm_num [rationalBadParameter] at h0 h1 h2 h3 h4 h5
  simp only [GoodData,affine_delta_factorization,eval_mul,eval_C,eval_pow,eval_sub,
    eval_X,eval_ofNat,eval_one]
  have heN : (twistN (Polynomial.X:K[X])).eval t=twistN t := by simp [twistN]
  rw [heN]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
    (mul_ne_zero (mul_ne_zero (by norm_num [deltaConstant]) (pow_ne_zero 4 (sub_ne_zero.mpr h0)))
      (pow_ne_zero 4 (sub_ne_zero.mpr h1))) (pow_ne_zero 4 (sub_ne_zero.mpr h2)))
        (pow_ne_zero 4 (sub_ne_zero.mpr h3))) h5) (pow_ne_zero 2 (sub_ne_zero.mpr h4)))
          (pow_ne_zero 2 hN)

/-- The infinity chart has unit c4 at the point at infinity. -/
theorem infinity_c4_at_zero : (infinityModel (R:=K)).c₄.eval 0 ≠ 0 := by
  norm_num [infinity_c4,infinityS,infinityW]

/-- The infinity discriminant has a simple zero. -/
theorem infinity_discriminantOrder :
    discriminantOrder (infinityModel (R:=K)) 0 = 1 := by
  let q : K[X] := C (deltaConstant (R:=K)) *
    (1-Polynomial.X)^4*(1-81*Polynomial.X)^4*(1-121*Polynomial.X)^4*
    (1-9801*Polynomial.X)^4*(1-99*Polynomial.X)^2*(infinityN Polynomial.X)^2
  apply rootMultiplicity_of_factorization _ q 0 1
  · rw [infinity_delta_factorization]
    simp only [C_0,sub_zero,pow_one]
    dsimp [q]
    ring
  · norm_num [q,deltaConstant,infinityN]

/-- Multiplicative local invariant data at infinity. -/
theorem infinity_multiplicativeData : MultiplicativeData (infinityModel (R:=K)) 0 1 :=
  ⟨infinity_delta_ne_zero,infinity_c4_at_zero,by decide,infinity_discriminantOrder⟩

end
end Z2Z4Rank6.SurfaceLocalInvariants
