module

public import Z2Z4Rank6.GSpecializationPolynomials
public import Z2Z4Rank6.GusicTadicQuartic

@[expose] public section

/-!
# Irreducibility of the h-twist quartic

The extra factor in Proposition 7.2(b), Jaswal,
DOI: 10.5281/zenodo.23437117. An explicit complex root has rationally
independent first four powers, by irrationality of sqrt(814). The primitive
integer polynomial is therefore irreducible and squarefree.
-/

namespace Z2Z4Rank6.GSpecialization

open Polynomial
open scoped BigOperators
noncomputable section

def hMonicQ : ℚ[X] := Polynomial.X^4-C (9998/99)*Polynomial.X^2+9801
def hRoot : ℂ := (10/33)*(Real.sqrt 814 : ℂ)+(49/33)*(Real.sqrt 11 : ℂ)*Complex.I

private theorem sqrt814_sq : (Real.sqrt 814 : ℂ)^2=(814 : ℂ) := by
  norm_cast
  exact Real.sq_sqrt (by norm_num)

private theorem sqrt11_sq : (Real.sqrt 11 : ℂ)^2=(11 : ℂ) := by
  norm_cast
  exact Real.sq_sqrt (by norm_num)

theorem hRoot_sq : hRoot^2=4999/99+(980/1089)*(Real.sqrt 814 : ℂ)*
    (Real.sqrt 11 : ℂ)*Complex.I := by
  unfold hRoot
  ring_nf
  rw [sqrt814_sq,sqrt11_sq,Complex.I_sq]
  ring

theorem hRoot_cube : hRoot^3=(1970/3267)*(Real.sqrt 814 : ℂ)+
    (970151/3267)*(Real.sqrt 11 : ℂ)*Complex.I := by
  rw [pow_succ,hRoot_sq]
  unfold hRoot
  ring_nf
  rw [sqrt814_sq,sqrt11_sq,Complex.I_sq]
  ring

theorem hRoot_aeval : aeval hRoot hMonicQ=0 := by
  norm_num [hMonicQ,Polynomial.aeval_def]
  rw [show hRoot^4=(hRoot^2)^2 by ring,hRoot_sq]
  ring_nf
  rw [sqrt814_sq,sqrt11_sq,Complex.I_sq]
  ring

private theorem rational_sqrt814_separation (a b : ℚ)
    (h : (a : ℝ)+(b : ℝ)*Real.sqrt 814=0) : a=0 ∧ b=0 := by
  have hi : Irrational (Real.sqrt 814) :=
    irrational_sqrt_natCast_iff.mpr (by norm_num : ¬IsSquare (814 : ℕ))
  have hb : b=0 := by
    by_contra hb
    have hbR : (b : ℝ)≠0 := by exact_mod_cast hb
    apply hi
    refine ⟨-(a/b), ?_⟩
    push_cast
    rw [←neg_div]
    apply (div_eq_iff hbR).2
    nlinarith [h]
  constructor
  · rw [hb] at h
    norm_num at h
    exact_mod_cast h
  · exact hb

private theorem rat_algebraMap_complex (q : ℚ) : algebraMap ℚ ℂ q=(q : ℂ) := by
  simpa only [Rat.cast_id] using map_ratCast (algebraMap ℚ ℂ) q

theorem hRoot_powers_independent : LinearIndependent ℚ (fun i : Fin 4 => hRoot^i.val) := by
  apply Fintype.linearIndependent_iff.mpr
  intro c hc
  rw [Fin.sum_univ_four] at hc
  simp only [Algebra.smul_def,rat_algebraMap_complex] at hc
  norm_num only [Fin.val_zero,Fin.val_one,pow_zero,pow_one,mul_one] at hc
  change (c 0 : ℂ)+(c 1 : ℂ)*hRoot+(c 2 : ℂ)*hRoot^2+(c 3 : ℂ)*hRoot^3=0 at hc
  rw [hRoot_sq,hRoot_cube] at hc
  unfold hRoot at hc
  have hre := congrArg Complex.re hc
  have him := congrArg Complex.im hc
  norm_num [Complex.mul_re,Complex.mul_im] at hre him
  have hr := rational_sqrt814_separation (c 0+(4999/99)*c 2)
    ((10/33)*c 1+(1970/3267)*c 3) (by push_cast; linear_combination hre)
  have him' : ((49/33 : ℚ)*c 1+(970151/3267)*c 3 : ℚ)+
      (((980/1089 : ℚ)*c 2 : ℚ) : ℝ)*Real.sqrt 814=0 := by
    have ht : Real.sqrt 11 *
        (((49/33 : ℚ)*c 1+(970151/3267)*c 3 : ℚ)+
          (((980/1089 : ℚ)*c 2 : ℚ) : ℝ)*Real.sqrt 814)=0 := by
      push_cast
      linear_combination him
    exact (mul_eq_zero.mp ht).resolve_left (by positivity)
  have hi := rational_sqrt814_separation ((49/33)*c 1+(970151/3267)*c 3)
    ((980/1089)*c 2) him'
  intro i
  fin_cases i
  · change c 0=0
    nlinarith [hr.1,hr.2,hi.1,hi.2]
  · change c 1=0
    nlinarith [hr.1,hr.2,hi.1,hi.2]
  · change c 2=0
    nlinarith [hr.1,hr.2,hi.1,hi.2]
  · change c 3=0
    nlinarith [hr.1,hr.2,hi.1,hi.2]

theorem hMonicQ_irreducible : Irreducible hMonicQ := by
  have hm : hMonicQ.Monic := by unfold hMonicQ; monicity!
  have hd : hMonicQ.degree=4 := by unfold hMonicQ; compute_degree!
  have he := minpoly.eq_of_linearIndependent ℚ hRoot hm hRoot_aeval 4 hd hRoot_powers_independent
  rw [←he]
  exact minpoly.irreducible ⟨hMonicQ,hm,hRoot_aeval⟩

theorem hPoly_irreducible : Irreducible hPoly := by
  apply (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast hPoly_primitive).2
  have he : hPoly.map (Int.castRingHom ℚ)=C 99*hMonicQ := by
    ext n
    cases n with
    | zero => norm_num [hPoly,GTwistSelmer.hPolynomial,hMonicQ,Polynomial.coeff_C_mul]
    | succ n =>
      simp [hPoly,GTwistSelmer.hPolynomial,hMonicQ,Polynomial.coeff_C_mul]
      split_ifs <;> norm_num
  rw [he]
  apply (irreducible_isUnit_mul (isUnit_C.mpr (isUnit_iff_ne_zero.mpr (by norm_num)))).2
  exact hMonicQ_irreducible

theorem hPoly_squarefree : Squarefree hPoly := hPoly_irreducible.squarefree

end
end Z2Z4Rank6.GSpecialization
