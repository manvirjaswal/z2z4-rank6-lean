import Z2Z4Rank6.SecondFamily
import Z2Z4Rank6.TorsionCongruence
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.Tactic

/-!
# The second family's 3-adic torsion neighborhood

Arithmetic in Remark 8.2 of M. Jaswal, *Infinitely many elliptic curves with
 torsion Z/2Z × Z/4Z and rank at least six*,
DOI 10.5281/zenodo.23437117. The neighborhood includes its center explicitly,
because Mathlib assigns valuation zero to the rational number zero.
-/
namespace Z2Z4Rank6.SecondFamily
noncomputable section
local instance threePrimeRemark82 : Fact (Nat.Prime 3) := ⟨by decide⟩

def baseTheta : ℚ := 857/140

def ThetaNear3 (t : ℚ) : Prop := t=baseTheta ∨ 6 ≤ padicValRat 3 (t-baseTheta)

def thetaRoots : Fin 8 → ℚ := ![10/3,-10/3,87/10,-87/10,25/4,-25/4,116/25,-116/25]
def thetaRootVals : Fin 8 → ℤ := ![-1,-1,0,0,2,0,0,5]

private theorem val3_unit (r : ℚ) (hn : ¬(3 : ℤ) ∣ r.num) (hd : ¬3 ∣ r.den) :
    padicValRat 3 r=0 := by
  rw [padicValRat_def,padicValInt.eq_zero_of_not_dvd hn,
    padicValNat.eq_zero_of_not_dvd hd]
  norm_num

private theorem val3_of_scale (q r : ℚ) (n : ℤ)
    (h : q=(3:ℚ)^n*r) (hr : r≠0) (hv : padicValRat 3 r=0) : padicValRat 3 q=n := by
  have hthree : padicValRat 3 (3:ℚ)=1 := padicValRat.self (p:=3) (by decide)
  rw [h,padicValRat.mul (zpow_ne_zero _ (by norm_num)) hr,padicValRat.zpow,
    hthree,hv]
  ring

theorem theta_base_factor_valuation (i : Fin 8) :
    padicValRat 3 (baseTheta-thetaRoots i)=thetaRootVals i := by
  fin_cases i
  · apply val3_of_scale _ (1171/140 : ℚ) (-1)
    · norm_num [baseTheta,thetaRoots]
    · norm_num
    · exact val3_unit _ (by norm_num) (by norm_num)
  · apply val3_of_scale _ (3971/140 : ℚ) (-1)
    · norm_num [baseTheta,thetaRoots]
    · norm_num
    · exact val3_unit _ (by norm_num) (by norm_num)
  · apply val3_of_scale _ (-361/140 : ℚ) (0)
    · norm_num [baseTheta,thetaRoots]
    · norm_num
    · exact val3_unit _ (by norm_num) (by norm_num)
  · apply val3_of_scale _ (415/28 : ℚ) (0)
    · norm_num [baseTheta,thetaRoots]
    · norm_num
    · exact val3_unit _ (by norm_num) (by norm_num)
  · apply val3_of_scale _ (-1/70 : ℚ) (2)
    · norm_num [baseTheta,thetaRoots]
    · norm_num
    · exact val3_unit _ (by norm_num) (by norm_num)
  · apply val3_of_scale _ (433/35 : ℚ) (0)
    · norm_num [baseTheta,thetaRoots]
    · norm_num
    · exact val3_unit _ (by norm_num) (by norm_num)
  · apply val3_of_scale _ (1037/700 : ℚ) (0)
    · norm_num [baseTheta,thetaRoots]
    · norm_num
    · exact val3_unit _ (by norm_num) (by norm_num)
  · apply val3_of_scale _ (31/700 : ℚ) (5)
    · norm_num [baseTheta,thetaRoots]
    · norm_num
    · exact val3_unit _ (by norm_num) (by norm_num)

private theorem denominator_base_valuation : padicValRat 3 (baseTheta^2-29)=0 := by
  apply val3_unit _ <;> norm_num [baseTheta]

private theorem twice_center_valuation : padicValRat 3 (2*baseTheta)=0 := by
  apply val3_unit _ <;> norm_num [baseTheta]

private theorem constant_valuation :
    padicValRat 3 (-(((beta:ℚ)-1)*(beta-lambda^2))) = -6 := by
  apply val3_of_scale _ (-13456000000/214358881 : ℚ) (-6)
  · norm_num [beta,lambda]
  · norm_num
  · exact val3_unit _ (by norm_num) (by norm_num)

theorem theta_factor_stable (t : ℚ) (ht : ThetaNear3 t) (i : Fin 8) :
    t-thetaRoots i ≠ 0 ∧ padicValRat 3 (t-thetaRoots i)=thetaRootVals i := by
  have hc : baseTheta-thetaRoots i ≠ 0 := by fin_cases i <;> norm_num [baseTheta,thetaRoots]
  rcases ht with rfl | ht
  · exact ⟨hc,theta_base_factor_valuation i⟩
  · have hd : t-baseTheta ≠ 0 := by
      intro hd
      rw [hd,padicValRat.zero] at ht
      omega
    have hi : thetaRootVals i < 6 := by fin_cases i <;> norm_num [thetaRootVals]
    have hs := rational_valuation_stable hc hd (p:=3) (by
      rw [theta_base_factor_valuation]
      omega)
    have heq : baseTheta-thetaRoots i+(t-baseTheta)=t-thetaRoots i := by ring
    rw [heq,theta_base_factor_valuation] at hs
    exact hs

theorem theta_denominator_stable (t : ℚ) (ht : ThetaNear3 t) :
    t^2-29 ≠ 0 ∧ padicValRat 3 (t^2-29)=0 := by
  rcases ht with rfl | ht
  · exact ⟨by norm_num [baseTheta],denominator_base_valuation⟩
  · have hd : t-baseTheta ≠ 0 := by
      intro hd
      rw [hd,padicValRat.zero] at ht
      omega
    have htwice : 2*baseTheta ≠ 0 := by norm_num [baseTheta]
    have hs := rational_valuation_stable htwice hd (p:=3) (by
      rw [twice_center_valuation]
      omega)
    have heq : 2*baseTheta+(t-baseTheta)=t+baseTheta := by ring
    rw [heq,twice_center_valuation] at hs
    have he : (t-baseTheta)*(t+baseTheta) ≠ 0 := mul_ne_zero hd hs.1
    have heval : 6 ≤ padicValRat 3 ((t-baseTheta)*(t+baseTheta)) := by
      rw [padicValRat.mul hd hs.1,hs.2,add_zero]
      exact ht
    have hbase : baseTheta^2-29 ≠ 0 := by norm_num [baseTheta]
    have hs' := rational_valuation_stable hbase he (p:=3) (by
      rw [denominator_base_valuation]
      omega)
    have heq' : baseTheta^2-29+(t-baseTheta)*(t+baseTheta)=t^2-29 := by ring
    rw [heq',denominator_base_valuation] at hs'
    exact hs'

theorem theta_product_valuation (t : ℚ) (ht : ThetaNear3 t) :
    singularThetaProduct t ≠ 0 ∧ padicValRat 3 (singularThetaProduct t)=5 := by
  have h := rational_valuation_mul (rational_valuation_mul (rational_valuation_mul
    (rational_valuation_mul (rational_valuation_mul (rational_valuation_mul
    (rational_valuation_mul (theta_factor_stable t ht 0) (theta_factor_stable t ht 1))
    (theta_factor_stable t ht 2)) (theta_factor_stable t ht 3)) (theta_factor_stable t ht 4))
    (theta_factor_stable t ht 5)) (theta_factor_stable t ht 6)) (theta_factor_stable t ht 7)
  norm_num [thetaRoots,thetaRootVals,singularThetaProduct] at h ⊢
  exact h

theorem V_theta_factorization (t : ℚ) (hd : t^2-29 ≠ 0) :
    V ((thetaS1 t)^2) =
      (-(((beta:ℚ)-1)*(beta-lambda^2)))*singularThetaProduct t/(t^2-29)^4 := by
  have h := theta_singular_factorization t hd
  unfold V
  apply (eq_div_iff (pow_ne_zero 4 hd)).mpr
  linear_combination -h

/-- The printed radius six preserves ord₃(V)=-1 everywhere in
the stated rational theta-neighborhood. -/
theorem V_theta_valuation (t : ℚ) (ht : ThetaNear3 t) :
    V ((thetaS1 t)^2) ≠ 0 ∧ padicValRat 3 (V ((thetaS1 t)^2)) = -1 := by
  have hd := theta_denominator_stable t ht
  have hp := theta_product_valuation t ht
  have hc : -(((beta:ℚ)-1)*(beta-lambda^2)) ≠ 0 := by norm_num [beta,lambda]
  rw [V_theta_factorization t hd.1]
  refine ⟨div_ne_zero (mul_ne_zero hc hp.1) (pow_ne_zero 4 hd.1),?_⟩
  rw [padicValRat.div (mul_ne_zero hc hp.1) (pow_ne_zero 4 hd.1),
    padicValRat.mul hc hp.1,constant_valuation,hp.2,padicValRat.pow,hd.2]
  norm_num

theorem V_theta_not_squares (t : ℚ) (ht : ThetaNear3 t) :
    ¬IsSquare (V ((thetaS1 t)^2)) ∧ ¬IsSquare (-V ((thetaS1 t)^2)) := by
  have hv := (V_theta_valuation t ht).2
  have hodd : ∀ q : ℚ, padicValRat 3 q = -1 → ¬IsSquare q := by
    intro q hq
    rintro ⟨r,hr⟩
    have he : q=r^2 := by simpa only [pow_two] using hr
    rw [he,padicValRat.pow] at hq
    omega
  exact ⟨hodd _ hv,hodd _ (by simpa only [padicValRat.neg] using hv)⟩

/-- The stronger printed obstruction holds in the field Q₃. -/
theorem V_theta_not_squares_padic (t : ℚ) (ht : ThetaNear3 t) :
    ¬IsSquare ((V ((thetaS1 t)^2) : ℚ) : Padic 3) ∧
      ¬IsSquare ((-V ((thetaS1 t)^2) : ℚ) : Padic 3) := by
  have hv := (V_theta_valuation t ht).2
  have hodd : ∀ q : ℚ, padicValRat 3 q = -1 → ¬IsSquare (q : Padic 3) := by
    intro q hq
    rintro ⟨r,hr⟩
    have he : (q:Padic 3)=r^2 := by simpa only [pow_two] using hr
    have hval : (q:Padic 3).valuation = -1 := by rw [Padic.valuation_ratCast]; exact hq
    rw [he,Padic.valuation_pow] at hval
    omega
  exact ⟨hodd _ hv,hodd _ (by simpa only [padicValRat.neg] using hv)⟩

theorem F_theta_good (t : ℚ) (ht : ThetaNear3 t) : (F ((thetaS1 t)^2)).IsElliptic := by
  have hd := (theta_denominator_stable t ht).1
  have hv := (V_theta_valuation t ht).1
  have hs : thetaS1 t ≠ 0 := by
    unfold thetaS1
    exact mul_ne_zero (mul_ne_zero (by norm_num) (by positivity)) (inv_ne_zero hd)
  have hl : (0:ℚ)<lambda := by norm_num [lambda]
  constructor
  rw [isUnit_iff_ne_zero,F_discriminant,U_sq_sub_fourV_sq]
  exact mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 4 hv))
    (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
      (pow_ne_zero 2 (by positivity))) (pow_ne_zero 2 hs)) (pow_ne_zero 2 (by positivity)))

/-- Exact rational torsion on every fiber in the printed 3-adic class.
Infinitude is proved in SecondLocalInfinitude and SecondCongruenceInfinitude. -/
theorem F_theta_torsion_exact (hMazur : MazurTorsionTheorem)
    (t : ℚ) (ht : ThetaNear3 t) : TorsionExact (F ((thetaS1 t)^2)) := by
  let A := (thetaS1 t-1)*(thetaS1 t-lambda)
  let B := (thetaS1 t+1)*(thetaS1 t+lambda)
  have hsplit : F ((thetaS1 t)^2)=E A B := F_split (thetaS1 t)
  have hab : A*B= -V ((thetaS1 t)^2) := by dsimp [A,B,V]; ring
  have hAB : A*B ≠ 0 := by rw [hab]; exact neg_ne_zero.mpr (V_theta_valuation t ht).1
  have hgood := F_theta_good t ht
  have hdiff : A^2-B^2 ≠ 0 := by
    intro hd
    apply hgood.isUnit.ne_zero
    rw [hsplit,E_discriminant,hd]
    ring
  rw [hsplit]
  apply E_torsion_exact hMazur A B (mul_ne_zero hAB hdiff)
  · rw [hab]
    exact (V_theta_not_squares t ht).2
  · rw [hab,neg_neg]
    exact (V_theta_not_squares t ht).1

end
end Z2Z4Rank6.SecondFamily
