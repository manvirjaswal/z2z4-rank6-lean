import Z2Z4Rank6.HeightInvariantContentCharts
import Mathlib.Algebra.Polynomial.Homogenize
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.Localization.Rat
import Mathlib.RingTheory.Int.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Uniform integral content of the binary invariant forms

Jaswal, DOI 10.5281/zenodo.23437117, Remark 6.3.
Rational Bezout identities are cleared to integer identities and homogenized
in both affine charts. At primitive integer pairs, a common divisor of the
two homogeneous forms then divides a fixed nonzero integer. The application
uses the degree 48 forms (-27*c4)^3 and (-54*c6)^2, so the twelfth
power of every short-model normalization scale is uniformly bounded.
-/
namespace Z2Z4Rank6.HeightInvariantContent
noncomputable section
open scoped Classical
set_option maxHeartbeats 1000000

/-- Rational polynomial coprimality gives an integral Bezout identity with
a fixed nonzero integer on the right. -/
theorem exists_integer_bezout (f g : Polynomial ℤ)
    (h : IsCoprime (f.map (algebraMap ℤ ℚ)) (g.map (algebraMap ℤ ℚ))) :
    ∃ M : ℤ, M≠0 ∧ ∃ s t : Polynomial ℤ, s*f+t*g=Polynomial.C M := by
  obtain ⟨s,t,hst⟩ := h
  obtain ⟨a,ha,hsa⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) s
  obtain ⟨b,hb,htb⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) t
  let S := IsLocalization.integerNormalization (nonZeroDivisors ℤ) s
  let T := IsLocalization.integerNormalization (nonZeroDivisors ℤ) t
  refine ⟨a*b,mul_ne_zero (nonZeroDivisors.ne_zero ha) (nonZeroDivisors.ne_zero hb),
    Polynomial.C b*S,Polynomial.C a*T,?_⟩
  apply Polynomial.map_injective (algebraMap ℤ ℚ) Rat.intCast_injective
  simp only [Polynomial.map_add,Polynomial.map_mul,Polynomial.map_C]
  have hPoly : algebraMap ℤ (Polynomial ℚ)=Polynomial.C.comp (Int.castRingHom ℚ) :=
    Subsingleton.elim _ _
  have hRat : algebraMap ℤ ℚ=Int.castRingHom ℚ := Subsingleton.elim _ _
  have hs : S.map (algebraMap ℤ ℚ)=Polynomial.C (a:ℚ)*s := by
    calc
      _=a • s := hsa
      _=_ := by rw [Algebra.smul_def,hPoly]; rfl
  have ht : T.map (algebraMap ℤ ℚ)=Polynomial.C (b:ℚ)*t := by
    calc
      _=b • t := htb
      _=_ := by rw [Algebra.smul_def,hPoly]; rfl
  rw [hs,ht]
  calc
    _=Polynomial.C ((a:ℚ)*b)*(s*f.map (algebraMap ℤ ℚ)+t*g.map (algebraMap ℤ ℚ)) := by
      rw [Polynomial.C_mul]
      rw [hRat]
      simp only [Int.coe_castRingHom]
      ring
    _=Polynomial.C ((a*b:ℤ):ℚ) := by rw [hst,mul_one]; simp

/-- Dehomogenization in the chart where coordinate 1 is the denominator. -/
def chart (F : MvPolynomial (Fin 2) ℤ) : Polynomial ℤ :=
  MvPolynomial.aeval ![Polynomial.X,1] F

/-- A homogeneous combination of equal-degree forms homogenizes the
integer Bezout identity, without introducing a denominator. -/
theorem exists_chart_identity (F G : MvPolynomial (Fin 2) ℤ) (D : ℕ)
    (hF : F.IsHomogeneous D) (hG : G.IsHomogeneous D)
    (hcop : IsCoprime ((chart F).map (algebraMap ℤ ℚ))
      ((chart G).map (algebraMap ℤ ℚ))) :
    ∃ M : ℤ, M≠0 ∧ ∃ N : ℕ, ∃ U V : MvPolynomial (Fin 2) ℤ,
      MvPolynomial.C M*MvPolynomial.X 1^N=U*F+V*G := by
  obtain ⟨M,hM,s,t,hst⟩ := exists_integer_bezout (chart F) (chart G) hcop
  let K := max s.natDegree t.natDegree
  let U := s.homogenize K
  let V := t.homogenize K
  refine ⟨M,hM,K+D,U,V,?_⟩
  have hHom : (U*F+V*G).IsHomogeneous (K+D) :=
    ((Polynomial.isHomogeneous_homogenize s).mul hF).add
      ((Polynomial.isHomogeneous_homogenize t).mul hG)
  have hEval : MvPolynomial.aeval ![Polynomial.X,1] (U*F+V*G)=Polynomial.C M := by
    simp only [map_add,map_mul]
    change MvPolynomial.aeval ![Polynomial.X,1] (s.homogenize K)*chart F+
      MvPolynomial.aeval ![Polynomial.X,1] (t.homogenize K)*chart G=Polynomial.C M
    rw [Polynomial.aeval_homogenize_X_one s (le_max_left _ _),
      Polynomial.aeval_homogenize_X_one t (le_max_right _ _)]
    exact hst
  have hh := Polynomial.homogenize_eq_of_isHomogeneous hHom hEval
  simpa only [Polynomial.homogenize_C] using hh

/-- The exact integral chart identity controls divisibility at every pair,
including pairs on the coordinate axes. -/
theorem chart_common_divisor (F G : MvPolynomial (Fin 2) ℤ) (D : ℕ)
    (hF : F.IsHomogeneous D) (hG : G.IsHomogeneous D)
    (hcop : IsCoprime ((chart F).map (algebraMap ℤ ℚ))
      ((chart G).map (algebraMap ℤ ℚ))) :
    ∃ M : ℤ, M≠0 ∧ ∃ N : ℕ, ∀ (x : Fin 2→ℤ) (d : ℤ),
      d∣MvPolynomial.eval x F → d∣MvPolynomial.eval x G → d∣M*(x 1)^N := by
  obtain ⟨M,hM,N,U,V,hid⟩ := exists_chart_identity F G D hF hG hcop
  refine ⟨M,hM,N,?_⟩
  intro x d hdF hdG
  have he := congrArg (MvPolynomial.eval x) hid
  simp only [map_add,map_mul,map_pow,MvPolynomial.eval_C,MvPolynomial.eval_X] at he
  rw [he]
  exact dvd_add (dvd_mul_of_dvd_right hdF _) (dvd_mul_of_dvd_right hdG _)

/-- Two homogeneous integer chart identities bound common content at every
primitive pair by a fixed nonzero integer. -/
theorem exists_primitive_content_constant (F G : BinaryForm) (D : ℕ)
    (hF : F.IsHomogeneous D) (hG : G.IsHomogeneous D)
    (h0 : IsCoprime ((chart F).map (algebraMap ℤ ℚ)) ((chart G).map (algebraMap ℤ ℚ)))
    (h1 : IsCoprime ((chart (swapVariables F)).map (algebraMap ℤ ℚ))
      ((chart (swapVariables G)).map (algebraMap ℤ ℚ))) :
    ∃ M : ℤ, M≠0 ∧ ∀ x₀ x₁ : ℤ, IsCoprime x₀ x₁ → ∀ d : ℤ,
      d∣MvPolynomial.eval ![x₀,x₁] F → d∣MvPolynomial.eval ![x₀,x₁] G → d∣M := by
  obtain ⟨M0,hM0,N0,hchart0⟩ := chart_common_divisor F G D hF hG h0
  obtain ⟨M1,hM1,N1,hchart1⟩ := chart_common_divisor (swapVariables F) (swapVariables G) D
    (swapVariables_homogeneous F D hF) (swapVariables_homogeneous G D hG) h1
  refine ⟨M0*M1,mul_ne_zero hM0 hM1,?_⟩
  intro x₀ x₁ hprim d hdF hdG
  have hx1 : d∣M0*x₁^N0 := by
    simpa only [Matrix.cons_val_one,Matrix.cons_val_zero] using hchart0 ![x₀,x₁] d hdF hdG
  have hx0 : d∣M1*x₀^N1 := by
    apply hchart1 ![x₁,x₀] d
    · simpa only [eval_swapVariables] using hdF
    · simpa only [eval_swapVariables] using hdG
  have hdx0 : d∣(M0*M1)*x₀^N1 := by
    convert dvd_mul_of_dvd_right hx0 M0 using 1
    ring
  have hdx1 : d∣(M0*M1)*x₁^N0 := by
    convert dvd_mul_of_dvd_right hx1 M1 using 1
    ring
  obtain ⟨u,v,huv⟩ := (hprim.pow_left (m:=N1)).pow_right (n:=N0)
  have hd := dvd_add (dvd_mul_of_dvd_right hdx0 u) (dvd_mul_of_dvd_right hdx1 v)
  have he : u*((M0*M1)*x₀^N1)+v*((M0*M1)*x₁^N0)=M0*M1 := by
    linear_combination (M0*M1)*huv
  rwa [he] at hd

/-- A fixed nonzero integer controls every common divisor of the two
short-invariant powers at primitive integer pairs. -/
theorem actual_content_constant :
    ∃ M : ℤ, M≠0 ∧ ∀ x₀ x₁ : ℤ, IsCoprime x₀ x₁ → ∀ d : ℤ,
      d∣(-27*HeightInvariantForms.c4 x₀ x₁)^3 →
      d∣(-54*HeightInvariantForms.c6 x₀ x₁)^2 → d∣M := by
  obtain ⟨M,hM,h⟩ := exists_primitive_content_constant shortC4Cube shortC6Square 48
    shortC4Cube_homogeneous shortC6Square_homogeneous short_chart_coprime short_swapped_chart_coprime
  refine ⟨M,hM,?_⟩
  intro x₀ x₁ hprim d hd4 hd6
  apply h x₀ x₁ hprim d
  · simpa only [eval_shortC4Cube,Matrix.cons_val_zero,Matrix.cons_val_one] using hd4
  · simpa only [eval_shortC6Square,Matrix.cons_val_zero,Matrix.cons_val_one] using hd6

/-- In particular, the common divisors of the integer c4,c6 values
at primitive pairs divide a fixed nonzero integer. -/
theorem c4_c6_content_constant :
    ∃ M : ℤ, M≠0 ∧ ∀ x₀ x₁ : ℤ, IsCoprime x₀ x₁ → ∀ d : ℤ,
      d∣HeightInvariantForms.c4 x₀ x₁ → d∣HeightInvariantForms.c6 x₀ x₁ → d∣M := by
  obtain ⟨M,hM,h⟩ := actual_content_constant
  refine ⟨M,hM,?_⟩
  intro x₀ x₁ hprim d hd4 hd6
  apply h x₀ x₁ hprim d
  · simpa only [pow_one] using pow_dvd_pow_of_dvd_of_le
      (dvd_mul_of_dvd_right hd4 (-27)) (by decide : 1≤3)
  · simpa only [pow_one] using pow_dvd_pow_of_dvd_of_le
      (dvd_mul_of_dvd_right hd6 (-54)) (by decide : 1≤2)

/-- Positive natural form of the uniform invariant common-divisor bound. -/
theorem exists_invariant_content_bound :
    ∃ M : ℕ, 0<M ∧ ∀ x₀ x₁ : ℤ, Nat.Coprime x₀.natAbs x₁.natAbs → ∀ d : ℕ,
      (d:ℤ)∣HeightInvariantForms.c4 x₀ x₁ →
      (d:ℤ)∣HeightInvariantForms.c6 x₀ x₁ → d∣M := by
  obtain ⟨M,hM,h⟩ := c4_c6_content_constant
  refine ⟨M.natAbs,Int.natAbs_pos.mpr hM,?_⟩
  intro x₀ x₁ hprim d hd4 hd6
  have hd := h x₀ x₁ (Int.isCoprime_iff_nat_coprime.mpr hprim) (d:ℤ) hd4 hd6
  simpa only [Int.natAbs_natCast] using Int.natAbs_dvd_natAbs.mpr hd

/-- The twelfth power of every short-model normalization scale is
uniformly bounded on primitive integer parameter pairs. -/
theorem exists_normalization_bound :
    ∃ C : ℕ, 0<C ∧ ∀ x₀ x₁ : ℤ, Nat.Coprime x₀.natAbs x₁.natAbs → ∀ d : ℕ,
      (d:ℤ)^4∣-27*HeightInvariantForms.c4 x₀ x₁ →
      (d:ℤ)^6∣-54*HeightInvariantForms.c6 x₀ x₁ → d^12≤C := by
  obtain ⟨M,hM,h⟩ := actual_content_constant
  refine ⟨M.natAbs,Int.natAbs_pos.mpr hM,?_⟩
  intro x₀ x₁ hprim d hd4 hd6
  have he : (d:ℤ)^12∣M := by
    apply h x₀ x₁ (Int.isCoprime_iff_nat_coprime.mpr hprim)
    · simpa only [←pow_mul] using pow_dvd_pow_of_dvd hd4 3
    · simpa only [←pow_mul] using pow_dvd_pow_of_dvd hd6 2
  have hd : d^12∣M.natAbs := by
    simpa only [Int.natAbs_pow,Int.natAbs_natCast] using Int.natAbs_dvd_natAbs.mpr he
  exact Nat.le_of_dvd (Int.natAbs_pos.mpr hM) hd

end
end Z2Z4Rank6.HeightInvariantContent
