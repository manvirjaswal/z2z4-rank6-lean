module

public import Z2Z4Rank6.MinimalitySmallDiscriminant
public import Mathlib.NumberTheory.Padics.RingHoms

@[expose] public section

/-!
# A two-adic invariant obstruction to lowering an integral equation

If c₄=16A with A a two-adic unit and c₆=64B with B≡1(mod 4),
the equation is minimal. Any improving scale must be twice-inverse times
a unit. Its resulting c₄ would be a unit, forcing c₆≡−1(mod 4), whereas
its transformed c₆ is congruent to 1. All reductions use
p-adic integers and their ZModPow map.
-/
namespace Z2Z4Rank6.MinimalityTwoAdic
open WeierstrassCurve WithZero Multiplicative
open IsDiscreteValuationRing IsDedekindDomain.HeightOneSpectrum
open MinimalitySmallDiscriminant
noncomputable section
local instance minimalityTwoAdicPrimeTwo : Fact (Nat.Prime 2) := ⟨by decide⟩

abbrev R := PadicInt 2
abbrev K := Padic 2
abbrev val : Valuation K ℤᵐ⁰ := valuation K (maximalIdeal R)

theorem unit_sixth_mod_four (u : (ZMod 4)ˣ) : (u : ZMod 4)^6=1 := by
  exact (by decide +kernel : ∀ t : (ZMod 4)ˣ,(t : ZMod 4)^6=1) u

/-- For any integral Weierstrass model with odd c₄, its c₆ is 3 mod 4. -/
theorem c6_mod_four_of_unit_c4 (V : WeierstrassCurve (ZMod 4))
    (hunit : IsUnit V.c₄) : V.c₆=3 := by
  have h4 : V.c₄=V.a₁^4 := by
    have h40 : (4 : ZMod 4)=0 := by decide +kernel
    have h240 : (24 : ZMod 4)=0 := by decide +kernel
    simp only [WeierstrassCurve.c₄,WeierstrassCurve.b₂,h40,h240,zero_mul,add_zero,sub_zero]
    ring
  have h6 : V.c₆= -V.a₁^6 := by
    have h40 : (4 : ZMod 4)=0 := by decide +kernel
    have h360 : (36 : ZMod 4)=0 := by decide +kernel
    have h2160 : (216 : ZMod 4)=0 := by decide +kernel
    simp only [WeierstrassCurve.c₆,WeierstrassCurve.b₂,h40,h360,h2160,zero_mul,add_zero,sub_zero]
    ring
  have ha4 : IsUnit (V.a₁^3*V.a₁) := by
    rw [←pow_succ]
    exact h4 ▸ hunit
  obtain ⟨u,hu⟩ := isUnit_of_mul_isUnit_right ha4
  rw [h6,←hu,unit_sixth_mod_four]
  decide +kernel

/-- Normalized DVR integrality provides an element of the base ring. -/
theorem exists_integral_of_value_le_one (x : K) (hx : val x≤1) :
    ∃ a : R,algebraMap R K a=x := by
  obtain ⟨n,d,hd⟩ := (maximalIdeal R).exists_primeCompl_mul_eq_of_integer x hx
  obtain ⟨u,hu⟩ := IsLocalRing.notMem_maximalIdeal.mp d.property
  refine ⟨n*((u⁻¹:Rˣ):R),?_⟩
  calc
    algebraMap R K (n*((u⁻¹:Rˣ):R))=
        algebraMap R K n*algebraMap R K ((u⁻¹:Rˣ):R) := map_mul _ _ _
    _=x*algebraMap R K (d:R)*algebraMap R K ((u⁻¹:Rˣ):R) := by rw [hd]
    _=x := by rw [mul_assoc,←map_mul,←hu,Units.mul_inv,map_one,mul_one]

theorem unit_of_value_one (a : R) (ha : val (algebraMap R K a)=1) : IsUnit a :=
  IsLocalRing.notMem_maximalIdeal.mp ((valuation_eq_one_iff_notMem (K:=K) (v:=maximalIdeal R)).mp ha)

private theorem value_eq_exp_one {a : ℤᵐ⁰} (ha : 1<a)
    (hb : a^4*exp (-4 : ℤ)≤1) : a=exp (1:ℤ) := by
  induction a using WithZero.expRecOn with
  | zero => simp at ha
  | exp n =>
    have hn0 : 0<n := one_lt_exp_iff.mp ha
    rw [←exp_nsmul,←exp_add,exp_le_one_iff] at hb
    simp only [nsmul_eq_mul] at hb
    have hn : n=1 := by omega
    subst n
    rfl

/-- Generic invariant criterion proving minimality at two. -/
theorem isMinimal_of_normalized_c4_c6
    (V : WeierstrassCurve R) (A B : R) (hA : IsUnit A)
    (h4 : V.c₄=16*A) (h6 : V.c₆=64*B)
    (hB : PadicInt.toZModPow 2 B=1) : IsMinimal R (V.baseChange K) := by
  let W : WeierstrassCurve K := V.baseChange K
  let : IsIntegral R W := ⟨V,rfl⟩
  have hvA := valuation_unit (K:=K) R A hA
  have hv2 : val (2:K)=exp (-1:ℤ) := by
    simpa only [val,Nat.cast_ofNat] using padic_uniformizer_value 2
  have hw4 : W.c₄=(2:K)^4*algebraMap R K A := by
    simp only [W,WeierstrassCurve.baseChange,WeierstrassCurve.map_c₄,h4,map_mul,map_ofNat]
    norm_num
  have hw6 : W.c₆=(2:K)^6*algebraMap R K B := by
    simp only [W,WeierstrassCurve.baseChange,WeierstrassCurve.map_c₆,h6,map_mul,map_ofNat]
    norm_num
  have hv4 : val W.c₄=exp (-4 : ℤ) := by
    rw [hw4,map_mul,map_pow,hv2,hvA,mul_one,←exp_nsmul]
    norm_num
  refine ⟨⟨by simpa only [one_smul] using (inferInstance : IsIntegral R W),?_⟩⟩
  intro C hC _
  let : IsIntegral R (C • W) := hC
  have hu : val ((C.u⁻¹ : Kˣ) : K)≤1 := by
    by_contra hle
    have hu1 : 1<val ((C.u⁻¹ : Kˣ) : K) := lt_of_not_ge hle
    have hint4 : val (C • W).c₄≤1 := by
      rw [←integralModel_c₄_eq R (C • W)]
      exact valuation_le_one (maximalIdeal R) _
    rw [variableChange_c₄,map_mul,map_pow,hv4] at hint4
    have hscale := value_eq_exp_one hu1 hint4
    have htval : val ((2:K)*((C.u⁻¹ : Kˣ):K))=1 := by
      rw [map_mul,hv2,hscale,←exp_add]
      norm_num
    obtain ⟨t,ht⟩ := exists_integral_of_value_le_one _ htval.le
    have htunit := unit_of_value_one t (by rw [ht];exact htval)
    let V' := integralModel R (C • W)
    have h4unit : IsUnit V'.c₄ := by
      apply unit_of_value_one
      rw [integralModel_c₄_eq R (C • W),variableChange_c₄,map_mul,map_pow,hv4,hscale,←exp_nsmul,←exp_add]
      norm_num
    have h6eq : V'.c₆=t^6*B := by
      apply IsFractionRing.injective R K
      rw [map_mul,map_pow,ht,integralModel_c₆_eq R (C • W),variableChange_c₆,hw6]
      ring
    let f : R →+* ZMod 4 := PadicInt.toZModPow 2
    have hlow : f V'.c₆=3 := by
      have h := c6_mod_four_of_unit_c4 (V'.map f) (by simpa only [map_c₄] using h4unit.map f)
      simpa only [map_c₆] using h
    have hhigh : f V'.c₆=1 := by
      rw [h6eq,map_mul,map_pow]
      obtain ⟨u,hu⟩ := htunit.map f
      rw [←hu,unit_sixth_mod_four]
      simpa only [one_mul,f] using hB
    have hbad : (1 : ZMod 4)=3 := hhigh.symm.trans hlow
    exact (by decide +kernel : (1 : ZMod 4)≠3) hbad
  change (valuation_Δ_aux R (C • W) : ℤᵐ⁰)≤(valuation_Δ_aux R (1 • W) : ℤᵐ⁰)
  rw [one_smul,valuation_Δ_aux_eq_of_isIntegral,valuation_Δ_aux_eq_of_isIntegral,
    variableChange_Δ,map_mul,map_pow]
  exact mul_le_of_le_one_left zero_le (pow_le_one₀ zero_le hu)

end
end Z2Z4Rank6.MinimalityTwoAdic
