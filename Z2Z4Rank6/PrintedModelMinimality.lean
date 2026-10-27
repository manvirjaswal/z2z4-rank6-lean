import Z2Z4Rank6.MinimalitySmallDiscriminant
import Z2Z4Rank6.MinimalityTwoAdic
import Z2Z4Rank6.GJacobianBasic
import Z2Z4Rank6.SecondJacobianBasic

/-!
# Arithmetic minimality of the printed rational equations

The integral equations EC,JG,J2 are the equations printed in Jaswal,
DOI 10.5281/zenodo.23437117, Lemma 4.1 and Propositions 7.2/8.1. Integer
Bezout and discriminant certificates are checked in the kernel. Odd-prime
minimality follows from gcd(c₄,Δ)=16. The two-adic discriminant criterion
checks EC and JG; a proved two-adic invariant obstruction checks J2.
-/
namespace Z2Z4Rank6.PrintedModelMinimality
open WeierstrassCurve WithZero Multiplicative
open IsDiscreteValuationRing IsDedekindDomain.HeightOneSpectrum
open MinimalitySmallDiscriminant
noncomputable section

def integerModel (i : Fin 3) : WeierstrassCurve ℤ where
  a₁ := 0
  a₂ := 1
  a₃ := 0
  a₄ := ![-137620,-26097400,-7927479575830823114160] i
  a₆ := ![-10504000,38851416548,271658305399029819040875379804308] i

def rationalModel : Fin 3 → WeierstrassCurve ℚ := ![EC,JG,J2]

def bezout : Fin 3 → ℤ×ℤ :=
  ![(1212977069605141,-67016),
    (-6120999260472842092199,15803464),
    (72655637489640826298085128382521986760623432521241360964935921,-6767408787153011765281)]

def twoExponent : Fin 3 → ℕ := ![8,10,12]
def oddDiscriminant : Fin 3 → ℤ :=
  ![467044181552025,473814736540703105625,
    997386137939924199105447445545086019388565194519883057450625]

theorem integerModel_map (i : Fin 3) :
    (integerModel i).map (Int.castRingHom ℚ)=rationalModel i := by
  fin_cases i <;> ext <;> norm_num [integerModel,rationalModel,EC,JG,J2]

/-- Exact Bezout certificate for all three printed invariant pairs. -/
theorem invariant_bezout (i : Fin 3) :
    (bezout i).1*(integerModel i).c₄+(bezout i).2*(integerModel i).Δ=16 := by
  fin_cases i <;> norm_num [bezout,integerModel,WeierstrassCurve.c₄,WeierstrassCurve.Δ,
    WeierstrassCurve.b₂,WeierstrassCurve.b₄,WeierstrassCurve.b₆,WeierstrassCurve.b₈]

theorem discriminant_two_factorization (i : Fin 3) :
    (integerModel i).Δ=2^(twoExponent i)*oddDiscriminant i := by
  fin_cases i <;> norm_num [integerModel,twoExponent,oddDiscriminant,WeierstrassCurve.Δ,
    WeierstrassCurve.b₂,WeierstrassCurve.b₄,WeierstrassCurve.b₆,WeierstrassCurve.b₈]

theorem oddDiscriminant_odd (i : Fin 3) : ¬(2:ℤ)∣oddDiscriminant i := by
  fin_cases i <;> norm_num [oddDiscriminant]

def localModel (i : Fin 3) (p : ℕ) [Fact p.Prime] : WeierstrassCurve (Padic p) :=
  ((integerModel i).map (Int.castRingHom (PadicInt p))).baseChange (Padic p)

theorem localModel_eq (i : Fin 3) (p : ℕ) [Fact p.Prime] :
    localModel i p=(rationalModel i).map (Rat.castHom (Padic p)) := by
  fin_cases i <;> ext <;> norm_num [localModel,integerModel,rationalModel,EC,JG,J2,
    WeierstrassCurve.baseChange,PadicInt.coe_natCast,PadicInt.coe_intCast]
  all_goals norm_cast

private theorem coprime_of_unit_combination {R : Type*} [CommRing R]
    (a b r s n : R) (h : r*a+s*b=n) (hu : IsUnit n) : IsCoprime a b := by
  obtain ⟨u,rfl⟩ := hu
  refine ⟨((u⁻¹:Rˣ):R)*r,((u⁻¹:Rˣ):R)*s,?_⟩
  calc
    _=((u⁻¹:Rˣ):R)*(r*a+s*b) := by ring
    _=((u⁻¹:Rˣ):R)*(u:R) := by rw [h]
    _=1 := Units.inv_mul u

/-- All three integral equations are minimal at every odd rational prime. -/
theorem minimal_at_odd_prime (i : Fin 3) (p : ℕ) [hp : Fact p.Prime] (hodd : p≠2) :
    IsMinimal (PadicInt p) ((rationalModel i).map (Rat.castHom (Padic p))) := by
  have hnp : ¬(p:ℤ)∣(2:ℤ) := by
    intro h
    have hn : p∣2 := by exact_mod_cast h
    have hle := Nat.le_of_dvd (by decide : 0<2) hn
    have hge := hp.out.two_le
    exact hodd (by omega)
  have hu2 := padicInt_isUnit_intCast p 2 hnp
  have hu16 : IsUnit (16 : PadicInt p) := by convert hu2.pow 4 using 1; norm_num
  let V : WeierstrassCurve (PadicInt p) := (integerModel i).map (Int.castRingHom (PadicInt p))
  have hbez : ((bezout i).1 : PadicInt p)*V.c₄+((bezout i).2 : PadicInt p)*V.Δ=16 := by
    have h := congrArg (Int.castRingHom (PadicInt p)) (invariant_bezout i)
    simpa only [map_add,map_mul,map_ofNat,V,WeierstrassCurve.map_c₄,WeierstrassCurve.map_Δ,Int.coe_castRingHom] using h
  have hc := coprime_of_unit_combination _ _ _ _ _ hbez hu16
  have hm := Minimality.baseChange_isMinimal_of_isCoprime (K:=Padic p) (PadicInt p) V hc
  rw [←localModel_eq]
  exact hm

local instance printedMinimalPrimeTwo : Fact (Nat.Prime 2) := ⟨by decide⟩

/-- Direct normalized DVR discriminant values, computed from integer
factorizations rather than a real-norm comparison. -/
theorem discriminant_value_two (i : Fin 3) :
    valuation (Padic 2) (maximalIdeal (PadicInt 2)) (localModel i 2).Δ=
      exp (-(twoExponent i : ℤ)) := by
  have hv := padic_integer_value 2 (twoExponent i) (oddDiscriminant i) (oddDiscriminant_odd i)
  have hcast := congrArg (Int.castRingHom (Padic 2)) (discriminant_two_factorization i)
  simp only [map_mul,map_pow,map_ofNat,Int.coe_castRingHom] at hcast
  norm_num only at hv
  rw [←hcast] at hv
  simpa only [localModel,WeierstrassCurve.baseChange,WeierstrassCurve.map_Δ,Int.coe_castRingHom,map_intCast] using hv

/-- EC and JG are minimal at two because their discriminant valuations 8
and 10 are strictly less than twelve. -/
theorem minimal_at_two_of_small_exponent (i : Fin 3) (hi : twoExponent i<12) :
    IsMinimal (PadicInt 2) ((rationalModel i).map (Rat.castHom (Padic 2))) := by
  let V : WeierstrassCurve (PadicInt 2) := (integerModel i).map (Int.castRingHom (PadicInt 2))
  let : IsIntegral (PadicInt 2) (localModel i 2) := ⟨V,rfl⟩
  rw [←localModel_eq]
  apply isMinimal_of_discriminant_gt
  rw [discriminant_value_two,exp_lt_exp]
  have hiZ : (twoExponent i : ℤ)<12 := by exact_mod_cast hi
  omega

/-- The printed EC equation is minimal at every rational prime. -/
theorem ec_minimal (p : ℕ) [Fact p.Prime] :
    IsMinimal (PadicInt p) (EC.map (Rat.castHom (Padic p))) := by
  by_cases hp : p=2
  · subst p
    exact minimal_at_two_of_small_exponent 0 (by decide)
  · exact minimal_at_odd_prime 0 p hp

/-- The printed JG equation is minimal at every rational prime. -/
theorem jg_minimal (p : ℕ) [Fact p.Prime] :
    IsMinimal (PadicInt p) (JG.map (Rat.castHom (Padic p))) := by
  by_cases hp : p=2
  · subst p
    exact minimal_at_two_of_small_exponent 1 (by decide)
  · exact minimal_at_odd_prime 1 p hp

/-- The normalized invariants of the printed J2 equation give the
two-adic obstruction to a smaller integral equation. -/
theorem j2_minimal_at_two :
    IsMinimal (PadicInt 2) (J2.map (Rat.castHom (Padic 2))) := by
  let A : ℤ := 23782438727492469342481
  let B : ℤ := -3667387122922576215143056331371879
  let V : WeierstrassCurve (PadicInt 2) :=
    (integerModel 2).map (Int.castRingHom (PadicInt 2))
  have hA : IsUnit (A : PadicInt 2) :=
    padicInt_isUnit_intCast 2 A (by norm_num [A])
  have h4Z : (integerModel 2).c₄=16*A := by
    norm_num [A,integerModel,WeierstrassCurve.c₄,WeierstrassCurve.b₂,WeierstrassCurve.b₄]
  have h6Z : (integerModel 2).c₆=64*B := by
    norm_num [B,integerModel,WeierstrassCurve.c₆,WeierstrassCurve.b₂,
      WeierstrassCurve.b₄,WeierstrassCurve.b₆]
  have h4 : V.c₄=16*(A : PadicInt 2) := by
    have h := congrArg (Int.castRingHom (PadicInt 2)) h4Z
    simpa only [V,WeierstrassCurve.map_c₄,map_mul,map_ofNat,Int.coe_castRingHom] using h
  have h6 : V.c₆=64*(B : PadicInt 2) := by
    have h := congrArg (Int.castRingHom (PadicInt 2)) h6Z
    simpa only [V,WeierstrassCurve.map_c₆,map_mul,map_ofNat,Int.coe_castRingHom] using h
  have hB : PadicInt.toZModPow 2 (B : PadicInt 2)=1 := by
    simp only [map_intCast]
    decide +kernel
  have h := MinimalityTwoAdic.isMinimal_of_normalized_c4_c6 V _ _ hA h4 h6 hB
  change IsMinimal (PadicInt 2) (localModel 2 2) at h
  simpa [localModel_eq,rationalModel] using h

/-- The printed J2 equation is minimal at every rational prime. -/
theorem j2_minimal (p : ℕ) [Fact p.Prime] :
    IsMinimal (PadicInt p) (J2.map (Rat.castHom (Padic p))) := by
  by_cases hp : p=2
  · subst p
    exact j2_minimal_at_two
  · exact minimal_at_odd_prime 2 p hp

/-- Global minimality is local Mathlib minimality at every prime. -/
def GlobalMinimal (W : WeierstrassCurve ℚ) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], IsMinimal (PadicInt p) (W.map (Rat.castHom (Padic p)))

theorem ec_global_minimal : GlobalMinimal EC := ec_minimal
theorem jg_global_minimal : GlobalMinimal JG := jg_minimal
theorem j2_global_minimal : GlobalMinimal J2 := j2_minimal

end
end Z2Z4Rank6.PrintedModelMinimality
