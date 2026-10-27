module

public import Z2Z4Rank6.SecondFunctionFieldCopy
public import Z2Z4Rank6.SecondFunctionFieldLocal
public import Z2Z4Rank6.SecondQuarticForward
public import Z2Z4Rank6.SecondLocalMaps
public import Z2Z4Rank6.SecondBaseFunctionFieldCoordinates
public import Z2Z4Rank6.LaurentConstantSquares
public import Mathlib.FieldTheory.AlgebraicClosure

@[expose] public section

/-!
# Printed J2 coordinates generating the degree-eight field Q(G2)

The conic inverse produces theta and eta inside the existing three-step
quadratic field. The pointed-quartic formulas then produce x,y on the printed
J2 cubic and recover all four G2 coordinates.
-/
namespace Z2Z4Rank6
noncomputable section
set_option maxHeartbeats 500000
set_option maxRecDepth 4096

section Membership
variable {L : Type*} [Field L] [Algebra ℚ L]
private theorem thetaS1_mem (S : IntermediateField ℚ L) (t : L) (ht : t∈S) : SecondFamily.thetaS1 t∈S := by
  let ts : S := ⟨t,ht⟩
  exact (map_thetaS1 S.toSubfield.subtype ts) ▸ (SecondFamily.thetaS1 ts).property
private theorem thetaS2_mem (S : IntermediateField ℚ L) (t : L) (ht : t∈S) : SecondFamily.thetaS2 t∈S := by
  let ts : S := ⟨t,ht⟩
  exact (map_thetaS2 S.toSubfield.subtype ts) ▸ (SecondFamily.thetaS2 ts).property
private theorem etaToS3_mem (S : IntermediateField ℚ L) (t z : L) (ht : t∈S) (hz : z∈S) : secondEtaToS3 t z∈S := by
  let ts : S := ⟨t,ht⟩
  let zs : S := ⟨z,hz⟩
  exact (map_secondEtaToS3 S.toSubfield.subtype ts zs) ▸ (secondEtaToS3 ts zs).property
private theorem secondTheta_mem (S : IntermediateField ℚ L) (x y : L) (hx : x∈S) (hy : y∈S) : secondQuarticTheta x y∈S := by
  let xs : S := ⟨x,hx⟩
  let ys : S := ⟨y,hy⟩
  exact (map_secondQuarticTheta S.toSubfield.subtype xs ys) ▸ (secondQuarticTheta xs ys).property
private theorem secondEta_mem (S : IntermediateField ℚ L) (x y : L) (hx : x∈S) (hy : y∈S) : secondQuarticEta x y∈S := by
  let xs : S := ⟨x,hx⟩
  let ys : S := ⟨y,hy⟩
  exact (map_secondQuarticEta S.toSubfield.subtype xs ys) ▸ (secondQuarticEta xs ys).property
end Membership

namespace SecondBaseFunctionFieldIso
open SecondFamily
abbrev K := SecondFunctionFieldCopy.K
local instance secondBaseIsoDecidableEq : DecidableEq K := Classical.decEq _
abbrev baseW : K := SecondFunctionFieldCopy.W
abbrev baseS1 : K := SecondFunctionFieldCopy.s1
abbrev baseS2 : K := SecondFunctionFieldCopy.s2
abbrev baseS3 : K := SecondFunctionFieldCopy.s3

theorem baseS1_sq : baseS1^2=baseW := SecondFunctionFieldCopy.s1_sq
theorem baseS2_sq : baseS2^2=qA baseW := SecondFunctionFieldCopy.s2_sq
theorem baseS3_sq : baseS3^2=qB baseW := SecondFunctionFieldCopy.s3_sq
theorem baseW_transcendental : Transcendental ℚ baseW := SecondFunctionFieldCopy.W_transcendental

theorem baseW_ne_rational (r : ℚ) : baseW≠algebraMap ℚ K r := by
  intro h
  apply baseW_transcendental
  rw [h]
  exact isAlgebraic_algebraMap _

theorem baseCoordinates_generate : IntermediateField.adjoin ℚ
    ({baseW,baseS1,baseS2,baseS3}:Set K)=⊤ :=
  SecondFunctionFieldCopy.field_adjoin_coordinates_eq_top

@[irreducible] def theta : K := secondConicTheta baseS1 baseS2
@[irreducible] def eta : K := thetaEta theta baseS3

theorem s1_sub_base_ne_zero : baseS1-161/1089≠0 := by
  intro hs
  have h1 : baseS1=161/1089 := sub_eq_zero.mp hs
  have hw : baseW=(beta:K) := by
    rw [←baseS1_sq,h1]
    rfl
  exact baseW_ne_rational (beta:ℚ)
    (hw.trans (SecondFunctionField.map_beta (algebraMap ℚ K)).symm)

theorem conic_equation : baseS2^2=
    29*(baseS1^2-(161/1089)^2) := by
  have he := baseS2_sq
  rw [←baseS1_sq] at he
  exact he

theorem theta_den_ne_zero : theta^2-29≠0 := by
  unfold theta
  exact secondConic_denom_ne_zero _ _ s1_sub_base_ne_zero conic_equation

theorem s1_recover : thetaS1 theta=baseS1 := by
  unfold theta
  exact secondConic_inverse_s1 _ _ s1_sub_base_ne_zero conic_equation

theorem s2_recover : thetaS2 theta=baseS2 := by
  unfold theta
  exact secondConic_inverse_s2 _ _ s1_sub_base_ne_zero conic_equation

theorem W_recover : (thetaS1 theta)^2=baseW := by
  rw [s1_recover,baseS1_sq]

theorem eta_formula : thetaEta theta baseS3=eta := by unfold eta; rfl

theorem quartic_equation : eta^2=secondQuartic theta := by
  have hB : baseS3^2=qB ((thetaS1 theta)^2) := by
    rw [W_recover]
    exact baseS3_sq
  have he := (theta_third_iff_quartic theta baseS3 theta_den_ne_zero).mp hB
  have hq : thetaQuartic theta=secondQuartic theta := rfl
  rw [eta_formula,hq] at he
  exact he

theorem s3_recover : secondEtaToS3 theta eta=baseS3 := by
  have he := secondEta_inverse theta baseS3 theta_den_ne_zero
  rw [eta_formula] at he
  exact he

theorem theta_transcendental : Transcendental ℚ theta := by
  intro ht
  let S := algebraicClosure ℚ K
  have htS : theta∈S := mem_algebraicClosure_iff.mpr ht
  have h1 := thetaS1_mem S theta htS
  have hW : (thetaS1 theta)^2∈S := pow_mem h1 2
  rw [W_recover] at hW
  exact baseW_transcendental (mem_algebraicClosure_iff.mp hW)

theorem theta_sub_base_ne_zero : theta-10/3≠0 := by
  intro h
  have he : theta=10/3 := sub_eq_zero.mp h
  apply theta_transcendental
  rw [he]
  have hr : IsAlgebraic ℚ (algebraMap ℚ K (10/3)) := isAlgebraic_algebraMap _
  simpa only [map_div₀,map_ofNat] using hr

theorem leading_nonsquare : ¬IsSquare (secondQuarticA:K) := by
  change ¬IsSquare (1326538900:K)
  simpa only [Rat.cast_ofNat] using
    (not_isSquare_ratCast_of_laurent_embedding
      (SecondFunctionFieldLocal.embedding.comp SecondFunctionFieldCopy.equiv.toRingHom)
      (1326538900:ℚ) (by norm_num))

theorem forward_den_ne_zero : pointedInverseDen secondQuarticA secondQuarticQ
    (pointedForwardX secondQuarticD secondQuarticQ (theta-10/3) eta)≠0 :=
  pointed_inverse_den_ne_zero _ _ _ secondQuartic_q_ne_zero leading_nonsquare

@[irreducible] def x : K := secondQuarticRecoverX theta eta
@[irreducible] def y : K := secondQuarticRecoverY theta eta

theorem x_formula : secondQuarticRecoverX theta eta=x := by unfold x; rfl
theorem y_formula : secondQuarticRecoverY theta eta=y := by unfold y; rfl

theorem equation_factor : y^2=(x+102809641014)*(x-51068871386)*(x-51740769627) := by
  have he := secondQuartic_forward_equation theta eta theta_sub_base_ne_zero quartic_equation
  rw [x_formula,y_formula] at he
  exact he

theorem equation : y^2=x^3+x^2-7927479575830823114160*x+271658305399029819040875379804308 := by
  have he := equation_factor
  rw [secondJacobian_cubic_factor] at he
  exact he

theorem theta_recover : secondQuarticTheta x y=theta := by
  have he := secondQuartic_forward_inverse_Theta theta eta forward_den_ne_zero
  rw [x_formula,y_formula] at he
  exact he

theorem eta_recover : secondQuarticEta x y=eta := by
  have he := secondQuartic_forward_inverse_Eta theta eta theta_sub_base_ne_zero forward_den_ne_zero
  rw [x_formula,y_formula] at he
  exact he

theorem x_transcendental : Transcendental ℚ x := by
  intro hx
  have hy2 : IsAlgebraic ℚ (y^2) := by
    rw [equation_factor]
    exact ((hx.add (isAlgebraic_natCast 102809641014)).mul
      (hx.sub (isAlgebraic_natCast 51068871386))).mul (hx.sub (isAlgebraic_natCast 51740769627))
  have hy : IsAlgebraic ℚ y := hy2.of_pow (by decide : 0<(2:ℕ))
  let S := algebraicClosure ℚ K
  have hxS : x∈S := mem_algebraicClosure_iff.mpr hx
  have hyS : y∈S := mem_algebraicClosure_iff.mpr hy
  have htS := secondTheta_mem S x y hxS hyS
  rw [theta_recover] at htS
  exact theta_transcendental (mem_algebraicClosure_iff.mp htS)

theorem field_adjoin_coordinates_eq_top : IntermediateField.adjoin ℚ ({x,y}:Set K)=⊤ := by
  let S := IntermediateField.adjoin ℚ ({x,y}:Set K)
  have hxS : x∈S := IntermediateField.subset_adjoin _ _ (by simp)
  have hyS : y∈S := IntermediateField.subset_adjoin _ _ (by simp)
  have htS := secondTheta_mem S x y hxS hyS
  have heS := secondEta_mem S x y hxS hyS
  rw [theta_recover] at htS
  rw [eta_recover] at heS
  have h1 := thetaS1_mem S theta htS
  have h2 := thetaS2_mem S theta htS
  have h3 := etaToS3_mem S theta eta htS heS
  have hW : (thetaS1 theta)^2∈S := pow_mem h1 2
  rw [W_recover] at hW
  rw [s1_recover] at h1
  rw [s2_recover] at h2
  rw [s3_recover] at h3
  have hle : IntermediateField.adjoin ℚ
      ({baseW,baseS1,baseS2,baseS3}:Set K)≤S := by
    apply IntermediateField.adjoin_le_iff.mpr
    intro z hz
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact hW
    · exact h1
    · exact h2
    · exact h3
  rw [baseCoordinates_generate] at hle
  exact top_unique hle

end SecondBaseFunctionFieldIso
end
end Z2Z4Rank6
