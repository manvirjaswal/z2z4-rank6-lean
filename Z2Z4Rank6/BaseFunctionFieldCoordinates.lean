module

public import Z2Z4Rank6.Quartic

@[expose] public section

/-!
# Two-sided conic and quartic coordinates over characteristic-zero fields

These generic field identities support the function-field isomorphism
in Lemma 4.1(a), DOI 10.5281/zenodo.23437117. All denominators are displayed.
-/
namespace Z2Z4Rank6
section Field
variable {K : Type*} [Field K] [CharZero K]

def baseConicK (m u : K) : K := (u-35)/(m-1)
def baseConicEta (m u v : K) : K := v*((baseConicK m u)^2-15)/5

omit [CharZero K] in
theorem baseConic_line (m u : K) (hm : m-1≠0) :
    u=35+baseConicK m u*(m-1) := by
  unfold baseConicK
  field_simp
  ring

omit [CharZero K] in
theorem baseConic_relation (m u : K) (hm : m-1≠0) (hu : u^2=5*(3*m^2+242)) :
    ((baseConicK m u)^2-15)*m=(baseConicK m u)^2-70*baseConicK m u+15 := by
  let k := baseConicK m u
  have he := baseConic_line m u hm
  change u=35+k*(m-1) at he
  rw [he] at hu
  have hp : (m-1)*((k^2-15)*m-(k^2-70*k+15))=0 := by
    linear_combination hu
  exact sub_eq_zero.mp ((mul_eq_zero.mp hp).resolve_left hm)

theorem baseConic_denom_ne_zero (m u : K) (hm : m-1≠0)
    (hu : u^2=5*(3*m^2+242)) : (baseConicK m u)^2-15≠0 := by
  have hr := baseConic_relation m u hm hu
  intro hd
  rw [hd,zero_mul] at hr
  have hk : baseConicK m u=3/7 := by
    linear_combination (1/70:K)*(hd+hr)
  rw [hk] at hd
  norm_num at hd

theorem baseConic_inverse_M (m u : K) (hm : m-1≠0) (hu : u^2=5*(3*m^2+242)) :
    conicM (baseConicK m u)=m := by
  unfold conicM
  apply (div_eq_iff (baseConic_denom_ne_zero m u hm hu)).mpr
  simpa only [mul_comm] using (baseConic_relation m u hm hu).symm

theorem baseConic_inverse_U (m u : K) (hm : m-1≠0) (hu : u^2=5*(3*m^2+242)) :
    conicU (baseConicK m u)=u := by
  rw [conic_line _ (baseConic_denom_ne_zero m u hm hu),baseConic_inverse_M m u hm hu]
  exact (baseConic_line m u hm).symm

theorem baseConic_inverse_V (m u v : K) (hm : m-1≠0) (hu : u^2=5*(3*m^2+242)) :
    conicV (baseConicK m u) (baseConicEta m u v)=v := by
  have hd := baseConic_denom_ne_zero m u hm hu
  unfold conicV baseConicEta
  field_simp

theorem baseConic_quartic_equation (m u v : K) (hm : m-1≠0)
    (hu : u^2=5*(3*m^2+242)) (hv : v^2=5*(2*m^2+243)) :
    (baseConicEta m u v)^2=quartic (baseConicK m u) := by
  have hd := baseConic_denom_ne_zero m u hm hu
  rw [←baseConic_inverse_M m u hm hu] at hv
  unfold conicM at hv
  have he : v^2*((baseConicK m u)^2-15)^2=25*quartic (baseConicK m u) := by
    rw [hv]
    have hi := quartic_conic_identity (baseConicK m u)
    field_simp at hi ⊢
    exact hi
  unfold baseConicEta
  field_simp
  linear_combination he

theorem quartic_ec_k_inverse (k eta : K) (hx : quarticX k eta+82≠0) :
    ecToK (quarticX k eta) (quarticY k eta)=k := by
  unfold ecToK quarticY
  field_simp
  ring

theorem quartic_ec_eta_inverse (k eta : K) (hx : quarticX k eta+82≠0) :
    ecToEta (quarticX k eta) (quarticY k eta)=eta := by
  unfold ecToEta
  rw [quartic_ec_k_inverse k eta hx]
  unfold quarticX
  field_simp
  ring

theorem quarticX_bad_parameter (k eta : K) (he : eta^2=quartic k)
    (hx : quarticX k eta+82=0) : k=123/7 := by
  have hl : 7*eta+49*k^2-28*k+249=0 := by
    unfold quarticX at hx
    linear_combination 2*hx
  unfold quartic at he
  linear_combination -(1/(3888*7):K)*((7*eta-49*k^2+28*k-249)*hl-49*he)

end Field
section Naturality
variable {K L : Type*} [Field K] [Field L] (f : K→+*L)

theorem map_conicM (k : K) : f (conicM k)=conicM (f k) := by
  simp [conicM,map_ofNat]
theorem map_conicU (k : K) : f (conicU k)=conicU (f k) := by
  simp [conicU,map_ofNat]
theorem map_conicV (k eta : K) : f (conicV k eta)=conicV (f k) (f eta) := by
  simp [conicV,map_ofNat]
theorem map_quarticX (k eta : K) : f (quarticX k eta)=quarticX (f k) (f eta) := by
  simp [quarticX,map_ofNat]
theorem map_quarticY (k eta : K) : f (quarticY k eta)=quarticY (f k) (f eta) := by
  simp [quarticY,map_quarticX,map_ofNat]
theorem map_ecToK (x y : K) : f (ecToK x y)=ecToK (f x) (f y) := by
  simp [ecToK,map_ofNat]
theorem map_ecToEta (x y : K) : f (ecToEta x y)=ecToEta (f x) (f y) := by
  simp [ecToEta,map_ecToK,map_ofNat]

end Naturality
end Z2Z4Rank6
