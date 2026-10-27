module

public import Z2Z4Rank6.SecondQuarticMaps
public import Z2Z4Rank6.SecondFamily

@[expose] public section

/-! Generic inverse coordinates for the second conic and quartic. -/
namespace Z2Z4Rank6
section Field
variable {K : Type*} [Field K] [CharZero K]

def secondConicTheta (s1 s2 : K) : K := s2/(s1-161/1089)

theorem secondConic_relation (s1 s2 : K) (hs : s1-161/1089≠0)
    (he : s2^2=29*(s1^2-(161/1089)^2)) :
    ((secondConicTheta s1 s2)^2-29)*(s1-161/1089)=58*(161/1089) := by
  unfold secondConicTheta
  generalize ha : (161/1089:K)=a at *
  have hq : (s2/(s1-a))^2=29*(s1+a)/(s1-a) := by
    rw [div_pow,he]
    field_simp [hs]
    ring
  rw [hq]
  field_simp [hs]
  ring

theorem secondConic_denom_ne_zero (s1 s2 : K) (hs : s1-161/1089≠0)
    (he : s2^2=29*(s1^2-(161/1089)^2)) : (secondConicTheta s1 s2)^2-29≠0 := by
  have hr := secondConic_relation s1 s2 hs he
  intro hd
  rw [hd,zero_mul] at hr
  norm_num at hr

theorem secondConic_inverse_s1 (s1 s2 : K) (hs : s1-161/1089≠0)
    (he : s2^2=29*(s1^2-(161/1089)^2)) :
    SecondFamily.thetaS1 (secondConicTheta s1 s2)=s1 := by
  have hd := secondConic_denom_ne_zero s1 s2 hs he
  unfold SecondFamily.thetaS1
  apply (div_eq_iff hd).mpr
  have hr := secondConic_relation s1 s2 hs he
  linear_combination -hr

theorem secondConic_inverse_s2 (s1 s2 : K) (hs : s1-161/1089≠0)
    (he : s2^2=29*(s1^2-(161/1089)^2)) :
    SecondFamily.thetaS2 (secondConicTheta s1 s2)=s2 := by
  unfold SecondFamily.thetaS2
  rw [secondConic_inverse_s1 s1 s2 hs he]
  unfold secondConicTheta
  exact div_mul_cancel₀ _ hs

theorem secondEta_inverse (t s3 : K) (ht : t^2-29≠0) :
    (58/1185921)*SecondFamily.thetaEta t s3/(t^2-29)=s3 := by
  unfold SecondFamily.thetaEta
  field_simp

omit [CharZero K] in
theorem secondJacobian_cubic_factor (x : K) :
    (x+102809641014)*(x-51068871386)*(x-51740769627)=
      x^3+x^2-7927479575830823114160*x+271658305399029819040875379804308 := by ring

def secondEtaToS3 (t eta : K) : K := (58/1185921)*eta/(t^2-29)

end Field
section Maps
variable {K L : Type*} [Field K] [Field L] (f : K→+*L)

theorem map_secondEtaToS3 (t eta : K) : f (secondEtaToS3 t eta)=secondEtaToS3 (f t) (f eta) := by
  simp [secondEtaToS3,map_ofNat]

theorem map_thetaS1 (t : K) : f (SecondFamily.thetaS1 t)=SecondFamily.thetaS1 (f t) := by
  simp [SecondFamily.thetaS1,map_ofNat]
theorem map_thetaS2 (t : K) : f (SecondFamily.thetaS2 t)=SecondFamily.thetaS2 (f t) := by
  simp [SecondFamily.thetaS2,map_thetaS1,map_ofNat]

end Maps
end Z2Z4Rank6
