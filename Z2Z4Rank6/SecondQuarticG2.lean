module

public import Z2Z4Rank6.SecondQuarticMaps
public import Z2Z4Rank6.SecondFamily

@[expose] public section

/-!
# Infinite rational points on the second base G2

The checked quartic points map injectively to the three printed square
equations of G2 through the paper's conic parametrization. Combined with the explicit cofinite
inverse from J2, this proves rational infinitude.
-/
namespace Z2Z4Rank6

theorem secondQuartic_theta_denom (theta:ℚ):theta^2-29≠0 := by
  intro h
  have hn:¬IsSquare (29:ℚ) := by norm_num
  apply hn
  exact ⟨theta,by nlinarith⟩

def secondQuarticS3 (P:SecondQuarticPoint):ℚ :=
  (58/1185921)*P.eta/(P.theta^2-29)

theorem secondQuartic_eta_recover(P:SecondQuarticPoint):
    SecondFamily.thetaEta P.theta (secondQuarticS3 P)=P.eta := by
  have hd:=secondQuartic_theta_denom P.theta
  norm_num [SecondFamily.thetaEta,secondQuarticS3]
  field_simp

def secondQuarticToG2(P:SecondQuarticPoint):SecondFamily.G2Point ℚ :=
  SecondFamily.thetaG2Point P.theta (secondQuarticS3 P) (secondQuartic_theta_denom P.theta)
    (by rw [secondQuartic_eta_recover];exact P.equation)

theorem secondQuartic_thetaS1_sub_base_ne_zero(theta:ℚ):
    SecondFamily.thetaS1 theta-161/1089≠0 := by
  have hd:=secondQuartic_theta_denom theta
  have he:(SecondFamily.thetaS1 theta-161/1089)*(theta^2-29)=(161/1089)*58 := by
    norm_num [SecondFamily.thetaS1]
    field_simp
    ring
  intro h
  rw [h,zero_mul] at he
  norm_num at he

theorem secondQuartic_theta_recover(P:SecondQuarticPoint):
    (secondQuarticToG2 P).s2/((secondQuarticToG2 P).s1-161/1089)=P.theta := by
  have hd:=secondQuartic_thetaS1_sub_base_ne_zero P.theta
  change SecondFamily.thetaS2 P.theta/(SecondFamily.thetaS1 P.theta-161/1089)=P.theta
  dsimp only [SecondFamily.thetaS2]
  exact mul_div_cancel_right₀ P.theta hd

theorem secondQuarticToG2_injective:Function.Injective secondQuarticToG2 := by
  intro P Q h
  have ht:=congrArg (fun z:SecondFamily.G2Point ℚ=>z.s2/(z.s1-161/1089)) h
  rw [secondQuartic_theta_recover,secondQuartic_theta_recover] at ht
  have hs:=congrArg (fun z:SecondFamily.G2Point ℚ=>z.s3) h
  have heP:=secondQuartic_eta_recover P
  have heQ:=secondQuartic_eta_recover Q
  change SecondFamily.thetaEta P.theta (secondQuarticToG2 P).s3=P.eta at heP
  change SecondFamily.thetaEta Q.theta (secondQuarticToG2 Q).s3=Q.eta at heQ
  rw [ht,hs] at heP
  exact SecondQuarticPoint.ext ht (heP.symm.trans heQ)

theorem secondG2_infinite(hSilvermanVII34:OddPrimeTorsionIntegrality):
    Infinite (SecondFamily.G2Point ℚ) := by
  let : Infinite SecondQuarticPoint := infinite_SecondQuarticPoint hSilvermanVII34
  exact Infinite.of_injective secondQuarticToG2 secondQuarticToG2_injective

end Z2Z4Rank6
