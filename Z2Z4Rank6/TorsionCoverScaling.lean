import Z2Z4Rank6.TorsionCoverPolynomialData
import Mathlib.Tactic

/-! Exact polynomial scaling identities for the weighted torsion-cover charts. -/
namespace Z2Z4Rank6.TorsionCoverScaling
noncomputable section
open HeightInvariantForms

variable {A B : Type*} [CommRing A] [CommRing B]

theorem map_binaryA (f : A→+*B) (z m : A) :
    f (binaryA z m)=binaryA (f z) (f m) := by
  norm_num [binaryA]
  norm_num only [map_ofNat]
theorem map_binaryB (f : A→+*B) (z m : A) :
    f (binaryB z m)=binaryB (f z) (f m) := by
  norm_num [binaryB]
  norm_num only [map_ofNat]

theorem normalized_first (m u z t : A) (hu : u^2=15*m^2+1210*z^2)
    (hz : z*t=1) : (u*t)^2=15*(m*t)^2+1210 := by
  have hzt := congrArg (fun x : A => x^2) hz
  linear_combination t^2*hu+1210*hzt

theorem normalized_second (m v z t : A) (hv : v^2=10*m^2+1215*z^2)
    (hz : z*t=1) : (v*t)^2=10*(m*t)^2+1215 := by
  have hzt := congrArg (fun x : A => x^2) hz
  linear_combination t^2*hv+1215*hzt

theorem normalized_first_infinity (m u z t : A) (hu : u^2=15*m^2+1210*z^2)
    (hm : m*t=1) : (u*t)^2=15+1210*(z*t)^2 := by
  have hmt := congrArg (fun x : A => x^2) hm
  linear_combination t^2*hu+15*hmt

theorem normalized_second_infinity (m v z t : A) (hv : v^2=10*m^2+1215*z^2)
    (hm : m*t=1) : (v*t)^2=10+1215*(z*t)^2 := by
  have hmt := congrArg (fun x : A => x^2) hm
  linear_combination t^2*hv+10*hmt

theorem normalized_third (m r z t s : A)
    (hr : r^2=s*binaryA z m*binaryB z m) :
    (r*t^4)^2=s*binaryA (z*t) (m*t)*binaryB (z*t) (m*t) := by
  rw [show z*t=t*z from mul_comm _ _,show m*t=t*m from mul_comm _ _,
    binaryA_scale,binaryB_scale,mul_pow,hr]
  ring

end
end Z2Z4Rank6.TorsionCoverScaling
