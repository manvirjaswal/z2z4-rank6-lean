import Z2Z4Rank6.TorsionCoverNormalForm

/-! The six square relations in the two signed torsion-cover charts,
plus homogeneous scaling identities over arbitrary commutative rings. -/
namespace Z2Z4Rank6.TorsionCoverEquations
noncomputable section
open Polynomial
section Generic
variable {A : Type*} [CommRing A] [Algebra ℚ A]
theorem aeval_a (t : A) : Polynomial.aeval t (a (Polynomial.X:ℚ[X]))=a t := by
  simp only [a,map_mul,map_sub,map_add,map_ofNat,map_one,Polynomial.aeval_X]
theorem aeval_b (t : A) : Polynomial.aeval t (b (Polynomial.X:ℚ[X]))=b t := by
  simp only [b,map_mul,map_sub,map_add,map_neg,map_ofNat,map_one,Polynomial.aeval_X]
theorem aeval_binaryA (t : A) :
    Polynomial.aeval t (HeightInvariantForms.binaryA (Polynomial.X:ℚ[X]) 1)=HeightInvariantForms.binaryA t 1 := by
  simp only [HeightInvariantForms.binaryA,map_mul,map_sub,map_add,map_ofNat,map_one,Polynomial.aeval_X]
theorem aeval_binaryB (t : A) :
    Polynomial.aeval t (HeightInvariantForms.binaryB (Polynomial.X:ℚ[X]) 1)=HeightInvariantForms.binaryB t 1 := by
  simp only [HeightInvariantForms.binaryB,map_mul,map_sub,map_add,map_neg,map_ofNat,map_one,Polynomial.aeval_X]
end Generic
section Rings
variable {A B : Type*} [CommRing A] [CommRing B]
theorem map_a (f : A→+*B) (t : A) : f (a t)=a (f t) := by simp only [a,map_mul,map_sub,map_add,map_ofNat,map_one]
theorem map_b (f : A→+*B) (t : A) : f (b t)=b (f t) := by simp only [b,map_mul,map_sub,map_add,map_neg,map_ofNat,map_one]

theorem binaryA_inverse (m z : A) (h : z*m=1) : HeightInvariantForms.binaryA z 1=z^4*a m := by
  have he := HeightInvariantForms.binaryA_scale z 1 m
  rw [mul_one,h] at he
  simpa only [HeightInvariantForms.binaryA,a,mul_one] using he

theorem binaryB_inverse (m z : A) (h : z*m=1) : HeightInvariantForms.binaryB z 1=z^4*b m := by
  have he := HeightInvariantForms.binaryB_scale z 1 m
  rw [mul_one,h] at he
  simpa only [HeightInvariantForms.binaryB,b,mul_one] using he

theorem scaled_square (m u z a b : A) (hu : u^2=a*m^2+b) (hm : m*z=1) :
    (u*z)^2=b*z^2+a := by
  calc
    _=u^2*z^2 := by ring
    _=(a*m^2+b)*z^2 := by rw [hu]
    _=b*z^2+a*(m*z)^2 := by ring
    _=b*z^2+a := by rw [hm,one_pow,mul_one]
end Rings
end
end Z2Z4Rank6.TorsionCoverEquations

namespace Z2Z4Rank6.TorsionCoverAffine
noncomputable section
open Polynomial TorsionCoverEquations

theorem u_sq (ε : Bool) : (u ε)^2=15*(m ε)^2+1210 := by
  have h := root_sq ε 0
  change (u ε)^2=Polynomial.aeval (m ε) (radicand ε 0) at h
  have hp : radicand ε 0=(15*Polynomial.X^2+1210:ℚ[X]) := rfl
  rw [hp] at h
  simpa only [map_add,map_mul,map_pow,map_ofNat,Polynomial.aeval_X] using h

theorem v_sq (ε : Bool) : (v ε)^2=10*(m ε)^2+1215 := by
  have h := root_sq ε 1
  change (v ε)^2=Polynomial.aeval (m ε) (radicand ε 1) at h
  have hp : radicand ε 1=(10*Polynomial.X^2+1215:ℚ[X]) := rfl
  rw [hp] at h
  simpa only [map_add,map_mul,map_pow,map_ofNat,Polynomial.aeval_X] using h

theorem r_sq (ε : Bool) : (r ε)^2=algebraMap ℚ (CoordinateRing ε) (TorsionHyperelliptic.sign ε)*a (m ε)*b (m ε) := by
  have h := root_sq ε 2
  change (r ε)^2=Polynomial.aeval (m ε) (radicand ε 2) at h
  have hp : radicand ε 2=Polynomial.C (TorsionHyperelliptic.sign ε)*a Polynomial.X*b Polynomial.X := rfl
  rw [hp] at h
  simpa only [map_mul,Polynomial.aeval_C,aeval_a,aeval_b] using h
end
end Z2Z4Rank6.TorsionCoverAffine

namespace Z2Z4Rank6.TorsionCoverInfinity
noncomputable section
open Polynomial TorsionCoverEquations

theorem U_sq (ε : Bool) : (U ε)^2=15+1210*(z ε)^2 := by
  have h := root_sq ε 0
  change (U ε)^2=Polynomial.aeval (z ε) (radicand ε 0) at h
  have hp : radicand ε 0=(15+1210*Polynomial.X^2:ℚ[X]) := rfl
  rw [hp] at h
  simpa only [map_add,map_mul,map_pow,map_ofNat,Polynomial.aeval_X] using h

theorem V_sq (ε : Bool) : (V ε)^2=10+1215*(z ε)^2 := by
  have h := root_sq ε 1
  change (V ε)^2=Polynomial.aeval (z ε) (radicand ε 1) at h
  have hp : radicand ε 1=(10+1215*Polynomial.X^2:ℚ[X]) := rfl
  rw [hp] at h
  simpa only [map_add,map_mul,map_pow,map_ofNat,Polynomial.aeval_X] using h

theorem R_sq (ε : Bool) : (R ε)^2=algebraMap ℚ (CoordinateRing ε) (TorsionHyperelliptic.sign ε)*
    HeightInvariantForms.binaryA (z ε) 1*HeightInvariantForms.binaryB (z ε) 1 := by
  have h := root_sq ε 2
  change (R ε)^2=Polynomial.aeval (z ε) (radicand ε 2) at h
  have hp : radicand ε 2=Polynomial.C (TorsionHyperelliptic.sign ε)*
      HeightInvariantForms.binaryA (Polynomial.X:ℚ[X]) 1*HeightInvariantForms.binaryB Polynomial.X 1 := rfl
  rw [hp] at h
  simpa only [map_mul,Polynomial.aeval_C,aeval_binaryA,aeval_binaryB] using h
end
end Z2Z4Rank6.TorsionCoverInfinity
