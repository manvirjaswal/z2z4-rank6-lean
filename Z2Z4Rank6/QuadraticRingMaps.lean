module

public import Mathlib.Algebra.QuadraticAlgebra.Basic

@[expose] public section

/-! Coefficient maps and root universal maps for quadratic algebras over
commutative rings. These elementary constructions expose their two normal-form
coefficients, so injectivity reduces to injectivity on coefficients. -/
namespace Z2Z4Rank6
noncomputable section
section Coefficients
variable {R S : Type*} [CommRing R] [CommRing S]
def quadraticCoefficientMap (a : R) (a' : S) (f : R→+*S) (ha : f a=a') :
    QuadraticAlgebra R a 0→+*QuadraticAlgebra S a' 0 where
  toFun z:=⟨f z.re,f z.im⟩
  map_zero':=by ext <;> simp
  map_one':=by
    ext
    · change f 1=1
      exact map_one f
    · change f 0=0
      exact map_zero f
  map_add' z w:=by ext <;> simp
  map_mul' z w:=by ext <;> simp [QuadraticAlgebra.re_mul,QuadraticAlgebra.im_mul,ha]

@[simp] theorem quadraticCoefficientMap_re (a : R) (a' : S) (f : R→+*S) (ha : f a=a')
    (z : QuadraticAlgebra R a 0) : (quadraticCoefficientMap a a' f ha z).re=f z.re := rfl
@[simp] theorem quadraticCoefficientMap_im (a : R) (a' : S) (f : R→+*S) (ha : f a=a')
    (z : QuadraticAlgebra R a 0) : (quadraticCoefficientMap a a' f ha z).im=f z.im := rfl
@[simp] theorem quadraticCoefficientMap_algebraMap (a : R) (a' : S) (f : R→+*S) (ha : f a=a') (r : R) :
    quadraticCoefficientMap a a' f ha (algebraMap R (QuadraticAlgebra R a 0) r)=
      algebraMap S (QuadraticAlgebra S a' 0) (f r) := by ext <;> simp
@[simp] theorem quadraticCoefficientMap_omega (a : R) (a' : S) (f : R→+*S) (ha : f a=a') :
    quadraticCoefficientMap a a' f ha QuadraticAlgebra.omega=QuadraticAlgebra.omega := by ext <;> simp

theorem quadraticCoefficientMap_injective (a : R) (a' : S) (f : R→+*S) (ha : f a=a')
    (hf : Function.Injective f) : Function.Injective (quadraticCoefficientMap a a' f ha) := by
  intro z w h
  ext
  · exact hf (congrArg QuadraticAlgebra.re h)
  · exact hf (congrArg QuadraticAlgebra.im h)
end Coefficients
section Roots
variable {R S : Type*} [CommRing R] [CommRing S]
def quadraticRingLift (a : R) (f : R→+*S) (z : S) (hz : z^2=f a) :
    QuadraticAlgebra R a 0→+*S := by
  letI : Algebra R S := f.toAlgebra
  refine (QuadraticAlgebra.lift (R:=R) (A:=S) ⟨z,?_⟩).toRingHom
  change z*z=f a*1+f 0*z
  simpa only [map_zero,zero_mul,add_zero,mul_one,←sq] using hz
@[simp] theorem quadraticRingLift_algebraMap (a : R) (f : R→+*S) (z : S) (hz : z^2=f a) (r : R) :
    quadraticRingLift a f z hz (algebraMap R (QuadraticAlgebra R a 0) r)=f r := by
  change f r*1+f 0*z=f r
  simp only [map_zero,zero_mul,add_zero,mul_one]
@[simp] theorem quadraticRingLift_omega (a : R) (f : R→+*S) (z : S) (hz : z^2=f a) :
    quadraticRingLift a f z hz QuadraticAlgebra.omega=z := by
  change f 0*1+f 1*z=z
  simp only [map_zero,map_one,zero_mul,one_mul,zero_add]
end Roots
end
end Z2Z4Rank6
