import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Algebra.Rat

/-!
# Quadratic root-field homomorphisms with explicit coefficient maps

The universal quadratic-algebra lift is packaged as a ring homomorphism, so
an existing scalar action on the target does not get confused with the new
coefficient embedding. Rational scalar compatibility is automatic.
-/
namespace Z2Z4Rank6
noncomputable section
section Fields
variable {F L : Type*} [Field F] [Field L]

def quadraticFieldLift (a : F) (f : F→+*L) (z : L) (hz : z^2=f a) :
    QuadraticAlgebra F a 0→+*L := by
  letI : Algebra F L := f.toAlgebra
  refine (QuadraticAlgebra.lift (R:=F) (A:=L) ⟨z,?_⟩).toRingHom
  change z*z=f a*1+f 0*z
  simpa only [map_zero,zero_mul,add_zero,mul_one,←sq] using hz

@[simp] theorem quadraticFieldLift_algebraMap (a : F) (f : F→+*L) (z : L) (hz : z^2=f a)
    (r : F) : quadraticFieldLift a f z hz (algebraMap F (QuadraticAlgebra F a 0) r)=f r := by
  change f r*1+f 0*z=f r
  simp only [map_zero,zero_mul,add_zero,mul_one]

@[simp] theorem quadraticFieldLift_omega (a : F) (f : F→+*L) (z : L) (hz : z^2=f a) :
    quadraticFieldLift a f z hz QuadraticAlgebra.omega=z := by
  change f 0*1+f 1*z=z
  simp only [map_zero,map_one,zero_mul,one_mul,zero_add]

end Fields

section Rational
variable {L M : Type*} [Field L] [Field M] [Algebra ℚ L] [Algebra ℚ M]

def ringHomToRatAlgHom (f : L→+*M) : L→ₐ[ℚ]M where
  __ := f
  commutes' := f.map_rat_algebraMap

@[simp] theorem ringHomToRatAlgHom_apply (f : L→+*M) (x : L) : ringHomToRatAlgHom f x=f x := rfl

end Rational
end
end Z2Z4Rank6
