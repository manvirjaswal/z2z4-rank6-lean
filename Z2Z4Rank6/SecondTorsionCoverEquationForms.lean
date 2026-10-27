import Z2Z4Rank6.SecondFamily
import Z2Z4Rank6.TorsionSquareLiftData
import Mathlib.Tactic
namespace Z2Z4Rank6.SecondTorsionCoverEquations
noncomputable section
open SecondFamily
open scoped Classical

def binary {A : Type*} [CommRing A] [Algebra ℚ A] (ε : Bool) (z m : A) : Fin 3→A :=
  ![29*(m^2-algebraMap ℚ A beta*z^2),
    algebraMap ℚ A (-29*beta)*(m^2-algebraMap ℚ A gamma*z^2),
    -algebraMap ℚ A (TorsionHyperelliptic.sign ε)*(m^2-z^2)*
      (m^2-algebraMap ℚ A (lambda^2)*z^2)]
def degree : Fin 3→ℕ := ![2,2,4]
def rootWeight : Fin 3→ℕ := ![1,1,2]

theorem scale {A : Type*} [CommRing A] [Algebra ℚ A]
    (ε : Bool) (z m t : A) (i : Fin 3) : binary ε (z*t) (m*t) i=t^(degree i)*binary ε z m i := by
  fin_cases i <;> dsimp [binary,degree] <;> ring

theorem map_binary {A B : Type*} [CommRing A] [CommRing B] [Algebra ℚ A] [Algebra ℚ B]
    (f : A→+*B) (ε : Bool) (z m : A) (i : Fin 3) : f (binary ε z m i)=binary ε (f z) (f m) i := by
  have hq : ∀q:ℚ,f (algebraMap ℚ A q)=algebraMap ℚ B q := fun q =>
    RingHom.congr_fun (RingHom.ext_rat (f.comp (algebraMap ℚ A)) (algebraMap ℚ B)) q
  fin_cases i <;> dsimp [binary]
  all_goals simp only [map_mul,map_sub,map_pow,map_neg,hq]
  all_goals norm_num only [map_ofNat]

theorem normalized {A : Type*} [CommRing A] [Algebra ℚ A] (ε : Bool) (z m r t : A) (i : Fin 3)
    (hr : r^2=binary ε z m i) : (r*t^(rootWeight i))^2=binary ε (z*t) (m*t) i := by
  have hd : degree i=rootWeight i*2 := by fin_cases i <;> rfl
  rw [scale,mul_pow,hr,←pow_mul,←hd,mul_comm]
end
end Z2Z4Rank6.SecondTorsionCoverEquations
