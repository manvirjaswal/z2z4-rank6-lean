module

public import Z2Z4Rank6.ThirdTwistCoverPolynomialData

@[expose] public section

namespace Z2Z4Rank6.ThirdTwistCoverEquations
noncomputable section
open scoped Classical

def binary {A : Type*} [CommRing A] [Algebra ℚ A] (z m : A) : Fin 3→A :=
  ![15*m^2+1210*z^2,10*m^2+1215*z^2,4*m^2+45*z^2]
def degree : Fin 3→ℕ := fun _=>2
def rootWeight : Fin 3→ℕ := fun _=>1

theorem scale {A : Type*} [CommRing A] [Algebra ℚ A]
    (z m t : A) (i : Fin 3) : binary (z*t) (m*t) i=t^(degree i)*binary z m i := by
  fin_cases i <;> dsimp [binary,degree] <;> ring

theorem map_binary {A B : Type*} [CommRing A] [CommRing B] [Algebra ℚ A] [Algebra ℚ B]
    (f : A→+*B) (z m : A) (i : Fin 3) : f (binary z m i)=binary (f z) (f m) i := by
  fin_cases i <;> dsimp [binary]
  all_goals simp only [map_add,map_mul,map_pow]
  all_goals norm_num only [map_ofNat]

theorem normalized {A : Type*} [CommRing A] [Algebra ℚ A] (z m r t : A) (i : Fin 3)
    (hr : r^2=binary z m i) : (r*t^(rootWeight i))^2=binary (z*t) (m*t) i := by
  rw [scale,mul_pow,hr]
  dsimp only [rootWeight,degree]
  ring
end
end Z2Z4Rank6.ThirdTwistCoverEquations
