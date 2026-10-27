module

public import Z2Z4Rank6.GTorsionCoverPolynomialData

@[expose] public section

/-! Binary forms and their scaling laws for the signed covers of G. -/
namespace Z2Z4Rank6.GTorsionCoverEquations
noncomputable section
open scoped Classical

def binary {A : Type*} [CommRing A] [Algebra ℚ A] (ε : Bool) (z m : A) : Fin 2→A :=
  ![99*m^4-9998*m^2*z^2+970299*z^4,
    algebraMap ℚ A (TorsionHyperelliptic.sign ε)*
      HeightInvariantForms.binaryA z m*HeightInvariantForms.binaryB z m]
def degree : Fin 2→ℕ := ![4,8]
def rootWeight : Fin 2→ℕ := ![2,4]

theorem scale {A : Type*} [CommRing A] [Algebra ℚ A]
    (ε : Bool) (z m t : A) (i : Fin 2) : binary ε (z*t) (m*t) i=t^(degree i)*binary ε z m i := by
  fin_cases i <;> dsimp [binary,degree,HeightInvariantForms.binaryA,HeightInvariantForms.binaryB] <;> ring

theorem map_binary {A B : Type*} [CommRing A] [CommRing B] [Algebra ℚ A] [Algebra ℚ B]
    (f : A→+*B) (ε : Bool) (z m : A) (i : Fin 2) : f (binary ε z m i)=binary ε (f z) (f m) i := by
  have hq : ∀q:ℚ,f (algebraMap ℚ A q)=algebraMap ℚ B q := fun q =>
    RingHom.congr_fun (RingHom.ext_rat (f.comp (algebraMap ℚ A)) (algebraMap ℚ B)) q
  fin_cases i <;> dsimp [binary,HeightInvariantForms.binaryA,HeightInvariantForms.binaryB]
  all_goals simp only [map_mul,map_add,map_sub,map_pow,map_neg,hq]
  all_goals norm_num only [map_ofNat]

theorem normalized {A : Type*} [CommRing A] [Algebra ℚ A] (ε : Bool) (z m r t : A) (i : Fin 2)
    (hr : r^2=binary ε z m i) : (r*t^(rootWeight i))^2=binary ε (z*t) (m*t) i := by
  have hd : degree i=rootWeight i*2 := by fin_cases i <;> rfl
  rw [scale,mul_pow,hr,←pow_mul,←hd,mul_comm]
end
end Z2Z4Rank6.GTorsionCoverEquations
