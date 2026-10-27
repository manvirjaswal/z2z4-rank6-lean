module

public import Z2Z4Rank6.BaseCurve
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

@[expose] public section

/-!
# Algebraic nonsingularity calculations for the base curve

The pencil and gradient calculations underlying Lemma 4.1(a) of M. Jaswal,
*Infinitely many elliptic curves with torsion Z/2Z × Z/4Z and rank at least six*,
DOI 10.5281/zenodo.23437117.

These are concrete matrix and polynomial statements. The general geometric
Jacobian criterion and the genus of the projective complete intersection are
not asserted by these declarations.
-/

namespace Z2Z4Rank6

def quadricPencil {K : Type*} [CommRing K] (l1 l2 : K) : Matrix (Fin 4) (Fin 4) K :=
  Matrix.diagonal ![-15*l1-10*l2, l1, l2, -1210*l1-1215*l2]

theorem quadricPencil_det {K : Type*} [CommRing K] (l1 l2 : K) :
    (quadricPencil l1 l2).det =
      25*l1*l2*(3*l1+2*l2)*(242*l1+243*l2) := by
  simp [quadricPencil, Matrix.det_diagonal, Fin.prod_univ_succ]
  ring

def quadricPencilRoot (i : Fin 4) : ℚ × ℚ :=
  ![(1,0),(0,1),(2,-3),(243,-242)] i

theorem quadricPencil_root_zero (i : Fin 4) :
    (quadricPencil (quadricPencilRoot i).1 (quadricPencilRoot i).2).det = 0 := by
  rw [quadricPencil_det]
  fin_cases i <;> norm_num [quadricPencilRoot]

theorem quadricPencil_roots_distinct (i j : Fin 4) (hij : i ≠ j) :
    (quadricPencilRoot i).1*(quadricPencilRoot j).2 -
      (quadricPencilRoot i).2*(quadricPencilRoot j).1 ≠ 0 := by
  fin_cases i <;> fin_cases j <;> first | exact (hij rfl).elim | norm_num [quadricPencilRoot]

/-- The two projective quadric gradients are independent at every nonzero
common zero, over any field of characteristic zero. The four displayed
vanishing products are a linear relation between their coordinate gradients,
after cancelling the harmless nonzero factors. -/
theorem quadric_gradients_independent {K : Type*} [Field K] [CharZero K]
    (m u v z l1 l2 : K)
    (hu : u^2 = 15*m^2+1210*z^2) (hv : v^2 = 10*m^2+1215*z^2)
    (hnonzero : m ≠ 0 ∨ u ≠ 0 ∨ v ≠ 0 ∨ z ≠ 0)
    (hmu : l1*u = 0) (hmv : l2*v = 0)
    (hmm : (3*l1+2*l2)*m = 0) (hmz : (242*l1+243*l2)*z = 0) :
    l1 = 0 ∧ l2 = 0 := by
  by_cases hl1 : l1 = 0
  · refine ⟨hl1, ?_⟩
    by_contra hl2
    have hv0 : v = 0 := (mul_eq_zero.mp hmv).resolve_left hl2
    have hm0 : m = 0 := (mul_eq_zero.mp hmm).resolve_left (by simpa [hl1] using hl2)
    have hz0 : z = 0 := (mul_eq_zero.mp hmz).resolve_left (by simpa [hl1] using hl2)
    have hu0 : u = 0 := by rw [hm0, hz0] at hu; simpa using hu
    simp [hm0, hu0, hv0, hz0] at hnonzero
  · by_cases hl2 : l2 = 0
    · refine ⟨?_, hl2⟩
      have hu0 : u = 0 := (mul_eq_zero.mp hmu).resolve_left hl1
      have hm0 : m = 0 := (mul_eq_zero.mp hmm).resolve_left (by simpa [hl2] using hl1)
      have hz0 : z = 0 := (mul_eq_zero.mp hmz).resolve_left (by simpa [hl2] using hl1)
      have hv0 : v = 0 := by rw [hm0, hz0] at hv; simpa using hv
      simp [hm0, hu0, hv0, hz0] at hnonzero
    · have hu0 : u = 0 := (mul_eq_zero.mp hmu).resolve_left hl1
      have hv0 : v = 0 := (mul_eq_zero.mp hmv).resolve_left hl2
      rw [hu0] at hu
      rw [hv0] at hv
      have hm2 : m^2 = 0 := by
        linear_combination (-243/1225)*hu + (242/1225)*hv
      have hz2 : z^2 = 0 := by
        linear_combination (2/1225)*hu - (3/1225)*hv
      have hm0 : m = 0 := by simpa using hm2
      have hz0 : z = 0 := by simpa using hz2
      simp [hm0, hu0, hv0, hz0] at hnonzero

end Z2Z4Rank6
