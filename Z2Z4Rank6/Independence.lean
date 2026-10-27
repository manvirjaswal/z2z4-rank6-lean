module

public import Mathlib.LinearAlgebra.LinearIndependent.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Tactic

@[expose] public section

/-!
# Independence detected by reduction modulo 3

The integral descent used in Proposition 5.1 of Manvir Jaswal,
*Infinitely many elliptic curves with torsion Z/2Z × Z/4Z and rank at least six*,
DOI 10.5281/zenodo.23437117.

The reduction maps must kill torsion. Dividing an integral relation by a common
factor preserves a relation to torsion, which is the property used below.
-/

namespace Z2Z4Rank6

open scoped BigOperators

/-- If every integral combination landing in torsion has all
coefficients divisible by 3, every such combination has zero coefficients. -/
theorem coefficients_zero_of_torsion_divisibility
    {ι G : Type*} [Fintype ι] [AddCommGroup G] (P : ι → G)
    (hdiv : ∀ a : ι → ℤ, IsOfFinAddOrder (∑ i, a i • P i) →
      ∀ j, (3 : ℤ) ∣ a j)
    (n : ι → ℤ) (ht : IsOfFinAddOrder (∑ i, n i • P i)) :
    ∀ i, n i = 0 := by
  classical
  intro i
  have aux : ∀ k : ℕ, ∀ a : ι → ℤ, (a i).natAbs = k →
      IsOfFinAddOrder (∑ j, a j • P j) → a i = 0 := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro a hak ha
      by_cases hai : a i = 0
      · exact hai
      let b : ι → ℤ := fun j => a j / 3
      have hb : ∀ j, (3 : ℤ) * b j = a j :=
        fun j => Int.mul_ediv_cancel' (hdiv a ha j)
      have heq : (3 : ℕ) • (∑ j, b j • P j) = ∑ j, a j • P j := by
        rw [Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro j _
        rw [← Nat.cast_smul_eq_nsmul ℤ, smul_smul]
        norm_num only [Nat.cast_ofNat]
        rw [hb]
      have hbt : IsOfFinAddOrder (∑ j, b j • P j) :=
        (heq ▸ ha).of_nsmul (by decide : (3 : ℕ) ≠ 0)
      have hlt : (b i).natAbs < k := by
        rw [← hak]
        change (a i / 3).natAbs < (a i).natAbs
        rw [Int.natAbs_ediv_of_dvd (hdiv a ha i)]
        exact Nat.div_lt_self (Int.natAbs_pos.mpr hai) (by decide)
      have hbi : b i = 0 := ih (b i).natAbs hlt b rfl hbt
      simpa only [hbi, mul_zero] using (hb i).symm
  exact aux (n i).natAbs n rfl ht

/-- Independent images modulo 3 force every integral combination
which is torsion to have all coefficients zero. -/
theorem coefficients_zero_of_torsion_combination
    {ι G V : Type*} [Fintype ι] [AddCommGroup G] [AddCommGroup V]
    [Module (ZMod 3) V] (P : ι → G) (f : G →+ V)
    (hkill : ∀ Q : G, IsOfFinAddOrder Q → f Q = 0)
    (hlin : LinearIndependent (ZMod 3) (fun i => f (P i)))
    (n : ι → ℤ) (ht : IsOfFinAddOrder (∑ i, n i • P i)) :
    ∀ i, n i = 0 := by
  apply coefficients_zero_of_torsion_divisibility P ?_ n ht
  intro a ha j
  have hz : ∑ i, (a i : ZMod 3) • f (P i) = 0 := by
    simpa only [map_sum, map_zsmul, Int.cast_smul_eq_zsmul] using
      hkill (∑ i, a i • P i) ha
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd (a j) 3).mp
    ((Fintype.linearIndependent_iff.mp hlin) (fun i => (a i : ZMod 3)) hz j)

/-- a torsion-killing reduction map with linearly independent mod-3
images proves that the original points are linearly independent over Z. -/
theorem linearIndependent_of_mod3
    {ι G V : Type*} [Fintype ι] [AddCommGroup G] [AddCommGroup V]
    [Module (ZMod 3) V] (P : ι → G) (f : G →+ V)
    (hkill : ∀ Q : G, IsOfFinAddOrder Q → f Q = 0)
    (hlin : LinearIndependent (ZMod 3) (fun i => f (P i))) :
    LinearIndependent ℤ P := by
  apply Fintype.linearIndependent_iff.mpr
  intro n hn
  exact coefficients_zero_of_torsion_combination P f hkill hlin n
    (isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨1, by decide, by simpa using hn⟩)

/-- Order-three reduction generators and an invertible matrix of
scalar images detect all torsion-valued integral relations. The target groups
may vary with the reduction prime. -/
theorem coefficients_zero_of_three_torsion_rows
    {ι G : Type*} [Fintype ι] [DecidableEq ι] [AddCommGroup G]
    {H : ι → Type*} [∀ i, AddCommGroup (H i)]
    (P : ι → G) (f : ∀ i, G →+ H i) (g : ∀ i, H i)
    (M : Matrix ι ι (ZMod 3)) (hM : IsUnit M)
    (horder : ∀ i, addOrderOf (g i) = 3)
    (hkill : ∀ i Q, IsOfFinAddOrder Q → f i Q = 0)
    (hvalues : ∀ i j, f i (P j) = (M i j).val • g i)
    (n : ι → ℤ) (ht : IsOfFinAddOrder (∑ i, n i • P i)) :
    ∀ i, n i = 0 := by
  apply coefficients_zero_of_torsion_divisibility P ?_ n ht
  intro a ha
  have hz : M.mulVec (fun j => (a j : ZMod 3)) = 0 := by
    ext i
    have hs : (∑ j, a j * ((M i j).val : ℤ)) • g i = 0 := by
      rw [Finset.sum_smul]
      simpa only [map_sum, map_zsmul, hvalues, ← Nat.cast_smul_eq_nsmul ℤ,
        smul_smul] using hkill i (∑ j, a j • P j) ha
    have hd : (3 : ℤ) ∣ ∑ j, a j * ((M i j).val : ℤ) := by
      simpa only [horder, Nat.cast_ofNat] using
        (addOrderOf_dvd_iff_zsmul_eq_zero.mpr hs)
    have hc := (ZMod.intCast_zmod_eq_zero_iff_dvd
      (∑ j, a j * ((M i j).val : ℤ)) 3).mpr hd
    simpa [Matrix.mulVec, dotProduct, mul_comm] using hc
  have ha0 : (fun j => (a j : ZMod 3)) = 0 :=
    (Matrix.mulVec_injective_of_isUnit hM) (by simpa using hz)
  intro j
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd (a j) 3).mp (congrFun ha0 j)

/-- The checked order-three rows prove integer linear independence. -/
theorem linearIndependent_of_three_torsion_rows
    {ι G : Type*} [Fintype ι] [DecidableEq ι] [AddCommGroup G]
    {H : ι → Type*} [∀ i, AddCommGroup (H i)]
    (P : ι → G) (f : ∀ i, G →+ H i) (g : ∀ i, H i)
    (M : Matrix ι ι (ZMod 3)) (hM : IsUnit M)
    (horder : ∀ i, addOrderOf (g i) = 3)
    (hkill : ∀ i Q, IsOfFinAddOrder Q → f i Q = 0)
    (hvalues : ∀ i j, f i (P j) = (M i j).val • g i) :
    LinearIndependent ℤ P := by
  apply Fintype.linearIndependent_iff.mpr
  intro n hn
  apply coefficients_zero_of_three_torsion_rows P f g M hM horder hkill hvalues n
  simpa only [hn] using (IsOfFinAddOrder.zero (G := G))

end Z2Z4Rank6
