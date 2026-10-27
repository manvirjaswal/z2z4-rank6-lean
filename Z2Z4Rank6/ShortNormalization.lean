import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Int.Basic
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic

/-!
# Primitive normalization of integer short Weierstrass coefficients

Source: Jaswal, DOI 10.5281/zenodo.23437117, Remark 6.3 (height), following
Park–Poonen–Voight–Wood §5.1. A short equation is normalized by removing
all simultaneous fourth/sixth prime powers. The existence proof takes a
maximal positive common scale in a finite integer-divisor set.
-/
namespace Z2Z4Rank6.ShortHeight
noncomputable section
open scoped Classical

/-- No prime fourth/sixth power can simultaneously be removed. -/
def ShortPrimitive (A B : ℤ) : Prop :=
  ∀ p : ℕ,p.Prime→¬((p:ℤ)^4∣A ∧ (p:ℤ)^6∣B)

/-- The paper's max(|4A³|,|27B²|), as a natural number. -/
def coefficientHeight (A B : ℤ) : ℕ := max (4*A.natAbs^3) (27*B.natAbs^2)

theorem coefficientHeight_eq (A B : ℤ) :
    coefficientHeight A B=max (4*A^3).natAbs (27*B^2).natAbs := by
  simp [coefficientHeight,Int.natAbs_mul,Int.natAbs_pow]

private theorem scale_dvd_sum (A B : ℤ) (d : ℕ)
    (h4 : (d:ℤ)^4∣A) (h6 : (d:ℤ)^6∣B) : d∣A.natAbs+B.natAbs := by
  have hA : (d:ℤ)∣A := (dvd_pow_self _ (by decide : 4≠0)).trans h4
  have hB : (d:ℤ)∣B := (dvd_pow_self _ (by decide : 6≠0)).trans h6
  exact Nat.dvd_add (Int.natCast_dvd.mp hA) (Int.natCast_dvd.mp hB)

/-- Every nonzero pair of integer coefficients has a positive
common scale leaving primitive integer short coefficients. -/
theorem exists_normalization (A B : ℤ) (hn : A≠0∨B≠0) :
    ∃ d : ℕ,0<d ∧ ∃ A0 B0 : ℤ,
      A=(d:ℤ)^4*A0 ∧ B=(d:ℤ)^6*B0 ∧ ShortPrimitive A0 B0 := by
  let N := A.natAbs+B.natAbs
  have hN : N≠0 := by
    intro h
    have hz := Nat.add_eq_zero_iff.mp h
    rcases hn with ha | hb
    · exact ha (Int.natAbs_eq_zero.mp hz.1)
    · exact hb (Int.natAbs_eq_zero.mp hz.2)
  let s : Finset ℕ := N.divisors.filter (fun d : ℕ => (d:ℤ)^4∣A ∧ (d:ℤ)^6∣B)
  have h1 : 1∈s := by simp [s,hN]
  have hs : s.Nonempty := ⟨1,h1⟩
  let d := s.max' hs
  have hdmem : d∈s := s.max'_mem hs
  have hdpos : 0<d := (by decide : 0<1).trans_le (s.le_max' 1 h1)
  obtain ⟨A0,hA⟩ := (Finset.mem_filter.mp hdmem).2.1
  obtain ⟨B0,hB⟩ := (Finset.mem_filter.mp hdmem).2.2
  refine ⟨d,hdpos,A0,B0,hA,hB,?_⟩
  intro p hp hpAB
  obtain ⟨a,ha⟩ := hpAB.1
  obtain ⟨b,hb⟩ := hpAB.2
  have hdp4 : ((d*p:ℕ):ℤ)^4∣A := by
    refine ⟨a,?_⟩
    rw [hA,ha,Nat.cast_mul,mul_pow]
    ring
  have hdp6 : ((d*p:ℕ):ℤ)^6∣B := by
    refine ⟨b,?_⟩
    rw [hB,hb,Nat.cast_mul,mul_pow]
    ring
  have hdp : d*p∈s := Finset.mem_filter.mpr
    ⟨Nat.mem_divisors.mpr ⟨scale_dvd_sum A B (d*p) hdp4 hdp6,hN⟩,hdp4,hdp6⟩
  have hle : d*p≤d := s.le_max' _ hdp
  have hgt : d<d*p := by nlinarith [hp.two_le]
  exact (not_lt_of_ge hle) hgt

/-- Normalization data. -/
structure Normalization (A B : ℤ) where
  scale : ℕ
  scale_pos : 0<scale
  shortA : ℤ
  shortB : ℤ
  eqA : A=(scale:ℤ)^4*shortA
  eqB : B=(scale:ℤ)^6*shortB
  primitive : ShortPrimitive shortA shortB

def normalization (A B : ℤ) (hn : A≠0∨B≠0) : Normalization A B :=
  let h := exists_normalization A B hn
  { scale := h.choose
    scale_pos := h.choose_spec.1
    shortA := h.choose_spec.2.choose
    shortB := h.choose_spec.2.choose_spec.choose
    eqA := h.choose_spec.2.choose_spec.choose_spec.1
    eqB := h.choose_spec.2.choose_spec.choose_spec.2.1
    primitive := h.choose_spec.2.choose_spec.choose_spec.2.2 }

/-- Height on the primitive coefficients supplied by normalization. -/
def Normalization.height {A B : ℤ} (n : Normalization A B) : ℕ :=
  coefficientHeight n.shortA n.shortB

/-- Removing a fourth/sixth scale removes precisely its twelfth power
from the coefficient height. -/
theorem coefficientHeight_scale (d : ℕ) (A B : ℤ) :
    coefficientHeight ((d:ℤ)^4*A) ((d:ℤ)^6*B)=d^12*coefficientHeight A B := by
  have h4 : 4*((d:ℤ)^4*A).natAbs^3=d^12*(4*A.natAbs^3) := by
    simp only [Int.natAbs_mul,Int.natAbs_pow,Int.natAbs_natCast,mul_pow,←pow_mul]
    ring
  have h6 : 27*((d:ℤ)^6*B).natAbs^2=d^12*(27*B.natAbs^2) := by
    simp only [Int.natAbs_mul,Int.natAbs_pow,Int.natAbs_natCast,mul_pow,←pow_mul]
    ring
  simp only [coefficientHeight,h4,h6,←mul_max]

theorem Normalization.rawHeight_eq {A B : ℤ} (n : Normalization A B) :
    coefficientHeight A B=n.scale^12*n.height := by
  exact (congrArg₂ coefficientHeight n.eqA n.eqB).trans
    (coefficientHeight_scale n.scale n.shortA n.shortB)

end
end Z2Z4Rank6.ShortHeight
