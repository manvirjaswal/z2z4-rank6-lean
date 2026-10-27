import Z2Z4Rank6.ECDescentCertificates
import Mathlib.NumberTheory.Padics.RingHoms

/-!
# Reducing local quartic solutions

The elementary normalization step for the two-isogeny quartic tests in
Cremona, *Algorithms for Modular Elliptic Curves*, second edition (1997),
Section 3.6, Method 1, applied to the certificates for Jaswal's Lemma 4.1(b),
DOI 10.5281/zenodo.23437117. A nonzero local projective point reduces to a
primitive residue point after dividing by its largest coordinate.
-/

namespace Z2Z4Rank6

/-- Solubility of a homogeneous quartic on either weighted projective chart. -/
def HomogeneousQuarticSoluble {K : Type*} [CommRing K] (d A e : K) : Prop :=
  ∃ u v n : K, (u ≠ 0 ∨ v ≠ 0) ∧ n^2 = descentQuartic d A e u v

section Prime

variable {p : ℕ} [Fact p.Prime]

private theorem norm_root_le_one {n : ℚ_[p]} (h : ‖n^2‖ ≤ 1) : ‖n‖ ≤ 1 := by
  rw [norm_pow] at h
  nlinarith [norm_nonneg n]

private theorem integral_quartic_norm (d A e : ℤ) (u v : ℚ_[p])
    (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) :
    ‖descentQuartic (d : ℚ_[p]) (A : ℚ_[p]) (e : ℚ_[p]) u v‖ ≤ 1 := by
  let uI : ℤ_[p] := ⟨u,hu⟩
  let vI : ℤ_[p] := ⟨v,hv⟩
  let qI : ℤ_[p] := descentQuartic (d : ℤ_[p]) (A : ℤ_[p]) (e : ℤ_[p]) uI vI
  have hq : (qI : ℚ_[p]) =
      descentQuartic (d : ℚ_[p]) (A : ℚ_[p]) (e : ℚ_[p]) u v := by
    simp only [qI, descentQuartic, PadicInt.coe_add, PadicInt.coe_mul,
      PadicInt.coe_pow, PadicInt.coe_intCast]
    rfl
  rw [←hq]
  exact qI.property

private theorem primitive_mod_of_integral_unit (d A e : ℤ) (u v n : ℚ_[p])
    (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) (hunit : u = 1 ∨ v = 1)
    (heq : n^2 = descentQuartic (d : ℚ_[p]) (A : ℚ_[p]) (e : ℚ_[p]) u v) :
    PrimitiveQuarticSolubleMod p d A e := by
  have hn : ‖n‖ ≤ 1 := norm_root_le_one (heq ▸ integral_quartic_norm d A e u v hu hv)
  let uI : ℤ_[p] := ⟨u,hu⟩
  let vI : ℤ_[p] := ⟨v,hv⟩
  let nI : ℤ_[p] := ⟨n,hn⟩
  refine ⟨PadicInt.toZMod uI, PadicInt.toZMod vI, PadicInt.toZMod nI, ?_, ?_⟩
  · rcases hunit with hunit | hunit
    · left
      have hI : uI = 1 := Subtype.ext hunit
      rw [hI, map_one]
      exact one_ne_zero
    · right
      have hI : vI = 1 := Subtype.ext hunit
      rw [hI, map_one]
      exact one_ne_zero
  · have hI : nI^2 = descentQuartic (d : ℤ_[p]) (A : ℤ_[p]) (e : ℤ_[p]) uI vI := by
      apply Subtype.ext
      change n^2 = descentQuartic (d : ℚ_[p]) (A : ℚ_[p]) (e : ℚ_[p]) u v
      exact heq
    have hmod := congrArg PadicInt.toZMod hI
    simpa only [descentQuartic, map_pow, map_add, map_mul, map_intCast] using hmod

/-- Local solubility forces primitive solubility modulo the residue prime. -/
theorem homogeneousQuarticSoluble_implies_mod (d A e : ℤ)
    (h : HomogeneousQuarticSoluble (d : ℚ_[p]) (A : ℚ_[p]) (e : ℚ_[p])) :
    PrimitiveQuarticSolubleMod p d A e := by
  obtain ⟨u,v,n,hnonzero,heq⟩ := h
  rcases le_total ‖u‖ ‖v‖ with huv | hvu
  · have hv : v ≠ 0 := by
      intro hv
      have hu : u = 0 := norm_eq_zero.mp (le_antisymm (by simpa [hv] using huv) (norm_nonneg u))
      simp [hu,hv] at hnonzero
    have hnorm : ‖u/v‖ ≤ 1 := by
      rw [norm_div, div_le_one (norm_pos_iff.mpr hv)]
      exact huv
    apply primitive_mod_of_integral_unit d A e (u/v) 1 (n/v^2) hnorm (by simp) (Or.inr rfl)
    unfold descentQuartic at *
    field_simp
    linear_combination heq
  · have hu : u ≠ 0 := by
      intro hu
      have hv : v = 0 := norm_eq_zero.mp (le_antisymm (by simpa [hu] using hvu) (norm_nonneg v))
      simp [hu,hv] at hnonzero
    have hnorm : ‖v/u‖ ≤ 1 := by
      rw [norm_div, div_le_one (norm_pos_iff.mpr hu)]
      exact hvu
    apply primitive_mod_of_integral_unit d A e 1 (v/u) (n/u^2) (by simp) hnorm (Or.inl rfl)
    unfold descentQuartic at *
    field_simp
    linear_combination heq

end Prime

end Z2Z4Rank6
