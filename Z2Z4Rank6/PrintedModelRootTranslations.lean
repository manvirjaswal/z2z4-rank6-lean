module

public import Common.Elliptic.MulhollandTwoAdic
public import Z2Z4Rank6.PrintedModelMinimality

@[expose] public section

/-!
# Integral root translations for the three printed equations

The equations are those of Jaswal, DOI 10.5281/zenodo.23437117,
Lemma 4.1(b), Proposition 7.2(a) and Theorem 8.1(a). Integral
Weierstrass variable changes put them in the form y²=x³+ax²+bx.
The arithmetic hypotheses of the three relevant rows of Mulholland,
Theorem 2.1, Table 2.1, are checked directly.
-/

namespace Z2Z4Rank6.PrintedModelRootTranslations

open WeierstrassCurve Common.Elliptic.MulhollandTwoAdic PrintedModelMinimality
set_option maxRecDepth 10000

def root : Fin 3 → ℤ := ![404,1666,51068871386]
def translatedA : Fin 3 → ℤ := ![1213,4999,153206614159]
def translatedB : Fin 3 → ℤ := ![352836,-17767400,-103390701809256688400]
def starIndex : Fin 3 → ℕ := ![1,2,4]

/-- These are integral coefficient identities under x=X+r. -/
theorem translation_eq (i : Fin 3) :
    translation (root i) • integerModel i = equation (translatedA i) (translatedB i) := by
  fin_cases i <;> ext <;>
    norm_num [translation, root, integerModel, translatedA, translatedB,
      equation, WeierstrassCurve.variableChange_def]

/-- The exact arithmetic row inputs for the published two-adic classification. -/
theorem mulholland_row (i : Fin 3) :
    IStarRow (translatedA i) (translatedB i) (starIndex i) := by
  have hv {n k : ℕ} (hn : n ≠ 0) (h0 : 2^k ∣ n) (h1 : ¬2^(k+1) ∣ n) :
      padicValNat 2 n = k := by
    let : Fact (Nat.Prime 2) := ⟨by decide⟩
    have hlo : k ≤ padicValNat 2 n := (padicValNat_dvd_iff_le hn).mp h0
    have hhi : ¬ k+1 ≤ padicValNat 2 n := by
      intro h
      exact h1 ((padicValNat_dvd_iff_le hn).mpr h)
    omega
  have hA (i : Fin 3) : padicValNat 2 (translatedA i).natAbs = 0 := by
    apply padicValNat.eq_zero_of_not_dvd
    fin_cases i <;> norm_num [translatedA]
  fin_cases i
  · refine ⟨hA 0,Or.inl ⟨?_,by norm_num [translatedA],rfl⟩⟩
    exact hv (by norm_num [translatedB]) (by norm_num [translatedB]) (by norm_num [translatedB])
  · refine ⟨hA 1,Or.inr (Or.inl ⟨?_,by norm_num [translatedA],rfl⟩)⟩
    exact hv (by norm_num [translatedB]) (by norm_num [translatedB]) (by norm_num [translatedB])
  · refine ⟨hA 2,Or.inr (Or.inr ⟨?_,by norm_num [translatedA],rfl⟩)⟩
    exact hv (by norm_num [translatedB]) (by norm_num [translatedB]) (by norm_num [translatedB])

theorem translated_discriminant (i : Fin 3) :
    (equation (translatedA i) (translatedB i)).Δ = (integerModel i).Δ := by
  rw [← translation_eq, translation_discriminant]

end Z2Z4Rank6.PrintedModelRootTranslations
