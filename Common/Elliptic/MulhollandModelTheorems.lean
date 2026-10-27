module

public import Common.Elliptic.MulhollandTwoAdic
public import Common.Elliptic.GeometricConductor

@[expose] public section

/-!
# Published local component formulas for curves with rational two-torsion

Sources: J. T. Mulholland, Elliptic curves with rational
2-torsion and related ternary Diophantine equations, UBC PhD thesis (2006),
Theorem 2.1 p. 13, Table 2.1 p. 15, and Theorems 2.3–2.4 p. 13, Tables 2.3–2.4
p. 16. The conclusions here use the geometric component content of the
displayed Kodaira symbols: I_n has n components for n>0, I_0 has one,
and I_m* has m+5. These concern the full minimal proper regular fiber,
not the open smooth Néron group scheme.

Only the stated rows are retained. Each hypothesis is generic in the
equation, prime and minimal regular proper model.
The two-adic source hypotheses force an odd a. At odd primes the coprime
case is precisely semistable; its integral equation is minimal.

Each
input combines the stated published rows with their geometric component
interpretation.
-/

namespace Common.Elliptic.MulhollandModelTheorems
noncomputable section
open MulhollandTwoAdic GeometricConductor

/-- The component-count consequence of the three selected rows of
Mulholland Theorem 2.1/Table 2.1, with minimal regular models. -/
def Theorem21Components : Prop :=
  ∀ (a b : ℤ) (m : ℕ), (equation a b).Δ ≠ 0 → IStarRow a b m →
    ∀ (M : LocalModel (equation a b) 2), M.IsMinimal →
      M.geometricComponentCount = m+5

/-- The coprime-coefficient component-count specialization of
Mulholland Theorems 2.3–2.4 and their tables at odd primes. -/
def Theorems23And24SemistableComponents : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 →
    ∀ (a b : ℤ), (equation a b).Δ ≠ 0 → IsCoprime a b →
      ∀ (M : LocalModel (equation a b) p), M.IsMinimal →
        M.geometricComponentCount =
          if p ∣ (equation a b).Δ.natAbs then
            padicValNat p (equation a b).Δ.natAbs else 1

end
end Common.Elliptic.MulhollandModelTheorems
