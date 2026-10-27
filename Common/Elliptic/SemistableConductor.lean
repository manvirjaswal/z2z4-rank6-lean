module

public import Common.Elliptic.GeometricConductor

@[expose] public section

/-!
# The semistable branch of Tate's algorithm

Source: J. E. Cremona, Algorithms for Modular Elliptic
Curves, second edition (1997), §3.2, p. 65 (component formula), and Tate's
algorithm Steps 4 and 19–21, pp. 66–67. Author's corrected public edition:
https://johncremona.github.io/book/fulltext/chapter3.pdf.

For a minimal integral equation, good reduction has one geometric
component, and multiplicative reduction has ord_p(Delta) components.
This is the component formulation explicitly given on p. 65, including
primes 2 and 3 when c4 is a unit.
The conclusion concerns the full proper regular fiber, as explained in
that source, rather than the smaller open smooth Neron group scheme.
-/
namespace Common.Elliptic.GeometricConductor
noncomputable section

/-- The component content of Tate's good/multiplicative branches. -/
def CremonaTateSteps4And19to21 : Prop :=
  ∀ (W : WeierstrassCurve ℤ) (p : ℕ) [Fact p.Prime], W.Δ≠0 →
    WeierstrassCurve.IsMinimal (PadicInt p) (localEquation W p) →
    (¬p∣W.Δ.natAbs ∨ ¬(p:ℤ)∣W.c₄) →
    ∀ (M : LocalModel W p), M.IsMinimal →
      M.geometricComponentCount=if p∣W.Δ.natAbs then padicValNat p W.Δ.natAbs else 1

namespace Data
variable {W : WeierstrassCurve ℤ}

theorem semistable_exponent (hTate : CremonaTateSteps4And19to21) (D : Data W)
    (p : ℕ) [Fact p.Prime] (h : ¬p∣W.Δ.natAbs ∨ ¬(p:ℤ)∣W.c₄) :
    D.exponent p=if p∣W.Δ.natAbs then 1 else 0 := by
  rw [exponent,hTate W p D.discriminant_ne_zero (D.equation_minimal p) h
    (D.model p) (D.model_minimal p)]
  by_cases hd : p∣W.Δ.natAbs
  · simp [hd]
  · simp [hd,padicValNat.eq_zero_of_not_dvd hd]

end Data
end
end Common.Elliptic.GeometricConductor
