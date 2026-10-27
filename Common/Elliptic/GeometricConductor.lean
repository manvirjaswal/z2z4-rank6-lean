import Common.Elliptic.RegularProperModel
import Common.Elliptic.WeierstrassScheme
import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# The geometric conductor of a globally minimal integral elliptic equation

J. E. Cremona, *Algorithms for Modular Elliptic Curves*, second edition
(1997), Section 3.2, p. 65, defines the local exponent by
`ord_p(minimal discriminant) + 1 - number of geometric fiber components`.
Here the components are those of the geometric special fiber of a minimal proper regular model. The
global conductor is the product of these local prime powers.

The model-existence input below is the elliptic-curve case of B. Conrad,
*Minimal models for elliptic curves* (2015), Theorem 3.10, p. 8. A Weierstrass equation
with invertible discriminant specifies an elliptic curve, so this is a
restriction of the theorem to smooth proper curves of genus one.

No count or local exponent
is assigned by these definitions.
-/

namespace Common.Elliptic.GeometricConductor

noncomputable section
open AlgebraicGeometry CategoryTheory WeierstrassCurve
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

/-- Base change of the integral equation to the p-adic field. -/
def localEquation (W : WeierstrassCurve ℤ) (p : ℕ) [Fact p.Prime] :
    WeierstrassCurve (Padic p) :=
  W.map (Int.castRingHom (Padic p))

/-- A regular proper model of the complete p-adic cubic. -/
def LocalModel (W : WeierstrassCurve ℤ) (p : ℕ) [Fact p.Prime] :=
  RegularProperModel (PadicInt p) (Padic p)
    (WeierstrassScheme.scheme (localEquation W p))
    (WeierstrassScheme.structureMap (localEquation W p))

/-- Published minimal-model existence, specialized to elliptic
curves over p-adic fields. Conrad, Theorem 3.10, p. 8. -/
def EllipticMinimalModelsTheorem : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve (Padic p)), W.IsElliptic →
    Nonempty {M : RegularProperModel (PadicInt p) (Padic p)
      (WeierstrassScheme.scheme W) (WeierstrassScheme.structureMap W) // M.IsMinimal}

/-- Geometric conductor data: a globally minimal integral equation
and a minimal regular proper model at every rational prime. -/
structure Data (W : WeierstrassCurve ℤ) : Prop where
  discriminant_ne_zero : W.Δ ≠ 0
  equation_minimal (p : ℕ) [Fact p.Prime] :
    WeierstrassCurve.IsMinimal (PadicInt p) (localEquation W p)
  model_exists (p : ℕ) [Fact p.Prime] :
    Nonempty {M : LocalModel W p // RegularProperModel.IsMinimal M}

namespace Data

variable {W : WeierstrassCurve ℤ}

/-- Choose a minimal regular model only from its explicit existence. -/
def model (D : Data W) (p : ℕ) [Fact p.Prime] : LocalModel W p :=
  (Classical.choice (D.model_exists p)).val

theorem model_minimal (D : Data W) (p : ℕ) [Fact p.Prime] :
    RegularProperModel.IsMinimal (D.model p) :=
  (Classical.choice (D.model_exists p)).property

/-- The local exponent in the geometric definition of the conductor. -/
def exponent (D : Data W) (p : ℕ) [Fact p.Prime] : ℕ :=
  padicValNat p W.Δ.natAbs + 1 - (D.model p).geometricComponentCount

/-- The prime-power factor, extended by one away from prime indices. -/
def factor (D : Data W) (p : ℕ) : ℕ :=
  if hp : p.Prime then
    letI : Fact p.Prime := ⟨hp⟩
    p ^ D.exponent p
  else 1

/-- The geometric conductor, using the finite discriminant support.
Published good-reduction theory makes all omitted local exponents zero. -/
def conductor (D : Data W) : ℕ :=
  ∏ p ∈ W.Δ.natAbs.primeFactors, D.factor p

theorem factor_eq_prime_pow (D : Data W) (p : ℕ) [hp : Fact p.Prime] :
    D.factor p = p ^ D.exponent p := by
  simp only [factor, dite_eq_left hp.out]

/-- Every local exponent is determined by a geometric component count. -/
theorem exponent_of_component_count (D : Data W) (p : ℕ) [Fact p.Prime]
    (n : ℕ) (hn : (D.model p).geometricComponentCount = n) :
    D.exponent p = padicValNat p W.Δ.natAbs + 1 - n := by
  rw [exponent, hn]

end Data

/-- Assemble models from the published theorem.
The globally minimal equation is separately supplied and retained. -/
theorem dataOfMinimalEquation (hModels : EllipticMinimalModelsTheorem)
    (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0)
    (hMinimal : ∀ (p : ℕ) [Fact p.Prime],
      WeierstrassCurve.IsMinimal (PadicInt p) (localEquation W p))
    (hElliptic : ∀ (p : ℕ) [Fact p.Prime], (localEquation W p).IsElliptic) : Data W where
  discriminant_ne_zero := hΔ
  equation_minimal := hMinimal
  model_exists := fun p _hp => hModels p (localEquation W p) (hElliptic p)

end
end Common.Elliptic.GeometricConductor
