import Common.Elliptic.SurfaceModel
import Common.Elliptic.SurfaceLocalData
import Mathlib.Analysis.Complex.Basic

/-!
# Two polynomial charts of a Weierstrass surface

The finite equation and infinity equation are ordinary Weierstrass
polynomials. Their coefficients satisfy the weighted reciprocal
transition, so the change is t=1/s, x=x'/s^(2d), y=y'/s^(3d).

Reference: Miranda, The Basic Theory of Elliptic Surfaces (1989),
II.5, pp. 25–27 and III.1, pp. 28–29 (coordinate changes and weights).
-/
namespace Common.Elliptic.SurfaceWeierstrassData
noncomputable section
open Polynomial WeierstrassCurve

/-- Generic Weierstrass curve over Q(t). -/
def genericCurve {k : Type} [Field k] (W : WeierstrassCurve k[X]) : WeierstrassCurve (RatFunc k) :=
  W.map (algebraMap k[X] (RatFunc k))

/-- Base change of the polynomial coefficients to C. -/
def complexChart (W : WeierstrassCurve ℚ[X]) : WeierstrassCurve ℂ[X] :=
  W.map (Polynomial.mapRingHom (algebraMap ℚ ℂ))

def coefficient {R : Type*} [CommRing R] (W : WeierstrassCurve R) : Fin 5 → R :=
  ![W.a₁,W.a₂,W.a₃,W.a₄,W.a₆]
def coefficientWeight : Fin 5 → ℕ := ![1,2,3,4,6]

/-- Reciprocal coordinate compatibility of the two integral charts. -/
def ReciprocalCompatibility {k : Type} [Field k] (W V : WeierstrassCurve k[X]) (d : ℕ) : Prop :=
  ∀ (i : Fin 5) (s : k),s≠0 →
    (coefficient V i).eval s=
      s^(coefficientWeight i*d)*(coefficient W i).eval (1/s)

/-- Polynomial local data after the coefficient field extension. -/
abbrev MultiplicativeAt (W : WeierstrassCurve ℚ[X]) (t : ℂ) (n : ℕ) :=
  SurfaceLocalData.MultiplicativeData (complexChart W) t n
abbrev GoodAt (W : WeierstrassCurve ℚ[X]) (t : ℂ) :=
  SurfaceLocalData.GoodData (complexChart W) t

end
end Common.Elliptic.SurfaceWeierstrassData
