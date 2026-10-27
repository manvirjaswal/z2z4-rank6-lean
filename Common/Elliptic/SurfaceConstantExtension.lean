module

public import Common.Elliptic.SurfaceWeierstrassData

@[expose] public section

/-!
# Constant extension of the generic equation

Coefficient extension of rational functions is the localization
map. It sends the generic curve of a polynomial equation to the generic
curve of its coefficient extension.
-/
namespace Common.Elliptic.SurfaceWeierstrassData
noncomputable section
open Polynomial
variable (k K : Type) [Field k] [Field K] [Algebra k K]

def constantExtension : RatFunc k →+* RatFunc K :=
  IsFractionRing.map (K:=RatFunc k) (L:=RatFunc K)
    (j:=Polynomial.mapRingHom (algebraMap k K))
    (Polynomial.map_injective (algebraMap k K) (algebraMap k K).injective)

@[simp] theorem constantExtension_polynomial (p : k[X]) :
    constantExtension k K (algebraMap k[X] (RatFunc k) p)=
      algebraMap K[X] (RatFunc K) (Polynomial.map (algebraMap k K) p) := by
  dsimp only [constantExtension,IsFractionRing.map]
  exact IsLocalization.map_eq _ p

theorem genericCurve_constantExtension (W : WeierstrassCurve k[X]) :
    (genericCurve W).map (constantExtension k K)=
      genericCurve (W.map (Polynomial.mapRingHom (algebraMap k K))) := by
  ext <;> simp [genericCurve,WeierstrassCurve.map]

end
end Common.Elliptic.SurfaceWeierstrassData
