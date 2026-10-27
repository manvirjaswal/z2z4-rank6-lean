module

public import Common.Elliptic.SurfaceWeierstrassData
public import Common.Elliptic.NeronPolygon
public import Common.AlgebraicGeometry.ComplexPointsTopology
public import Common.AlgebraicGeometry.K3Surface

@[expose] public section

/-!
# Local elliptic-surface fibers over C

The local good/multiplicative criterion is Miranda, The Basic Theory of
Elliptic Surfaces (1989), Table IV.3.1, p. 41. The I_n configuration
is the standard Neron polygon. Its Euler number is the multiplicative-fiber
formula in Schuett–Shioda, Elliptic Surfaces, arXiv:0907.0298v3, §6.7,
p. 27, immediately preceding Theorem 6.10. Betti groups use the
classical topology and singular homology. The coefficient field is C.

Author's scan: https://www.math.colostate.edu/~miranda/BTES-Miranda.pdf.
-/
namespace Common.Elliptic.ComplexEllipticSurfaceTheorems
noncomputable section
open _root_.AlgebraicGeometry CategoryTheory Polynomial
open SurfaceModel SurfaceWeierstrassData
open scoped Classical

abbrev Base := ProjectiveLine.scheme ℂ
abbrev PointBase := Spec (CommRingCat.of ℂ)

/-- Finite parameters and the point at infinity. -/
def parameterPoint : Option ℂ → (PointBase ⟶ Base)
  | some t=>ProjectiveLine.affinePoint ℂ ℂ t
  | none=>ProjectiveLine.infinityPoint ℂ ℂ

def fiberOver {W : WeierstrassCurve (RatFunc ℂ)} (M : RegularModel ℂ W)
    (t : Option ℂ) : Over PointBase :=
  Over.mk (M.fiberStructureMap (parameterPoint t))

/-- Smooth elliptic fiber, expressed by a cubic isomorphism. -/
def IsGoodFiber (F : Over PointBase) : Prop :=
  ∃ W : WeierstrassCurve ℂ,W.IsElliptic ∧
    Nonempty (F ≅ Over.mk (WeierstrassScheme.structureMap W))

/-- Miranda's local good/multiplicative classification, with the
minimal regular model and polynomial coordinate changes retained. -/
structure MirandaTableIV31 : Prop where
  finite_good : ∀ (W : WeierstrassCurve ℂ[X]) [(genericCurve W).IsElliptic]
    (M : RegularModel ℂ (genericCurve W)), M.IsRelativelyMinimal → M.HasSection →
    ∀ t : ℂ,SurfaceLocalData.GoodData W t → IsGoodFiber (fiberOver M (some t))
  finite_multiplicative : ∀ (W : WeierstrassCurve ℂ[X]) [(genericCurve W).IsElliptic]
    (M : RegularModel ℂ (genericCurve W)), M.IsRelativelyMinimal → M.HasSection →
    ∀ (t : ℂ) (n : ℕ),SurfaceLocalData.MultiplicativeData W t n →
      NeronPolygon.IsTypeI ℂ (fiberOver M (some t)) n
  infinity_multiplicative : ∀ (W V : WeierstrassCurve ℂ[X]) (d : ℕ)
    [(genericCurve W).IsElliptic],ReciprocalCompatibility W V d →
    ∀ M : RegularModel ℂ (genericCurve W),M.IsRelativelyMinimal → M.HasSection →
    ∀ n : ℕ,SurfaceLocalData.MultiplicativeData V 0 n →
      NeronPolygon.IsTypeI ℂ (fiberOver M none) n

/-- The homological Euler number of a geometric I_n fiber. -/
def SchuttShiodaSection67FiberEuler : Prop :=
  ∀ (W : WeierstrassCurve (RatFunc ℂ)) [W.IsElliptic] (M : RegularModel ℂ W),
    M.IsRelativelyMinimal → M.HasSection →
    ∀ (t : Option ℂ) (n : ℕ),NeronPolygon.IsTypeI ℂ (fiberOver M t) n →
      ComplexPointsTopology.HasFiniteHomology ℂ (fiberOver M t).left (fiberOver M t).hom 2 ∧
      ComplexPointsTopology.euler ℂ (fiberOver M t).left (fiberOver M t).hom 2=
        (Nat.card (irreducibleComponents (fiberOver M t).left) : ℤ)

/-- The numeric n is obtained from the polygon's proved component count. -/
theorem fiberEuler_eq (h : SchuttShiodaSection67FiberEuler)
    (W : WeierstrassCurve (RatFunc ℂ)) [W.IsElliptic] (M : RegularModel ℂ W)
    (hmin : M.IsRelativelyMinimal) (hs : M.HasSection) (t : Option ℂ) (n : ℕ)
    (hn : NeronPolygon.IsTypeI ℂ (fiberOver M t) n) :
    ComplexPointsTopology.HasFiniteHomology ℂ (fiberOver M t).left (fiberOver M t).hom 2 ∧
    ComplexPointsTopology.euler ℂ (fiberOver M t).left (fiberOver M t).hom 2=(n:ℤ) := by
  obtain ⟨hf,he⟩ := h W M hmin hs t n hn
  exact ⟨hf,he.trans (congrArg (fun a : ℕ=>(a:ℤ)) (NeronPolygon.IsTypeI.componentCount ℂ hn))⟩

end
end Common.Elliptic.ComplexEllipticSurfaceTheorems
