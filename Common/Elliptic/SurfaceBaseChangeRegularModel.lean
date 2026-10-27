module

public import Common.Elliptic.SurfaceBaseChangeGenericFiber

@[expose] public section

/-!
# Regularity and dimension of the constant-field surface model

The sources are Stacks Lemma 33.25.3 (tag 056S), smooth
over a field implies regular, and EGA IV_2 Corollary 4.1.4, invariance of
dimension under field extension for locally algebraic schemes. Both are stated on schemes.
Regularity and dimension are separate
from preservation of relative minimality under field extension.
-/
namespace Common.Elliptic.SurfaceBaseChange
noncomputable section
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits SurfaceModel
open SurfaceWeierstrassData
set_option backward.isDefEq.respectTransparency false
variable (k K : Type) [Field k] [Field K] [Algebra k K]

/-- Stacks Lemma 33.25.3, tag 056S. -/
def Stacks056SSmoothRegular : Prop :=
  ∀ (X : Scheme.{0}) (s : X ⟶ Spec (CommRingCat.of K)),Smooth s → IsRegularScheme X

/-- EGA IV_2, Corollary 4.1.4: dimension is invariant under extension
of the base field, p. 54. The cartesian square is the field extension. -/
def EGAIV2Corollary414 : Prop :=
  ∀ (X Y : Scheme.{0}) (s : X ⟶ Spec (CommRingCat.of k))
    (t : Y ⟶ Spec (CommRingCat.of K)) (p : Y ⟶ X),
    IsPullback p t s (Common.AlgebraicGeometry.K3BaseChange.extensionMap k K) →
    LocallyOfFiniteType s → topologicalKrullDim Y=topologicalKrullDim X

variable {W : WeierstrassCurve (RatFunc k)} (M : RegularModel k W)

theorem regular (h : Stacks056SSmoothRegular K) : IsRegularScheme (scheme k K M) := by
  let := smooth k K M
  exact h _ (structureMap k K M) (SmoothOfRelativeDimension.smooth 2 _)

theorem dimension (h : EGAIV2Corollary414 k K) : topologicalKrullDim (scheme k K M)=2 := by
  let : SmoothOfRelativeDimension 2 M.structureMap := M.smooth
  let : Smooth M.structureMap := SmoothOfRelativeDimension.smooth 2 _
  have he := h M.scheme (scheme k K M) M.structureMap (structureMap k K M)
    (coefficientMap k K M) (structure_isPullback k K M) inferInstance
  exact he.trans M.dimension

def regularModel (hReg : Stacks056SSmoothRegular K) (hDim : EGAIV2Corollary414 k K) :
    RegularModel K (W.map (constantExtension k K)) :=
  model k K M (regular k K M hReg) (dimension k K M hDim)

theorem regularModel_hasSection (hReg : Stacks056SSmoothRegular K)
    (hDim : EGAIV2Corollary414 k K) (hs : M.HasSection) :
    (regularModel k K M hReg hDim).HasSection := hasSection k K M hs

/-- Predicate for preservation of relative minimality under coefficient-field
extension. -/
def MinimalityPreserved : Prop :=
  ∀ (W : WeierstrassCurve (RatFunc k)) [W.IsElliptic] (M : RegularModel k W),
    M.IsRelativelyMinimal → ∀ (hr : IsRegularScheme (scheme k K M))
      (hd : topologicalKrullDim (scheme k K M)=2),
      (model k K M hr hd).IsRelativelyMinimal

end
end Common.Elliptic.SurfaceBaseChange
