import Common.AlgebraicGeometry.K3Surface
import Mathlib.RingTheory.Flat.Basic

/-!
# Field-extension diagrams

The extension morphism, fiber product and structure map below are
Mathlib schemes and maps. Structure-sheaf cohomology is defined in K3Surface;
the cartesian comparison and descent constructions are in K3CartesianDescent.
-/
namespace Common.AlgebraicGeometry.K3BaseChange
noncomputable section
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
variable (k K : Type) [Field k] [Field K] [Algebra k K]

def extensionMap : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k K))

abbrev scheme (X : Scheme.{0}) (s : X ⟶ Spec (CommRingCat.of k)) :=
  pullback s (extensionMap k K)

def structureMap (X : Scheme.{0}) (s : X ⟶ Spec (CommRingCat.of k)) :
    scheme k K X s ⟶ Spec (CommRingCat.of K) :=
  pullback.snd s (extensionMap k K)

end
end Common.AlgebraicGeometry.K3BaseChange
