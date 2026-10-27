module

public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.AlgebraicTopology.SingularHomology.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian

@[expose] public section

/-!
# Complex points with the classical topology and singular homology

For each affine open, evaluation on all regular functions embeds its
complex points into a product of copies of C. The final topology for
these affine charts is the classical complex topology on a scheme of
finite type over a subfield of C. Betti groups below are rational singular
homology groups. Euler characteristics are finite alternating sums of
their dimensions, always accompanied by finite-dimensionality and
vanishing bounds where a published Euler theorem is applied.

Reference: Serre, Geometrie algebrique et geometrie analytique (1956),
§1, pp. 1–3 (classical topology via affine embeddings); Hatcher,
Algebraic Topology (2002), §2.2, p. 146 (Euler characteristic and homology).
The topology uses all regular functions, so does not choose generators.
-/
namespace AlgebraicGeometry.ComplexPointsTopology
noncomputable section
open CategoryTheory Opposite
open scoped Classical

variable (k : Type) [Field k] [Algebra k ℂ]

abbrev Base := Spec (CommRingCat.of k)
def complexBaseMap : Spec (CommRingCat.of ℂ) ⟶ Base k :=
  Spec.map (CommRingCat.ofHom (algebraMap k ℂ))

abbrev Points (X : Scheme.{0}) (s : X ⟶ Base k) :=
  {p : Spec (CommRingCat.of ℂ) ⟶ X // p≫s=complexBaseMap k}

/-- Evaluation of a regular function at a complex-valued point. -/
def evaluation (U : Scheme.{0}) (p : Spec (CommRingCat.of ℂ) ⟶ U) :
    ↥(U.presheaf.obj (op ⊤)) → ℂ :=
  fun a=>(Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom (p.appTop.hom a)

@[instance_reducible] def affineTopology (U : Scheme.{0}) (s : U ⟶ Base k) :
    TopologicalSpace (Points k U s) :=
  TopologicalSpace.induced (fun p=>evaluation U p.val) inferInstance

def chartMap (X : Scheme.{0}) (s : X ⟶ Base k) (U : X.Opens) :
    Points k U.toScheme (U.ι≫s) → Points k X s :=
  fun p=>⟨p.val≫U.ι,by simpa only [Category.assoc] using p.property⟩

/-- The classical topology is final for every affine chart. -/
@[instance_reducible] def topology (X : Scheme.{0}) (s : X ⟶ Base k) :
    TopologicalSpace (Points k X s) :=
  ⨆ (U : X.Opens) (_hU : IsAffineOpen U),
    TopologicalSpace.coinduced (chartMap k X s U) (affineTopology k U.toScheme (U.ι≫s))

def space (X : Scheme.{0}) (s : X ⟶ Base k) : TopCat :=
  @TopCat.of (Points k X s) (topology k X s)

abbrev Homology (X : Scheme.{0}) (s : X ⟶ Base k) (i : ℕ) :=
  ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℚ) i).obj (ModuleCat.of ℚ ℚ)).obj
    (space k X s)

/-- Betti number, used only with an explicit finite-dimensionality proof. -/
def betti (X : Scheme.{0}) (s : X ⟶ Base k) (i : ℕ) : ℕ :=
  Module.finrank ℚ (Homology k X s i)

/-- Bounded topological Euler characteristic. A complex d-fold uses 2d. -/
def euler (X : Scheme.{0}) (s : X ⟶ Base k) (bound : ℕ) : ℤ :=
  ∑ i∈Finset.range (bound+1),(-1 : ℤ)^i*(betti k X s i : ℤ)

/-- Finite Betti groups and vanishing beyond the dimension bound. -/
structure HasFiniteHomology (X : Scheme.{0}) (s : X ⟶ Base k) (bound : ℕ) : Prop where
  finite (i : ℕ) : FiniteDimensional ℚ (Homology k X s i)
  vanishes (i : ℕ) (hi : bound < i) : Subsingleton (Homology k X s i)

end
end AlgebraicGeometry.ComplexPointsTopology
