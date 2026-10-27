module

public import Common.AlgebraicGeometry.ProjectiveLine
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

@[expose] public section

/-!
# Split Kodaira I_n fibers

A polygon is the reduced scheme obtained by pinching n copies of
P1 at infinity and zero in cyclic order. The definition retains the
pushout square, finite normalization morphism, node embedding and
images of the irreducible components. For n=1 it is the nodal
rational curve; n=2 has two components meeting at two distinct nodes.
No polynomial vanishing order or assigned integer is called a fiber type.

References: Deligne–Rapoport, Les schemas de modules de courbes
elliptiques (1973), II.1.1 (standard Neron polygons); Miranda, The Basic
Theory of Elliptic Surfaces (1989), I.4, pp. 5–6 and IV.3.1, p. 41.
-/
namespace Common.Elliptic.NeronPolygon
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable (k : Type) [Field k]

abbrev Base := Spec (CommRingCat.of k)
def point : Over (Base k) := Over.mk (𝟙 (Base k))
def line : Over (Base k) := Over.mk (ProjectiveLine.structureMap k)

def zero : point k ⟶ line k :=
  Over.homMk (ProjectiveLine.affinePoint k k 0) (by
    change ProjectiveLine.affinePoint k k 0 ≫ ProjectiveLine.structureMap k = 𝟙 _
    convert ProjectiveLine.affinePoint_over k k 0 using 1
    change 𝟙 _ = Spec.map (𝟙 _)
    exact (Spec.map_id _).symm)

def infinity : point k ⟶ line k :=
  Over.homMk (ProjectiveLine.infinityPoint k k) (by
    change ProjectiveLine.infinityPoint k k ≫ ProjectiveLine.structureMap k = 𝟙 _
    convert ProjectiveLine.infinityPoint_over k k using 1
    change 𝟙 _ = Spec.map (𝟙 _)
    exact (Spec.map_id _).symm)

def normalization (n : ℕ) : Over (Base k) := ∐ fun _ : Fin n=>line k
def nodes (n : ℕ) : Over (Base k) := ∐ fun _ : Fin n=>point k
def branches (n : ℕ) : Over (Base k) := ∐ fun _ : Fin n × Bool=>point k

def next {n : ℕ} (hn : 0<n) (i : Fin n) : Fin n :=
  ⟨(i.val+1)%n,Nat.mod_lt _ hn⟩

def branchToNormalization (n : ℕ) (hn : 0<n) : branches k n ⟶ normalization k n :=
  Sigma.desc (fun i : Fin n × Bool=>
    if i.2 then zero k≫Sigma.ι (fun _ : Fin n=>line k) (next hn i.1)
    else infinity k≫Sigma.ι (fun _ : Fin n=>line k) i.1)

def branchToNodes (n : ℕ) : branches k n ⟶ nodes k n :=
  Sigma.desc (fun i : Fin n × Bool=>Sigma.ι (fun _ : Fin n=>point k) i.1)

/-- A scheme-theoretic split n-gon, with its component images. -/
structure Presentation (F : Over (Base k)) (n : ℕ) where
  positive : 0<n
  normalizationMap : normalization k n ⟶ F
  nodeMap : nodes k n ⟶ F
  pushout : IsPushout (branchToNormalization k n positive) (branchToNodes k n)
    normalizationMap nodeMap
  reduced : IsReduced F.left
  finite_normalization : IsFinite normalizationMap.left
  nodes_closed : IsClosedImmersion nodeMap.left
  components : Fin n ≃ irreducibleComponents F.left
  component_range (i : Fin n) :
    Set.range ((Sigma.ι (fun _ : Fin n=>line k) i≫normalizationMap).left)=
      (components i : Set F.left)

/-- A geometric Kodaira I_n fiber is a Neron n-gon. -/
def IsTypeI (F : Over (Base k)) (n : ℕ) : Prop := Nonempty (Presentation k F n)

theorem IsTypeI.componentCount {F : Over (Base k)} {n : ℕ} (h : IsTypeI k F n) :
    Nat.card (irreducibleComponents F.left)=n := by
  obtain ⟨P⟩ := h
  rw [←Nat.card_congr P.components]
  simp

theorem IsTypeI.finite_components {F : Over (Base k)} {n : ℕ} (h : IsTypeI k F n) :
    Finite (irreducibleComponents F.left) := by
  obtain ⟨P⟩ := h
  exact Finite.of_equiv (Fin n) P.components

end
end Common.Elliptic.NeronPolygon
