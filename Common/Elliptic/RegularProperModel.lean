module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

@[expose] public section

/-!
# Regular proper models of curves over a local ring

The definitions follow B. Conrad, *Minimal models for elliptic curves*
(21 November 2015), Definition 3.1, p. 6, and Definition 3.8, p. 8.
Regularity means regularity of every local ring. A model has a
proper flat structure map and a generic-fiber isomorphism.
Minimality means that every contraction to another regular proper model
is an isomorphism. The geometric special fiber and its components are
scheme-theoretic pullbacks and topological irreducible components.
-/

namespace Common.Elliptic

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

/-- A scheme is regular when all of its local rings are regular local rings. -/
def IsRegularScheme (X : Scheme.{u}) : Prop :=
  ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x)

section Models

variable (R K : Type u) [CommRing R] [Field K] [Algebra R K]
variable (C : Scheme.{u}) (c : C ⟶ Spec (CommRingCat.of K))

/-- The generic-point morphism supplied by the coefficient embedding. -/
def genericBaseMap : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R K))

/-- A regular proper model of the specified scheme over the fraction field.
For a DVR, this is Conrad's Definition 3.1 with properness and regularity. -/
structure RegularProperModel where
  scheme : Scheme.{u}
  structureMap : scheme ⟶ Spec (CommRingCat.of R)
  proper : IsProper structureMap
  flat : Flat structureMap
  regular : IsRegularScheme scheme
  genericIso : pullback structureMap (genericBaseMap R K) ≅ C
  genericIso_over : genericIso.hom ≫ c = pullback.snd structureMap (genericBaseMap R K)

namespace RegularProperModel

variable {R K C c}

attribute [instance] proper flat

/-- The identified generic fiber embeds into the model. -/
def genericInclusion (M : RegularProperModel R K C c) : C ⟶ M.scheme :=
  M.genericIso.inv ≫ pullback.fst M.structureMap (genericBaseMap R K)

@[reassoc]
theorem genericInclusion_over (M : RegularProperModel R K C c) :
    M.genericInclusion ≫ M.structureMap = c ≫ genericBaseMap R K := by
  simp only [genericInclusion, Category.assoc, pullback.condition]
  rw [← M.genericIso_over]
  simp only [Category.assoc, M.genericIso.inv_hom_id_assoc]

/-- A model morphism respects both the local base and the generic-fiber
identification. These are the morphisms in Conrad's model category. -/
structure Hom (M N : RegularProperModel R K C c) where
  hom : M.scheme ⟶ N.scheme
  over : hom ≫ N.structureMap = M.structureMap
  generic : M.genericInclusion ≫ hom = N.genericInclusion

/-- The identity morphism of a model. -/
def Hom.id (M : RegularProperModel R K C c) : Hom M M where
  hom := 𝟙 M.scheme
  over := Category.id_comp _
  generic := Category.comp_id _

/-- Composition of morphisms preserving the chosen generic fiber. -/
def Hom.comp {M N P : RegularProperModel R K C c} (f : Hom M N) (g : Hom N P) :
    Hom M P where
  hom := f.hom ≫ g.hom
  over := by rw [Category.assoc, g.over, f.over]
  generic := by rw [← Category.assoc, f.generic, g.generic]

/-- A minimal regular proper model admits no nontrivial contraction to a
regular proper model of the same generic fiber (Conrad, Definition 3.8). -/
def IsMinimal (M : RegularProperModel R K C c) : Prop :=
  ∀ (N : RegularProperModel R K C c) (f : Hom M N), IsIso f.hom

/-- The minimal-model universal property of Conrad, Theorem 3.10 and
Remark 3.11, p. 8, retained as a separate property. -/
def IsTerminal (M : RegularProperModel R K C c) : Prop :=
  ∀ N : RegularProperModel R K C c, ∃! _f : Hom N M, True

/-- Reidentify the generic fiber by an isomorphism over the field.
The integral model, regularity and geometric special fiber are unchanged. -/
def transport {D : Scheme.{u}} {d : D ⟶ Spec (CommRingCat.of K)}
    (M : RegularProperModel R K C c) (e : C ≅ D) (he : e.hom ≫ d = c) :
    RegularProperModel R K D d where
  scheme := M.scheme
  structureMap := M.structureMap
  proper := M.proper
  flat := M.flat
  regular := M.regular
  genericIso := M.genericIso ≪≫ e
  genericIso_over := by simp only [Iso.trans_hom, Category.assoc, he, M.genericIso_over]

@[reassoc]
theorem transport_genericInclusion {D : Scheme.{u}} {d : D ⟶ Spec (CommRingCat.of K)}
    (M : RegularProperModel R K C c) (e : C ≅ D) (he : e.hom ≫ d = c) :
    (M.transport e he).genericInclusion = e.inv ≫ M.genericInclusion := by
  simp only [transport, genericInclusion, Iso.trans_inv, Category.assoc]

theorem transport_isMinimal {D : Scheme.{u}} {d : D ⟶ Spec (CommRingCat.of K)}
    (M : RegularProperModel R K C c) (hM : M.IsMinimal)
    (e : C ≅ D) (he : e.hom ≫ d = c) : (M.transport e he).IsMinimal := by
  intro N f
  have hei : e.inv ≫ c = d := by rw [← he, e.inv_hom_id_assoc]
  let N' := N.transport e.symm hei
  let f' : Hom M N' := {
    hom := f.hom
    over := f.over
    generic := by
      change M.genericInclusion ≫ f.hom = e.hom ≫ N.genericInclusion
      calc
        M.genericInclusion ≫ f.hom =
            e.hom ≫ (e.inv ≫ (M.genericInclusion ≫ f.hom)) :=
          (e.hom_inv_id_assoc _).symm
        _ = e.hom ≫ ((M.transport e he).genericInclusion ≫ f.hom) := by
          rw [transport_genericInclusion, Category.assoc]
        _ = e.hom ≫ N.genericInclusion := congrArg (fun g => e.hom ≫ g) f.generic }
  exact hM N' f'

section SpecialFiber

variable [IsLocalRing R]

/-- The algebraic closure of the residue field, viewed over the base. -/
def geometricClosedPoint :
    Spec (CommRingCat.of (AlgebraicClosure (IsLocalRing.ResidueField R))) ⟶
      Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom
    ((algebraMap (IsLocalRing.ResidueField R)
      (AlgebraicClosure (IsLocalRing.ResidueField R))).comp (IsLocalRing.residue R)))

/-- The geometric special fiber of the model. -/
def geometricSpecialFiber (M : RegularProperModel R K C c) : Scheme.{u} :=
  pullback M.structureMap (geometricClosedPoint (R := R))

/-- The geometric component count is the cardinality of the
irreducible-component set. Finiteness is explicit in later applications. -/
def geometricComponentCount (M : RegularProperModel R K C c) : ℕ :=
  Nat.card (irreducibleComponents M.geometricSpecialFiber)

theorem transport_geometricComponentCount
    {D : Scheme.{u}} {d : D ⟶ Spec (CommRingCat.of K)}
    (M : RegularProperModel R K C c) (e : C ≅ D) (he : e.hom ≫ d = c) :
    (M.transport e he).geometricComponentCount = M.geometricComponentCount := rfl

theorem geometricComponents_finite (M : RegularProperModel R K C c)
    [IsNoetherian M.geometricSpecialFiber] :
    (irreducibleComponents M.geometricSpecialFiber).Finite :=
  TopologicalSpace.NoetherianSpace.finite_irreducibleComponents

/-- Properness over the residue-field closure makes the geometric special
fiber Noetherian, so its component count never uses Nat.card's infinite case. -/
instance geometricSpecialFiber_noetherian (M : RegularProperModel R K C c) :
    IsNoetherian M.geometricSpecialFiber := by
  let f := pullback.snd M.structureMap (geometricClosedPoint (R := R))
  have : IsLocallyNoetherian M.geometricSpecialFiber :=
    LocallyOfFiniteType.isLocallyNoetherian f
  let : CompactSpace M.geometricSpecialFiber :=
    QuasiCompact.compactSpace_of_compactSpace f
  exact { __ := this }

/-- The geometric component type is finite for every proper model.
This rules out the infinite-type fallback in Nat.card. -/
theorem geometricComponentType_finite (M : RegularProperModel R K C c) :
    Finite (irreducibleComponents M.geometricSpecialFiber) := by
  let : IsNoetherian M.geometricSpecialFiber := geometricSpecialFiber_noetherian M
  exact (geometricComponents_finite M).to_subtype

end SpecialFiber
end RegularProperModel
end Models
end
end Common.Elliptic
