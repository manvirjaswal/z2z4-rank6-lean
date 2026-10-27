import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.CategoryTheory.Monoidal.CommGrp_

/-!
# Jacobians by Albanese universal properties

An abelian variety is a smooth proper geometrically connected
commutative group scheme. The definition of a Jacobian below uses its
universal properties for morphisms to arbitrary abelian varieties. The
basepoint-free version uses a difference map from the square of the curve.
All maps, group laws and isomorphisms are morphisms of schemes.

Reference: J. S. Milne, *Jacobian Varieties*, in *Arithmetic Geometry*
(Springer, 1986), Propositions 6.1 and 6.4 and Remark 6.5, pp. 185–187;
corrected author reprint dated 12 June 2021, pp. 19–21,
https://www.jmilne.org/math/xnotes/JVs.pdf.
Remark 7.7 also discusses this characterization of the Jacobian.

The definitions do not assert existence, identify a concrete curve, or
choose an equation for a Jacobian. In particular, Weierstrass Jacobian
coordinates play no role here.
-/

noncomputable section

namespace AlgebraicGeometry.Jacobian

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.MonObj
open CategoryTheory.CartesianMonoidalCategory

universe u

variable (S : Scheme.{u})

local instance overCartesian : CartesianMonoidalCategory (Over S) :=
  Over.cartesianMonoidalCategory S

local instance overBraided : BraidedCategory (Over S) := Over.braidedCategory S

/-- A smooth proper geometrically connected commutative group scheme. -/
structure AbelianVariety where
  group : CommGrp (Over S)
  proper : IsProper group.X.hom
  smooth : Smooth group.X.hom
  geometricallyConnected : GeometricallyConnected group.X.hom

variable {S}

/-- The zero section of an abelian variety, as an over-scheme map. -/
def AbelianVariety.zero (A : AbelianVariety S) : 𝟙_ (Over S) ⟶ A.group.X := η

/-- The underlying over-scheme map of a homomorphism of abelian varieties. -/
def AbelianVariety.homMap {A B : AbelianVariety S} (f : A.group ⟶ B.group) :
    A.group.X ⟶ B.group.X := f.hom.hom.hom

@[simp] theorem AbelianVariety.homMap_id (A : AbelianVariety S) :
    homMap (𝟙 A.group) = 𝟙 A.group.X := rfl

@[simp] theorem AbelianVariety.homMap_comp {A B C : AbelianVariety S}
    (f : A.group ⟶ B.group) (g : B.group ⟶ C.group) :
    homMap (f ≫ g) = homMap f ≫ homMap g := rfl

/-- Milne's pointed Albanese universal property, with group-scheme
homomorphisms in the unique factorization. -/
def IsAlbanese (C : Over S) (p : 𝟙_ (Over S) ⟶ C)
    (A : AbelianVariety S) (a : C ⟶ A.group.X) : Prop :=
  p ≫ a = A.zero ∧
    ∀ (B : AbelianVariety S) (f : C ⟶ B.group.X), p ≫ f = B.zero →
      ∃! g : A.group ⟶ B.group, a ≫ AbelianVariety.homMap g = f

/-- A realization of a Jacobian by a specified over-scheme.
The base point and Abel map are included, as is the full universal property.
The target equation is identified by an over-scheme isomorphism. -/
structure PointedAlbanesePresentation (C J : Over S) where
  abelian : AbelianVariety S
  carrierIso : J ≅ abelian.group.X
  basepoint : 𝟙_ (Over S) ⟶ C
  abel : C ⟶ abelian.group.X
  universal : IsAlbanese C basepoint abelian abel

/-- The specified scheme is isomorphic over the base to the Jacobian
of the pointed smooth proper curve. Existence is not postulated. -/
def HasPointedAlbanesePresentation (C J : Over S) : Prop := Nonempty (PointedAlbanesePresentation C J)

/-- A pointed presentation additionally fixes the identity of the displayed
target model. -/
structure PointedPresentation (C J : Over S) (o : 𝟙_ (Over S) ⟶ J)
    extends PointedAlbanesePresentation C J where
  origin : o ≫ carrierIso.hom = abelian.zero

def IsPointedJacobian (C J : Over S) (o : 𝟙_ (Over S) ⟶ J) : Prop :=
  Nonempty (PointedPresentation C J o)

theorem hasPointedAlbanesePresentation_of_pointed {C J : Over S} {o : 𝟙_ (Over S) ⟶ J}
    (h : IsPointedJacobian C J o) : HasPointedAlbanesePresentation C J := by
  rcases h with ⟨P⟩
  exact ⟨P.toPointedAlbanesePresentation⟩

/-- Changing the displayed target by a base-preserving scheme
isomorphism preserves the Jacobian claim. -/
def PointedAlbanesePresentation.targetIso {C J J' : Over S} (P : PointedAlbanesePresentation C J)
    (e : J' ≅ J) : PointedAlbanesePresentation C J' where
  abelian := P.abelian
  carrierIso := e ≪≫ P.carrierIso
  basepoint := P.basepoint
  abel := P.abel
  universal := P.universal

theorem hasPointedAlbanesePresentation_targetIso {C J J' : Over S} (e : J' ≅ J)
    (h : HasPointedAlbanesePresentation C J) : HasPointedAlbanesePresentation C J' := by
  rcases h with ⟨P⟩
  exact ⟨P.targetIso e⟩

/-- Changing the source by a base-preserving isomorphism transports
the base point, Abel map and every unique factorization. -/
def PointedAlbanesePresentation.sourceIso {C C' J : Over S} (P : PointedAlbanesePresentation C J)
    (e : C' ≅ C) : PointedAlbanesePresentation C' J where
  abelian := P.abelian
  carrierIso := P.carrierIso
  basepoint := P.basepoint ≫ e.inv
  abel := e.hom ≫ P.abel
  universal := by
    constructor
    · simpa [Category.assoc] using P.universal.1
    · intro B f hf
      obtain ⟨g, hg, hu⟩ := P.universal.2 B (e.inv ≫ f) (by
        simpa [Category.assoc] using hf)
      refine ⟨g, ?_, ?_⟩
      · simpa [Category.assoc] using congrArg (fun q => e.hom ≫ q) hg
      · intro g' hg'
        apply hu g'
        simpa [Category.assoc] using congrArg (fun q => e.inv ≫ q) hg'

theorem hasPointedAlbanesePresentation_sourceIso {C C' J : Over S} (e : C' ≅ C)
    (h : HasPointedAlbanesePresentation C J) : HasPointedAlbanesePresentation C' J := by
  rcases h with ⟨P⟩
  exact ⟨P.sourceIso e⟩

/-- Transport a pointed target while preserving its specified zero
section. -/
def PointedPresentation.targetIso {C J J' : Over S}
    {o : 𝟙_ (Over S) ⟶ J} {o' : 𝟙_ (Over S) ⟶ J'}
    (P : PointedPresentation C J o) (e : J' ≅ J) (ho : o' ≫ e.hom = o) :
    PointedPresentation C J' o' where
  toPointedAlbanesePresentation := P.toPointedAlbanesePresentation.targetIso e
  origin := by
    change o' ≫ (e.hom ≫ P.carrierIso.hom) = P.abelian.zero
    rw [← Category.assoc, ho]
    exact P.origin

theorem isPointedJacobian_targetIso {C J J' : Over S}
    {o : 𝟙_ (Over S) ⟶ J} {o' : 𝟙_ (Over S) ⟶ J'}
    (e : J' ≅ J) (ho : o' ≫ e.hom = o)
    (h : IsPointedJacobian C J o) : IsPointedJacobian C J' o' := by
  rcases h with ⟨P⟩
  exact ⟨P.targetIso e ho⟩

/-- The diagonal of an over-scheme, using its fiber product. -/
def diagonal (C : Over S) : C ⟶ C ⊗ C := lift (𝟙 C) (𝟙 C)

/-- Milne's basepoint-free Albanese universal property (Proposition 6.4).
The difference map is zero on the diagonal, and is universal among
all such scheme maps to abelian varieties. -/
def IsUnpointedAlbanese (C : Over S) (A : AbelianVariety S)
    (difference : C ⊗ C ⟶ A.group.X) : Prop :=
  diagonal C ≫ difference = toUnit C ≫ A.zero ∧
    ∀ (B : AbelianVariety S) (f : C ⊗ C ⟶ B.group.X),
      diagonal C ≫ f = toUnit C ≫ B.zero →
        ∃! g : A.group ⟶ B.group, difference ≫ AbelianVariety.homMap g = f

/-- A Jacobian realization of a curve by a target scheme.
It does not require a rational point on the curve. -/
structure Presentation (C J : Over S) where
  abelian : AbelianVariety S
  carrierIso : J ≅ abelian.group.X
  difference : C ⊗ C ⟶ abelian.group.X
  universal : IsUnpointedAlbanese C abelian difference

/-- The displayed scheme is the Jacobian, characterized by Milne's
basepoint-free Albanese property and an over-base isomorphism.
No rational point, equation or Jacobian existence is built into this definition. -/
def IsJacobian (C J : Over S) : Prop := Nonempty (Presentation C J)

def Presentation.targetIso {C J J' : Over S} (P : Presentation C J)
    (e : J' ≅ J) : Presentation C J' where
  abelian := P.abelian
  carrierIso := e ≪≫ P.carrierIso
  difference := P.difference
  universal := P.universal

theorem isJacobian_targetIso {C J J' : Over S} (e : J' ≅ J)
    (h : IsJacobian C J) : IsJacobian C J' := by
  rcases h with ⟨P⟩
  exact ⟨P.targetIso e⟩

/-- The universal property determines the abelian variety up to a
group-scheme isomorphism. This is proved categorically. -/
def Presentation.groupIso {C J J' : Over S} (P : Presentation C J)
    (Q : Presentation C J') : P.abelian.group ≅ Q.abelian.group := by
  classical
  let f := (P.universal.2 Q.abelian Q.difference Q.universal.1).choose
  have hf : P.difference ≫ AbelianVariety.homMap f = Q.difference :=
    (P.universal.2 Q.abelian Q.difference Q.universal.1).choose_spec.1
  let g := (Q.universal.2 P.abelian P.difference P.universal.1).choose
  have hg : Q.difference ≫ AbelianVariety.homMap g = P.difference :=
    (Q.universal.2 P.abelian P.difference P.universal.1).choose_spec.1
  have hfg : f ≫ g = 𝟙 P.abelian.group := by
    obtain ⟨h, _, hu⟩ := P.universal.2 P.abelian P.difference P.universal.1
    apply (hu (f ≫ g) ?_).trans (hu (𝟙 P.abelian.group) ?_).symm
    · rw [AbelianVariety.homMap_comp, ← Category.assoc, hf, hg]
    · simp
  have hgf : g ≫ f = 𝟙 Q.abelian.group := by
    obtain ⟨h, _, hu⟩ := Q.universal.2 Q.abelian Q.difference Q.universal.1
    apply (hu (g ≫ f) ?_).trans (hu (𝟙 Q.abelian.group) ?_).symm
    · rw [AbelianVariety.homMap_comp, ← Category.assoc, hg, hf]
    · simp
  exact ⟨f, g, hfg, hgf⟩

/-- Two displayed Jacobian models are isomorphic over their base. -/
def Presentation.modelIso {C J J' : Over S} (P : Presentation C J)
    (Q : Presentation C J') : J ≅ J' :=
  P.carrierIso ≪≫ (CommGrp.forget (Over S)).mapIso (P.groupIso Q) ≪≫ Q.carrierIso.symm

theorem isJacobian_unique {C J J' : Over S}
    (h : IsJacobian C J) (h' : IsJacobian C J') : Nonempty (J ≅ J') := by
  rcases h with ⟨P⟩
  rcases h' with ⟨Q⟩
  exact ⟨P.modelIso Q⟩

end AlgebraicGeometry.Jacobian
