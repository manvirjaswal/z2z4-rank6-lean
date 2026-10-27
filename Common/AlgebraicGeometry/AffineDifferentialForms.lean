module

public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Tactic

@[expose] public section

/-!
# Differential forms on the affine basis of a scheme

On an affine open `U`, the module of `d`-forms is the exterior
power of the Kähler differentials of its coordinate algebra. Compatible
generators on the affine basis express a trivial canonical bundle on a
smooth `d`-dimensional scheme.

References: Stacks Project, Lemma 29.33.5 and Remark 29.33.6
(Section tag 01UM), and Lemma 29.35.12 (tag 02G1).
-/

namespace Common.AlgebraicGeometry.AffineDifferentialForms

open _root_.AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
noncomputable section

variable (k : Type) [Field k]

section Maps

variable {A B : Type} [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]

/-- Restrict the scalars of an alternating map. -/
def restrictAlternatingScalars {M N : Type} [AddCommGroup M] [AddCommGroup N]
    [Module A M] [Module A N] [Module B M] [Module B N] [Algebra A B]
    [IsScalarTower A B M] [IsScalarTower A B N] {ι : Type}
    (f : M [⋀^ι]→ₗ[B] N) : M [⋀^ι]→ₗ[A] N where
  toMultilinearMap := f.toMultilinearMap.restrictScalars A
  map_eq_zero_of_eq' := f.map_eq_zero_of_eq

end Maps

/-- The coordinate algebra on a scheme open, with the scalar
map induced by the structure morphism. -/
def sections (X : Scheme.{0}) (s : X ⟶ Spec (CommRingCat.of k)) (U : X.Opens) :
    CommAlgCat k := by
  let f : k →+* ↥(X.presheaf.obj (op U)) :=
    (((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ s.appTop) ≫
      X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op).hom
  letI := f.toAlgebra
  exact CommAlgCat.of k ↥(X.presheaf.obj (op U))

/-- Degree-`d` differential forms on an affine coordinate algebra.
The definition is also available on other opens, but the canonical
bundle definition below only uses affine opens. -/
abbrev Forms (X : Scheme.{0}) (s : X ⟶ Spec (CommRingCat.of k))
    (U : X.Opens) (d : ℕ) : Type :=
  ↥(⋀[sections k X s U]^d (KaehlerDifferential k (sections k X s U)))

/-- The restriction homomorphism of coordinate rings. -/
def restriction (X : Scheme.{0}) (s : X ⟶ Spec (CommRingCat.of k))
    (U V : X.Opens) (h : V ≤ U) : sections k X s U →+* sections k X s V :=
  (X.presheaf.map (homOfLE h).op).hom

/-- A trivialization of the top differential module on the affine basis.

The compatibility equation is given on the canonical spanning family
`da₁ ∧ ... ∧ da_d`. Its left side restricts the coefficient in the
trivialization on `U`; its right side first restricts the functions and
then computes the coefficient in the trivialization on `V`. Thus it
expresses compatibility of differential forms, with the
structure-map scalar action, rather than arbitrary identifications of
the underlying vector spaces. -/
structure CanonicalTrivialization (X : Scheme.{0})
    (s : X ⟶ Spec (CommRingCat.of k)) (d : ℕ) where
  coefficient : ∀ (U : X.Opens), IsAffineOpen U →
    Forms k X s U d ≃ₗ[sections k X s U] sections k X s U
  compatible : ∀ (U V : X.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (h : V ≤ U) (a : Fin d → sections k X s U),
    restriction k X s U V h
      (coefficient U hU (exteriorPower.ιMulti (sections k X s U) d
        (fun i => KaehlerDifferential.D k (sections k X s U) (a i)))) =
      coefficient V hV (exteriorPower.ιMulti (sections k X s V) d
        (fun i => KaehlerDifferential.D k (sections k X s V)
          (restriction k X s U V h (a i))))

/-- Triviality of the degree-`d` differential sheaf, expressed
on the affine basis. On a smooth `d`-fold this is canonical triviality. -/
def HasTrivialCanonical (X : Scheme.{0}) (s : X ⟶ Spec (CommRingCat.of k))
    (d : ℕ) : Prop := Nonempty (CanonicalTrivialization k X s d)

end
end Common.AlgebraicGeometry.AffineDifferentialForms
