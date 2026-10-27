import Common.AlgebraicGeometry.CanonicalBundleDescent
import Common.AlgebraicGeometry.ModuleExteriorPower

/-!
# Constructing the canonical module from numbered affine comparisons

The cotangent module is the conormal of the diagonal
(Stacks Lemma 29.33.7). Stacks Lemma 29.33.5 gives its affine differential
description. Stacks Lemma 26.7.2(2) identifies exterior powers on affines.
The exterior-power sheaf has already been constructed by
sheafifying exterior powers and semilinear restrictions.

The compatible degree-d presentation is assembled below.
-/
namespace Common.AlgebraicGeometry.CanonicalCotangentConstruction
noncomputable section
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open AffineDifferentialForms CanonicalModulePresentation
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000

def cotangent (k : Type) [Field k] (X : Scheme.{0})
    (s : X ⟶ Spec (CommRingCat.of k)) : X.Modules :=
  ConormalDegree.conormal (pullback.diagonal s)

structure CotangentDescription (k : Type) [Field k] (X : Scheme.{0})
    (s : X ⟶ Spec (CommRingCat.of k)) where
  affine : ∀ U : X.Opens,IsAffineOpen U →
    KaehlerDifferential k (sections k X s U) ≃ₗ[sections k X s U] Γ(cotangent k X s,U)
  compatible : ∀ (U V : X.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (h : V≤U) (a : sections k X s U),
    (cotangent k X s).presheaf.map (homOfLE h).op
      (affine U hU (KaehlerDifferential.D k (sections k X s U) a))=
      affine V hV (KaehlerDifferential.D k (sections k X s V) (restriction k X s U V h a))

/-- Stacks Lemma 29.33.5, with Omega defined by its diagonal conormal
as in Lemma 29.33.7. Restriction respects the canonical derivations. -/
def StacksLemma29335 (k : Type) [Field k] : Prop :=
  ∀ (X : Scheme.{0}) (s : X ⟶ Spec (CommRingCat.of k)),IsSeparated s →
    Nonempty (CotangentDescription k X s)

structure ExteriorDescription (X : Scheme.{0}) (M : X.Modules) (d : ℕ) where
  affine : ∀ U : X.Opens,IsAffineOpen U →
    (⋀[Γ(X,U)]^d Γ(M,U)) ≃ₗ[Γ(X,U)] Γ(ModuleExteriorPower.sheaf X M d,U)
  compatible : ∀ (U V : X.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (h : V≤U) (m : Fin d → Γ(M,U)),
    (ModuleExteriorPower.sheaf X M d).presheaf.map (homOfLE h).op
      (affine U hU (exteriorPower.ιMulti Γ(X,U) d m))=
      affine V hV (exteriorPower.ιMulti Γ(X,V) d
        (fun i=>M.presheaf.map (homOfLE h).op (m i)))
  quasicoherent : (ModuleExteriorPower.sheaf X M d).IsQuasicoherent

/-- Stacks Lemma 26.7.2(2), the exterior-power affine comparison
for a quasicoherent module, including naturality on elementary wedges. -/
def StacksLemma2672 : Prop :=
  ∀ (X : Scheme.{0}) (M : X.Modules),M.IsQuasicoherent →
    ∀ d : ℕ,Nonempty (ExteriorDescription X M d)

variable {R A B : Type} [CommRing R] [AddCommGroup A] [AddCommGroup B]
  [Module R A] [Module R B]

def wedgeEquiv (d : ℕ) (e : A ≃ₗ[R] B) : (⋀[R]^d A) ≃ₗ[R] (⋀[R]^d B) :=
  LinearEquiv.ofLinearMap (exteriorPower.map d e.toLinearMap)
    (exteriorPower.map d e.symm.toLinearMap)
    (by
      rw [← exteriorPower.map_comp]
      have h : e.toLinearMap.comp e.symm.toLinearMap=LinearMap.id := by ext x; simp
      rw [h,exteriorPower.map_id])
    (by
      rw [← exteriorPower.map_comp]
      have h : e.symm.toLinearMap.comp e.toLinearMap=LinearMap.id := by ext x; simp
      rw [h,exteriorPower.map_id])

@[simp] theorem wedgeEquiv_wedge (d : ℕ) (e : A ≃ₗ[R] B) (a : Fin d → A) :
    wedgeEquiv d e (exteriorPower.ιMulti R d a)=
      exteriorPower.ιMulti R d (fun i=>e (a i)) :=
  exteriorPower.map_apply_ιMulti e.toLinearMap a

def presentation (k : Type) [Field k] (X : Scheme.{0})
    (s : X ⟶ Spec (CommRingCat.of k)) (d : ℕ)
    (C : CotangentDescription k X s)
    (E : ExteriorDescription X (cotangent k X s) d) : Presentation k X s d where
  sheaf := ModuleExteriorPower.sheaf X (cotangent k X s) d
  affine U hU := (wedgeEquiv d (C.affine U hU)).trans (E.affine U hU)
  compatible U V hU hV h a := by
    dsimp only [LinearEquiv.trans_apply]
    rw [wedgeEquiv_wedge,wedgeEquiv_wedge]
    calc
      _=E.affine V hV (exteriorPower.ιMulti Γ(X,V) d (fun i=>
          (cotangent k X s).presheaf.map (homOfLE h).op
            (C.affine U hU (KaehlerDifferential.D k (sections k X s U) (a i))))) :=
        E.compatible U V hU hV h _
      _=_ := by
        congr 1
        congr 1
        funext i
        exact C.compatible U V hU hV h (a i)

theorem differential_module (k : Type) [Field k]
    (hCotangent : StacksLemma29335 k) (hExterior : StacksLemma2672)
    (hConormal : ConormalCohomologyComparison.Stacks01R1ConormalQuasicoherent) :
    CanonicalBundleDescent.Stacks502DifferentialModule k := by
  intro X s d hp
  let : IsProper s := hp
  obtain ⟨C⟩ := hCotangent X s inferInstance
  have hqc : (cotangent k X s).IsQuasicoherent :=
    hConormal _ _ (pullback.diagonal s) inferInstance
  obtain ⟨E⟩ := hExterior X (cotangent k X s) hqc d
  exact ⟨presentation k X s d C E,E.quasicoherent⟩

end
end Common.AlgebraicGeometry.CanonicalCotangentConstruction
