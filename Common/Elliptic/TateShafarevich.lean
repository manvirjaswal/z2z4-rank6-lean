import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.Basic.Real.Basic

/-!
# Continuous first Galois cohomology of elliptic curves

The coefficients are the nonsingular points over the algebraic
closure, with their discrete topology and coordinatewise Galois action.
Continuous one-cocycles are divided by principal coboundaries.

References: Silverman, The Arithmetic of Elliptic Curves, second edition,
Appendix B, pp. 416, 418–419. The Shafarevich–Tate local condition is X.4,
p. 332, including the independence of closure embeddings in Remark 4.1.1.
The left-action cocycle convention is the inverse-index version of the
book's right-action convention.
-/
namespace Common.Elliptic.TateShafarevich
noncomputable section
open WeierstrassCurve
open scoped Classical

variable (W : WeierstrassCurve ℚ) (K : Type) [Field K] [CharZero K]

abbrev GeometricPoints := (W.baseChange (AlgebraicClosure K)).toAffine.Point
abbrev GaloisGroup := Field.absoluteGaloisGroup K

instance geometricPointsTopology : TopologicalSpace (GeometricPoints W K) := ⊥
instance geometricPointsDiscrete : DiscreteTopology (GeometricPoints W K) := ⟨rfl⟩

def action (σ : GaloisGroup K) : GeometricPoints W K →+ GeometricPoints W K :=
  Affine.Point.map (W' := W.toAffine) ((σ.restrictScalars ℚ).toAlgHom)

@[simp] theorem action_zero (σ : GaloisGroup K) : action W K σ 0 = 0 := map_zero _
@[simp] theorem action_add (σ : GaloisGroup K) (P Q : GeometricPoints W K) :
    action W K σ (P+Q)=action W K σ P+action W K σ Q := map_add _ _ _

@[simp] theorem action_one (P : GeometricPoints W K) : action W K 1 P=P := by
  exact Affine.Point.map_id P

theorem action_mul (σ τ : GaloisGroup K) (P : GeometricPoints W K) :
    action W K (σ*τ) P=action W K σ (action W K τ P) := by
  symm
  exact Affine.Point.map_map _ _ P

instance geometricPointsMulAction : DistribMulAction (GaloisGroup K) (GeometricPoints W K) where
  smul σ P := action W K σ P
  one_smul := action_one W K
  mul_smul := action_mul W K
  smul_zero := action_zero W K
  smul_add := action_add W K

instance geometricPointsContinuousAction :
    ContinuousSMul (GaloisGroup K) (GeometricPoints W K) := by
  apply continuousSMul_iff_stabilizer_isOpen.mpr
  intro P
  cases P with
  | zero =>
      change IsOpen {σ : GaloisGroup K | action W K σ 0=0}
      simp
  | some x y h =>
      have hx := stabilizer_isOpen_of_isIntegral (K := K) (L := AlgebraicClosure K) x
      have hy := stabilizer_isOpen_of_isIntegral (K := K) (L := AlgebraicClosure K) y
      have heq : {σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K |
          action W K σ (Affine.Point.some x y h)=Affine.Point.some x y h}=
          (MulAction.stabilizer (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) x :
            Set (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)) ∩
          (MulAction.stabilizer (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) y :
            Set (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)) := by
        ext σ
        change action W K σ (.some x y h)=.some x y h ↔ σ x=x ∧ σ y=y
        simp only [action,Affine.Point.map_some,Affine.Point.some.injEq]
        rfl
      change IsOpen {σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K |
        action W K σ (Affine.Point.some x y h)=Affine.Point.some x y h}
      rw [heq]
      exact hx.inter hy

/-- Continuous cocycles for the coordinate Galois action. -/
def cocycles : AddSubgroup C(GaloisGroup K,GeometricPoints W K) where
  carrier := {c | ∀ σ τ,c (σ*τ)=c σ+action W K σ (c τ)}
  zero_mem' := by intro σ τ; simp
  add_mem' := by
    intro c d hc hd σ τ
    simp only [ContinuousMap.add_apply,hc σ τ,hd σ τ,map_add]
    abel
  neg_mem' := by
    intro c hc σ τ
    simp only [ContinuousMap.neg_apply,hc σ τ,map_neg,neg_add]

/-- Principal continuous cocycles; the point producing the coboundary is
an algebraic point, not an arbitrary cochain. -/
def coboundaries : AddSubgroup (cocycles W K) where
  carrier := {c | ∃ P : GeometricPoints W K,∀ σ,c.val σ=action W K σ P-P}
  zero_mem' := by refine ⟨0,?_⟩; intro σ; simp
  add_mem' := by
    rintro c d ⟨P,hP⟩ ⟨Q,hQ⟩
    refine ⟨P+Q,?_⟩
    intro σ
    change c.val σ+d.val σ=action W K σ (P+Q)-(P+Q)
    rw [hP,hQ,map_add]
    abel
  neg_mem' := by
    rintro c ⟨P,hP⟩
    refine ⟨-P,?_⟩
    intro σ
    change -c.val σ=action W K σ (-P)-(-P)
    rw [hP,map_neg]
    abel

/-- Every principal coboundary is continuous, because every
algebraic point has an open Galois stabilizer. -/
def principalCocycle (P : GeometricPoints W K) : cocycles W K :=
  ⟨⟨fun σ=>action W K σ P-P,by
      change Continuous (fun σ : GaloisGroup K=>σ • P-P)
      fun_prop⟩,by
    intro σ τ
    change action W K (σ*τ) P-P=
      (action W K σ P-P)+action W K σ (action W K τ P-P)
    rw [action_mul,map_sub]
    abel⟩

theorem principalCocycle_mem (P : GeometricPoints W K) :
    principalCocycle W K P∈coboundaries W K := ⟨P,fun _=>rfl⟩

/-- Continuous H1(Gal(Kbar/K),E(Kbar)). -/
abbrev H1 := cocycles W K ⧸ coboundaries W K

def cohomologyClass : cocycles W K →+ H1 W K := QuotientAddGroup.mk' (coboundaries W K)

@[simp] theorem cohomologyClass_eq_zero (c : cocycles W K) :
    cohomologyClass W K c=0 ↔ ∃ P : GeometricPoints W K,
      ∀ σ,c.val σ=action W K σ P-P := QuotientAddGroup.eq_zero_iff c

end
end Common.Elliptic.TateShafarevich
