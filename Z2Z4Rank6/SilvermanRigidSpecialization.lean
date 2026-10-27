import Z2Z4Rank6.CanonicalLaurentSpecialization
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Algebraic.Defs

/-!
# Silverman's specialization theorem in normalized rational-place form

Source: J. H. Silverman, The Arithmetic of Elliptic Curves, 2nd ed., GTM 106 (2009),
Appendix C §20, pp. 456–457, Theorem 20.3; original specialization theorem:
J. reine angew. Math. 342 (1983), 197–211, DOI 10.1515/crll.1983.342.197.
The book states the cofinite injectivity of the specialization map
for nonconstant elliptic curves over number-field curve function fields.

This is its reformulation for unramified rational places, not a numbered statement in the source.
The function-field/smooth-projective-model correspondence
is Stacks Project, Theorem 53.2.6 and Lemma 53.2.8, tag 0BXX. Rational DVR places
are points of that proper model by the proper valuative criterion. Completion
with the specified rational coefficient field and uniformizer is described
by Stacks, Lemma 10.160.10, tag 0323. The exact identity m=c+T fixes that
uniformizer and prevents duplicate reparametrizations. The integral model
is likewise uniquely determined by its embedded coefficients.

The canonical specialization function is field base change followed
by explicit reduction of every point. Nonintegral affine coordinates
reduce to infinity.
-/
namespace Z2Z4Rank6

universe u
noncomputable section
open scoped Classical
open CanonicalLaurentSpecialization

/-- Normalized rational Laurent place with a good integral model.
The displayed equation fixes the local parameter, rather than allowing
arbitrary power-series reparametrizations of one place. -/
structure RigidGoodPlace (K : Type u) [Field K] [Algebra ℚ K]
    [Algebra (RatFunc ℚ) K] (W : WeierstrassCurve K) where
  parameter : ℚ
  embedding : K →ₐ[ℚ] LaurentSeries ℚ
  rigid : embedding (algebraMap (RatFunc ℚ) K RatFunc.X)=
    algebraMap (PowerSeries ℚ) (LaurentSeries ℚ)
      (PowerSeries.C parameter+PowerSeries.X)
  model : WeierstrassCurve (PowerSeries ℚ)
  model_eq : laurentCurve model=W.map embedding.toRingHom
  good : (constantCurve model).IsElliptic

namespace RigidGoodPlace
variable {K : Type u} [Field K] [Algebra ℚ K] [Algebra (RatFunc ℚ) K]
    {W : WeierstrassCurve K}

/-- Equal embeddings have equal parameters because the parameter's image
has constant coefficient equal to that rational number. -/
theorem parameter_eq_of_embedding_eq (v w : RigidGoodPlace K W)
    (h : v.embedding=w.embedding) : v.parameter=w.parameter := by
  have he : algebraMap (PowerSeries ℚ) (LaurentSeries ℚ)
      (PowerSeries.C v.parameter+PowerSeries.X)=
      algebraMap (PowerSeries ℚ) (LaurentSeries ℚ)
        (PowerSeries.C w.parameter+PowerSeries.X) :=
    v.rigid.symm.trans ((congrArg
      (fun f : K →ₐ[ℚ] LaurentSeries ℚ => f (algebraMap (RatFunc ℚ) K RatFunc.X)) h).trans w.rigid)
  have hp := (IsFractionRing.injective (PowerSeries ℚ) (LaurentSeries ℚ)) he
  simpa only [map_add,PowerSeries.constantCoeff_C,PowerSeries.constantCoeff_X,add_zero]
    using congrArg (PowerSeries.constantCoeff : PowerSeries ℚ →+* ℚ) hp

/-- The integral model is determined by its embedded coefficients. -/
theorem model_eq_of_embedding_eq (v w : RigidGoodPlace K W)
    (h : v.embedding=w.embedding) : v.model=w.model := by
  apply WeierstrassCurve.map_injective
    (IsFractionRing.injective (PowerSeries ℚ) (LaurentSeries ℚ))
  change laurentCurve v.model=laurentCurve w.model
  rw [v.model_eq,w.model_eq,h]

/-- No duplicate place is introduced by recording its integral model and
parameter. All remaining structure fields are propositions. -/
theorem embedding_injective : Function.Injective (embedding (K:=K) (W:=W)) := by
  intro v w h
  have hp := parameter_eq_of_embedding_eq v w h
  have hm := model_eq_of_embedding_eq v w h
  cases v
  cases w
  dsimp only at h hp hm
  cases h
  cases hp
  cases hm
  rfl

/-- Transport of points between equal equations. -/
def transport {F : Type*} [Field F] {V V' : WeierstrassCurve F}
    (h : V=V') : V.toAffine.Point → V'.toAffine.Point := by
  subst V'
  exact id

@[simp] theorem transport_zero {F : Type*} [Field F] {V V' : WeierstrassCurve F}
    (h : V=V') : transport h 0=0 := by
  subst V'
  rfl

variable [DecidableEq K]

/-- The canonical specialization is a fully defined function on every
point, including points whose affine coordinates are nonintegral. -/
def canonicalSpecialize (v : RigidGoodPlace K W) (P : W.toAffine.Point) :
    (constantCurve v.model).toAffine.Point := by
  letI := v.good
  exact reduce v.model (transport v.model_eq.symm
    (fieldPointMap v.embedding.toRingHom W P))

@[simp] theorem canonicalSpecialize_zero (v : RigidGoodPlace K W) :
    canonicalSpecialize v 0=0 := by
  simp only [canonicalSpecialize,map_zero,transport_zero,reduce_zero]

/-- The entire underlying function of the additive specialization map is
fixed. Agreement is not restricted to integral affine coordinates. -/
def HasInjectiveCanonicalSpecialization (v : RigidGoodPlace K W) : Prop :=
  ∃ σ : W.toAffine.Point →+ (constantCurve v.model).toAffine.Point,
    Function.Injective σ ∧ ∀ P,σ P=canonicalSpecialize v P

/-- Exceptional normalized places for this elliptic curve. -/
def badPlaces (W : WeierstrassCurve K) : Set (RigidGoodPlace K W) :=
  {v | ¬HasInjectiveCanonicalSpecialization v}

/-- An injective additive specialization agreeing everywhere makes the
already-defined canonical function injective. -/
theorem canonicalSpecialize_injective (v : RigidGoodPlace K W)
    (h : HasInjectiveCanonicalSpecialization v) : Function.Injective (canonicalSpecialize v) := by
  obtain ⟨σ,hσ,heq⟩ := h
  intro P Q hPQ
  apply hσ
  rw [heq P,heq Q]
  exact hPQ

theorem specialization_of_not_mem_badPlaces (v : RigidGoodPlace K W)
    (h : v∉badPlaces W) : HasInjectiveCanonicalSpecialization v := by
  change ¬¬HasInjectiveCanonicalSpecialization v at h
  exact not_not.mp h

end RigidGoodPlace

/-- For every finite extension of the rational function
field, an elliptic curve with transcendental j has an injective additive
specialization, with its fully fixed canonical underlying function, except
at finitely many good normalized rational Laurent places. This is the
generic rational-place consequence of Silverman's published theorem. -/
def SilvermanRigidSpecializationTheorem : Prop :=
  ∀ (K : Type u) [Field K] [Algebra ℚ K] [Algebra (RatFunc ℚ) K]
    [IsScalarTower ℚ (RatFunc ℚ) K] [FiniteDimensional (RatFunc ℚ) K] [DecidableEq K]
    (W : WeierstrassCurve K) (hW : W.IsElliptic),
    letI := hW
    Transcendental ℚ W.j → (RigidGoodPlace.badPlaces W).Finite

/-- Apply the published theorem to the finite set of bad
places. -/
theorem finite_bad_rigid_places (hS : SilvermanRigidSpecializationTheorem.{u})
    {K : Type u} [Field K] [Algebra ℚ K] [Algebra (RatFunc ℚ) K]
    [IsScalarTower ℚ (RatFunc ℚ) K] [FiniteDimensional (RatFunc ℚ) K] [DecidableEq K]
    (W : WeierstrassCurve K) (hW : W.IsElliptic)
    (hj : letI := hW; Transcendental ℚ W.j) :
    (RigidGoodPlace.badPlaces W).Finite := hS K W hW hj

end
end Z2Z4Rank6
