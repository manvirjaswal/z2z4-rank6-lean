module

public import Mathlib.RingTheory.LaurentSeries
public import Mathlib.FieldTheory.RatFunc.Basic
public import Mathlib.Algebra.Algebra.Rat

@[expose] public section

/-!
# Normalized rational Laurent places

The exact identity t=c+T fixes a rational parameter and its uniformizer.
This structure records only a field embedding and that identity.
-/
namespace Z2Z4Rank6
universe u
noncomputable section

structure RigidRationalPlace (K : Type u) [Field K] [Algebra ℚ K]
    [Algebra (RatFunc ℚ) K] where
  parameter : ℚ
  embedding : K→ₐ[ℚ]LaurentSeries ℚ
  rigid : embedding (algebraMap (RatFunc ℚ) K RatFunc.X)=
    algebraMap (PowerSeries ℚ) (LaurentSeries ℚ) (PowerSeries.C parameter+PowerSeries.X)

namespace RigidRationalPlace
variable {K : Type u} [Field K] [Algebra ℚ K] [Algebra (RatFunc ℚ) K]

theorem parameter_eq_of_embedding_eq (v w : RigidRationalPlace K)
    (h : v.embedding=w.embedding) : v.parameter=w.parameter := by
  have he : algebraMap (PowerSeries ℚ) (LaurentSeries ℚ)
      (PowerSeries.C v.parameter+PowerSeries.X)=
      algebraMap (PowerSeries ℚ) (LaurentSeries ℚ) (PowerSeries.C w.parameter+PowerSeries.X) :=
    v.rigid.symm.trans ((congrArg
      (fun f : K→ₐ[ℚ]LaurentSeries ℚ => f (algebraMap (RatFunc ℚ) K RatFunc.X)) h).trans w.rigid)
  have hp := (IsFractionRing.injective (PowerSeries ℚ) (LaurentSeries ℚ)) he
  simpa only [map_add,PowerSeries.constantCoeff_C,PowerSeries.constantCoeff_X,add_zero]
    using congrArg (PowerSeries.constantCoeff : PowerSeries ℚ→+*ℚ) hp

theorem embedding_injective : Function.Injective (embedding (K:=K)) := by
  intro v w h
  have hp := parameter_eq_of_embedding_eq v w h
  cases v
  cases w
  dsimp only at h hp
  cases h
  cases hp
  rfl

end RigidRationalPlace
end
end Z2Z4Rank6
