module

public import Z2Z4Rank6.FunctionFieldLocal
public import Z2Z4Rank6.FunctionFieldCoordinates
public import Z2Z4Rank6.UnivariateLocal
public import Z2Z4Rank6.SingularFibers
public import Mathlib.Algebra.Algebra.Rat

@[expose] public section

/-!
# Rigid Laurent places at all rational points of C

For c=(m₀,u₀,v₀), substitute m=m₀+T and lift the two square roots
with constants u₀,v₀. This constructs a Q-algebra embedding of the
function field Q(C) into Q((T)).
The three constant coordinates recover c, so different C-points give
different rigid embeddings. The integral model has good reduction outside
the sixteen singular points of Theorem 1.2(c), Jaswal,
DOI 10.5281/zenodo.23437117.
-/

namespace Z2Z4Rank6.FunctionFieldPointPlace

noncomputable section

abbrev PS := PowerSeries ℚ
abbrev LS := LaurentSeries ℚ

def mSeries (c : CPoint) : PS := UnivariateLocal.mSeries c.m

@[simp] theorem mSeries_constant (c : CPoint) : PowerSeries.constantCoeff (mSeries c)=c.m :=
  UnivariateLocal.mSeries_constant c.m

def uSeries (c : CPoint) : PS := Classical.choose
  (FunctionFieldLocal.exists_square_root_with_constant (q1 ((mSeries c)^2)) c.u
    (by simpa [q1,map_ofNat] using c.u_sq) c.u_ne_zero)

def vSeries (c : CPoint) : PS := Classical.choose
  (FunctionFieldLocal.exists_square_root_with_constant (q2 ((mSeries c)^2)) c.v
    (by simpa [q2,map_ofNat] using c.v_sq) c.v_ne_zero)

theorem uSeries_spec (c : CPoint) :
    (uSeries c)^2=q1 ((mSeries c)^2) ∧ PowerSeries.constantCoeff (uSeries c)=c.u :=
  Classical.choose_spec (FunctionFieldLocal.exists_square_root_with_constant
    (q1 ((mSeries c)^2)) c.u (by simpa [q1,map_ofNat] using c.u_sq) c.u_ne_zero)

theorem vSeries_spec (c : CPoint) :
    (vSeries c)^2=q2 ((mSeries c)^2) ∧ PowerSeries.constantCoeff (vSeries c)=c.v :=
  Classical.choose_spec (FunctionFieldLocal.exists_square_root_with_constant
    (q2 ((mSeries c)^2)) c.v (by simpa [q2,map_ofNat] using c.v_sq) c.v_ne_zero)

@[simp] theorem uSeries_constant (c : CPoint) : PowerSeries.constantCoeff (uSeries c)=c.u :=
  (uSeries_spec c).2

@[simp] theorem vSeries_constant (c : CPoint) : PowerSeries.constantCoeff (vSeries c)=c.v :=
  (vSeries_spec c).2

abbrev baseEmbedding (c : CPoint) : FunctionField.Base →+* LS :=
  UnivariateLocal.baseEmbedding c.m

theorem local_u_relation (c : CPoint) :
    (algebraMap PS LS (uSeries c))^2=baseEmbedding c FunctionField.d1 := by
  rw [←map_pow,(uSeries_spec c).1]
  simp [baseEmbedding,FunctionField.d1,q1,mSeries,map_ofNat]

def firstEmbedding (c : CPoint) : FunctionField.First →+* LS :=
  FunctionFieldLocal.quadraticLift (baseEmbedding c) FunctionField.d1
    (algebraMap PS LS (uSeries c)) (local_u_relation c)

theorem local_v_relation (c : CPoint) :
    (algebraMap PS LS (vSeries c))^2=firstEmbedding c FunctionField.d2First := by
  rw [←map_pow,(vSeries_spec c).1]
  simp [firstEmbedding,FunctionField.d2First,FunctionField.d2,q2,mSeries,map_ofNat]

/-- The field embedding at the rational C-point c. -/
def embedding (c : CPoint) : FunctionField.K →+* LS :=
  FunctionFieldLocal.quadraticLift (firstEmbedding c) FunctionField.d2First
    (algebraMap PS LS (vSeries c)) (local_v_relation c)

theorem embedding_injective (c : CPoint) : Function.Injective (embedding c) :=
  (embedding c).injective

@[simp] theorem embedding_base (c : CPoint) (r : FunctionField.Base) :
    embedding c (algebraMap FunctionField.Base FunctionField.K r)=baseEmbedding c r := by
  rw [IsScalarTower.algebraMap_apply FunctionField.Base FunctionField.First FunctionField.K]
  simp [embedding,firstEmbedding]

@[simp] theorem embedding_m (c : CPoint) :
    embedding c FunctionField.m=algebraMap PS LS (mSeries c) := by
  simp [FunctionField.m,mSeries]

@[simp] theorem embedding_u (c : CPoint) :
    embedding c FunctionField.u=algebraMap PS LS (uSeries c) := by
  simp [FunctionField.u,embedding,firstEmbedding]

@[simp] theorem embedding_v (c : CPoint) :
    embedding c FunctionField.v=algebraMap PS LS (vSeries c) := by
  simp [FunctionField.v,embedding]

/-- The same constructed embedding as a Q-algebra homomorphism. -/
def embeddingAlgHom (c : CPoint) : FunctionField.K →ₐ[ℚ] LS where
  toRingHom := embedding c
  commutes' q := RingHom.map_rat_algebraMap (embedding c) q

@[simp] theorem embeddingAlgHom_apply (c : CPoint) (x : FunctionField.K) :
    embeddingAlgHom c x=embedding c x := rfl

/-- The exact shift fixes the uniformizer, excluding arbitrary formal
reparametrizations from the family of places. -/
theorem embeddingAlgHom_parameter (c : CPoint) :
    embeddingAlgHom c (algebraMap (RatFunc ℚ) FunctionField.K RatFunc.X)=
      algebraMap PS LS (PowerSeries.C c.m+PowerSeries.X) := by
  change embedding c FunctionField.m=algebraMap PS LS (mSeries c)
  exact embedding_m c

theorem embedding_uniformizer (c : CPoint) :
    embedding c (FunctionField.m-algebraMap ℚ FunctionField.K c.m)=
      algebraMap PS LS PowerSeries.X := by
  rw [map_sub,embedding_m,RingHom.map_rat_algebraMap]
  change algebraMap PS LS (mSeries c)-algebraMap PS LS (PowerSeries.C c.m)=_
  rw [←map_sub]
  congr 1
  dsimp [mSeries,UnivariateLocal.mSeries]
  ring

/-- All three constant coordinates are recovered from the embedding's
images of m,u,v, which are integral power series. -/
theorem embedding_injective_on_points : Function.Injective embedding := by
  intro c d h
  have hm := congrArg (fun f : FunctionField.K →+* LS => f FunctionField.m) h
  have hu := congrArg (fun f : FunctionField.K →+* LS => f FunctionField.u) h
  have hv := congrArg (fun f : FunctionField.K →+* LS => f FunctionField.v) h
  rw [embedding_m,embedding_m] at hm
  rw [embedding_u,embedding_u] at hu
  rw [embedding_v,embedding_v] at hv
  have hm' := congrArg PowerSeries.constantCoeff ((IsFractionRing.injective PS LS) hm)
  have hu' := congrArg PowerSeries.constantCoeff ((IsFractionRing.injective PS LS) hu)
  have hv' := congrArg PowerSeries.constantCoeff ((IsFractionRing.injective PS LS) hv)
  apply CPoint.ext
  · simpa using hm'
  · simpa using hu'
  · simpa using hv'

theorem embeddingAlgHom_injective_on_points : Function.Injective embeddingAlgHom := by
  intro c d h
  apply embedding_injective_on_points
  exact congrArg AlgHom.toRingHom h

/-- The integral polynomial family in the rigid formal chart. -/
def seriesCurve (c : CPoint) : WeierstrassCurve PS := X (mSeries c)

theorem seriesCurve_constant (c : CPoint) :
    (seriesCurve c).map PowerSeries.constantCoeff=X c.m := by
  rw [seriesCurve,FunctionFieldLocal.map_family,mSeries_constant]

theorem seriesCurve_laurent (c : CPoint) :
    (seriesCurve c).map (algebraMap PS LS)=(X FunctionField.m).map (embedding c) := by
  rw [seriesCurve,FunctionFieldLocal.map_family,FunctionFieldLocal.map_family,embedding_m]

theorem constantFiber_elliptic (c : CPoint) (hc : c∉exceptionalPoints) :
    ((seriesCurve c).map PowerSeries.constantCoeff).IsElliptic := by
  rw [seriesCurve_constant]
  exact (X_good_iff_not_exceptional c).mpr hc

/-- The discriminant is a unit in Q[[T]]. -/
theorem seriesCurve_elliptic (c : CPoint) (hc : c∉exceptionalPoints) :
    (seriesCurve c).IsElliptic := by
  constructor
  rw [PowerSeries.isUnit_iff_constantCoeff,←WeierstrassCurve.map_Δ,seriesCurve_constant]
  exact ((X_good_iff_not_exceptional c).mpr hc).isUnit

instance laurentFiber_elliptic (c : CPoint) :
    ((seriesCurve c).map (algebraMap PS LS)).IsElliptic := by
  rw [seriesCurve_laurent]
  infer_instance

/-- Distinct points give distinct embedding/model pairs. -/
theorem place_model_injective :
    Function.Injective (fun c : CPoint => (embeddingAlgHom c,seriesCurve c)) := by
  intro c d h
  exact embeddingAlgHom_injective_on_points (congrArg Prod.fst h)

end
end Z2Z4Rank6.FunctionFieldPointPlace
