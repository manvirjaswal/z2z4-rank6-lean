import Z2Z4Rank6.GFunctionFieldLocal
import Z2Z4Rank6.GQuarticGeometry
import Z2Z4Rank6.FunctionFieldPointPlace

/-!
# Rigid Laurent places at all rational points of G

The printed quartic has no zero ordinate over Q. Hensel lifting at every
rational point therefore constructs a normalized embedding of Q(G)
into Q((T)). The constant coordinates recover the rational point.
Source: Jaswal, the specialization argument following Proposition 7.2.
-/
namespace Z2Z4Rank6.GFunctionFieldPointPlace
noncomputable section
open GFunctionField

abbrev PS := PowerSeries ℚ
abbrev LS := LaurentSeries ℚ

theorem eta_ne_zero (c : GQuarticPoint) : c.eta≠0 := by
  have hi : 99*c.eta^2=(99*c.m^2-4999)^2+71069600 := by
    rw [c.equation]
    dsimp [gQuartic]
    ring
  intro hz
  rw [hz] at hi
  nlinarith [sq_nonneg (99*c.m^2-4999)]

def mSeries (c : GQuarticPoint) : PS := UnivariateLocal.mSeries c.m

@[simp] theorem mSeries_constant (c : GQuarticPoint) :
    PowerSeries.constantCoeff (mSeries c)=c.m := UnivariateLocal.mSeries_constant c.m

private theorem eta_constant (c : GQuarticPoint) :
    c.eta^2=PowerSeries.constantCoeff (h (mSeries c)) := by
  rw [GFunctionFieldLocal.map_h,mSeries_constant]
  simpa only [gQuartic,h] using c.equation

def etaSeries (c : GQuarticPoint) : PS := Classical.choose
  (FunctionFieldLocal.exists_square_root_with_constant (h (mSeries c)) c.eta
    (eta_constant c) (eta_ne_zero c))

theorem etaSeries_spec (c : GQuarticPoint) :
    (etaSeries c)^2=h (mSeries c) ∧ PowerSeries.constantCoeff (etaSeries c)=c.eta :=
  Classical.choose_spec (FunctionFieldLocal.exists_square_root_with_constant
    (h (mSeries c)) c.eta (eta_constant c) (eta_ne_zero c))

abbrev baseEmbedding (c : GQuarticPoint) : Base →+* LS := UnivariateLocal.baseEmbedding c.m

private theorem local_eta_relation (c : GQuarticPoint) :
    (algebraMap PS LS (etaSeries c))^2=baseEmbedding c d := by
  rw [←map_pow,(etaSeries_spec c).1,GFunctionFieldLocal.map_h]
  simp only [d,GFunctionFieldLocal.map_h,baseEmbedding,
    UnivariateLocal.baseEmbedding_X,mSeries]

def embedding (c : GQuarticPoint) : K →+* LS :=
  FunctionFieldLocal.quadraticLift (baseEmbedding c) d
    (algebraMap PS LS (etaSeries c)) (local_eta_relation c)

@[simp] theorem embedding_base (c : GQuarticPoint) (r : Base) :
    embedding c (algebraMap Base K r)=baseEmbedding c r := by simp [embedding]

@[simp] theorem embedding_m (c : GQuarticPoint) :
    embedding c m=algebraMap PS LS (mSeries c) := by simp [m,baseEmbedding,mSeries]

@[simp] theorem embedding_eta (c : GQuarticPoint) :
    embedding c eta=algebraMap PS LS (etaSeries c) := by simp [eta,embedding]

def embeddingAlgHom (c : GQuarticPoint) : K →ₐ[ℚ] LS where
  toRingHom := embedding c
  commutes' q := RingHom.map_rat_algebraMap (embedding c) q

theorem embeddingAlgHom_parameter (c : GQuarticPoint) :
    embeddingAlgHom c (algebraMap (RatFunc ℚ) K RatFunc.X)=
      algebraMap PS LS (PowerSeries.C c.m+PowerSeries.X) := by
  change embedding c m=algebraMap PS LS (mSeries c)
  exact embedding_m c

theorem embedding_injective_on_points : Function.Injective embedding := by
  intro c e he
  have hm := congrArg (fun f : K →+* LS=>f m) he
  have hz := congrArg (fun f : K →+* LS=>f eta) he
  rw [embedding_m,embedding_m] at hm
  rw [embedding_eta,embedding_eta] at hz
  have hm' := congrArg PowerSeries.constantCoeff ((IsFractionRing.injective PS LS) hm)
  have hz' := congrArg PowerSeries.constantCoeff ((IsFractionRing.injective PS LS) hz)
  apply GQuarticPoint.ext
  · simpa only [mSeries_constant] using hm'
  · simpa only [(etaSeries_spec c).2,(etaSeries_spec e).2] using hz'

theorem embeddingAlgHom_injective_on_points : Function.Injective embeddingAlgHom := by
  intro c e he
  apply embedding_injective_on_points
  exact congrArg AlgHom.toRingHom he

def seriesCurve (c : GQuarticPoint) : WeierstrassCurve PS := X (mSeries c)

theorem seriesCurve_constant (c : GQuarticPoint) :
    (seriesCurve c).map PowerSeries.constantCoeff=X c.m := by
  rw [seriesCurve,FunctionFieldLocal.map_family,mSeries_constant]

theorem seriesCurve_laurent (c : GQuarticPoint) :
    (seriesCurve c).map (algebraMap PS LS)=(X m).map (embedding c) := by
  rw [seriesCurve,FunctionFieldLocal.map_family,FunctionFieldLocal.map_family,embedding_m]

theorem constantFiber_elliptic (c : GQuarticPoint) (hc : GoodCurve (X c.m)) :
    ((seriesCurve c).map PowerSeries.constantCoeff).IsElliptic := by
  rw [seriesCurve_constant]
  exact hc

theorem finite_m_fiber (r : ℚ) : {c : GQuarticPoint | c.m=r}.Finite := by
  classical
  by_cases hn : ({c : GQuarticPoint | c.m=r} : Set GQuarticPoint).Nonempty
  · obtain ⟨c,hc⟩ := hn
    let e : GQuarticPoint := ⟨c.m,-c.eta,by simpa only [neg_sq] using c.equation⟩
    apply ((Set.finite_singleton e).insert c).subset
    intro z hz
    have hm : z.m=c.m := hz.trans hc.symm
    have he : z.eta^2=c.eta^2 := by rw [z.equation,c.equation,hm]
    have hf : (z.eta-c.eta)*(z.eta+c.eta)=0 := by nlinarith
    rcases mul_eq_zero.mp hf with hf | hf
    · exact Or.inl (GQuarticPoint.ext hm (by linarith))
    · exact Or.inr (GQuarticPoint.ext hm (by dsimp [e]; linarith))
  · rw [Set.not_nonempty_iff_eq_empty.mp hn]
    exact Set.finite_empty

end
end Z2Z4Rank6.GFunctionFieldPointPlace
