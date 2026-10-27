import Common.Elliptic.TateShafarevichTransport
import Z2Z4Rank6.PointScaling
import Z2Z4Rank6.Basic

/-!
# Rational coordinate scaling preserves Sha[2]

The point isomorphisms use the formulas (x,y)↦(u²x,u³y) over
every characteristic-zero field. Their naturality is proved on
coordinates, so the resulting continuous-cohomology and local-restriction
isomorphisms do not depend on an abstract rational point-group equivalence.
-/
namespace Common.Elliptic.TateShafarevich.NaturalPointEquiv
noncomputable section
open WeierstrassCurve Z2Z4Rank6 Common.WeierstrassCoordinates
open scoped Classical

private theorem baseCurve_eq (A B : ℚ) (K : Type) [Field K] [CharZero K] :
    (PointScaling.curve A B).baseChange K=PointScaling.curve (A : K) (B : K) :=
  PointScaling.map_curve (algebraMap ℚ K) A B

private theorem scaledBaseCurve_eq (A B u : ℚ) (K : Type) [Field K] [CharZero K] :
    PointScaling.curve ((u : K)^2*(A : K)) ((u : K)^4*(B : K))=
      (PointScaling.curve (u^2*A) (u^4*B)).baseChange K := by
  rw [baseCurve_eq]
  simp only [Rat.cast_mul,Rat.cast_pow]

def scalingOnField (A B u : ℚ) (hu : u≠0) (K : Type) [Field K] [CharZero K] :
    ((PointScaling.curve A B).baseChange K).toAffine.Point≃+
      ((PointScaling.curve (u^2*A) (u^4*B)).baseChange K).toAffine.Point :=
  (PointScaling.pointCongr (baseCurve_eq A B K)).trans
    ((PointScaling.scaleEquiv (A : K) (B : K) (u : K) (by exact_mod_cast hu)).trans
      (PointScaling.pointCongr (scaledBaseCurve_eq A B u K)))

theorem encode_scalingOnField (A B u : ℚ) (hu : u≠0)
    (K : Type) [Field K] [CharZero K]
    (P : ((PointScaling.curve A B).baseChange K).toAffine.Point) :
    encode (scalingOnField A B u hu K P)=
      (encode P).map (fun xy=>((u : K)^2*xy.1,(u : K)^3*xy.2)) := by
  change encode (PointScaling.pointCongr (scaledBaseCurve_eq A B u K)
    (PointScaling.scaleEquiv (A : K) (B : K) (u : K) _
      (PointScaling.pointCongr (baseCurve_eq A B K) P)))=_
  rw [PointScaling.encode_pointCongr,PointScaling.encode_scaleEquiv,
    PointScaling.encode_pointCongr]

theorem encode_pointMap {W : WeierstrassCurve ℚ} {K L : Type}
    [Field K] [CharZero K] [Field L] [CharZero L] (f : K→ₐ[ℚ]L)
    (P : (W.baseChange K).toAffine.Point) :
    encode (Affine.Point.map (W' := W.toAffine) f P)=
      (encode P).map (fun xy=>(f xy.1,f xy.2)) := by cases P <;> rfl

/-- The rational scaling, natural over all coefficient fields. -/
def scaling (A B u : ℚ) (hu : u≠0) :
    NaturalPointEquiv (PointScaling.curve A B) (PointScaling.curve (u^2*A) (u^4*B)) where
  equiv K := scalingOnField A B u hu K
  natural := by
    intro K L _ _ _ _ f P
    apply encode_injective ((PointScaling.curve (u^2*A) (u^4*B)).baseChange L).toAffine
    rw [encode_scalingOnField,encode_pointMap,encode_pointMap,encode_scalingOnField,
      Option.map_map,Option.map_map]
    congr 1
    funext xy
    simp only [Function.comp_apply,map_mul,map_pow]
    simp only [map_ratCast]

/-- Scaling in the paper's split family, proved from the coordinate
formulas over every field. -/
def splitFamilyScaling (a b u : ℚ) (hu : u≠0) :
    NaturalPointEquiv (E a b) (E (u*a) (u*b)) :=
  (ofEq (show E a b=PointScaling.curve (a^2+b^2) (a^2*b^2) from rfl)).trans
    ((scaling (a^2+b^2) (a^2*b^2) u hu).trans (ofEq (by
      ext <;> simp only [PointScaling.curve,E] <;> ring)))

end
end Common.Elliptic.TateShafarevich.NaturalPointEquiv
