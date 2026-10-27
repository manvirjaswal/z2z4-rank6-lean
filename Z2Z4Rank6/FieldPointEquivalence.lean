import Z2Z4Rank6.PointMap
import Z2Z4Rank6.PointScaling

/-! A field isomorphism induces an additive equivalence of the
Mathlib nonsingular Weierstrass point groups, with coefficient transport. -/
namespace Z2Z4Rank6.FieldPointEquivalence
noncomputable section
open Common.WeierstrassCoordinates
variable {F L : Type*} [Field F] [Field L] [DecidableEq F] [DecidableEq L]

omit [DecidableEq F] [DecidableEq L] in
theorem map_back (e : F≃+*L) (W : WeierstrassCurve F) :
    (W.map e.toRingHom).map e.symm.toRingHom=W := by
  ext <;> exact e.symm_apply_apply _

def equiv (e : F≃+*L) (W : WeierstrassCurve F) :
    W.toAffine.Point ≃+ (W.map e.toRingHom).toAffine.Point where
  toFun := fieldPointMap e.toRingHom W
  invFun P := PointScaling.pointCongr (map_back e W)
    (fieldPointMap e.symm.toRingHom (W.map e.toRingHom) P)
  left_inv P := by
    apply encode_injective
    rw [PointScaling.encode_pointCongr,encode_fieldPointMap,encode_fieldPointMap]
    cases P with
    | zero => rfl
    | some x y h =>
      change some (e.symm (e x),e.symm (e y))=some (x,y)
      rw [e.symm_apply_apply,e.symm_apply_apply]
  right_inv P := by
    apply encode_injective
    rw [encode_fieldPointMap,PointScaling.encode_pointCongr,encode_fieldPointMap]
    cases P with
    | zero => rfl
    | some x y h =>
      change some (e (e.symm x),e (e.symm y))=some (x,y)
      rw [e.apply_symm_apply,e.apply_symm_apply]
  map_add' := (fieldPointMap e.toRingHom W).map_add

theorem coordinates (e : F≃+*L) (W : WeierstrassCurve F) (P : W.toAffine.Point) :
    encode (equiv e W P)=(encode P).map (fun xy=>(e xy.1,e xy.2)) :=
  encode_fieldPointMap _ _ _

end
end Z2Z4Rank6.FieldPointEquivalence
