module

public import Z2Z4Rank6.ThirdTwistFieldGalois

@[expose] public section

/-!
# Sign actions on the generic elliptic point group

The commuting additive involutions used in Remark 4.3 of Manvir Jaswal,
DOI 10.5281/zenodo.23437117, are induced by the constructed
field automorphisms. Their action on the curve coefficients is proved.
-/

namespace Z2Z4Rank6.ThirdTwistField

noncomputable section

set_option maxHeartbeats 1000000

open Common.WeierstrassCoordinates

abbrev PointGroup := (X m).toAffine.Point

def pointCurveCongr {F : Type*} [Field F] [DecidableEq F]
    {W W' : WeierstrassCurve F} (h : W = W') :
    W.toAffine.Point ≃+ W'.toAffine.Point := by
  subst W'
  exact AddEquiv.refl _

private theorem encode_pointCurveCongr {F : Type*} [Field F] [DecidableEq F]
    {W W' : WeierstrassCurve F} (h : W = W') (P : W.toAffine.Point) :
    encode (pointCurveCongr h P) = encode P := by
  subst W'
  rfl

theorem map_curve_eq (f : K →+* K) (hm : f m=m) : (X m).map f = X m := by
  ext <;> simp [X, E, a, b, map_ofNat, hm]

/-- A field endomorphism fixing m acts on the point group of X. -/
def pointEndOf (f : K →+* K) (hm : f m=m) : PointGroup →+ PointGroup :=
  (pointCurveCongr (map_curve_eq f hm)).toAddMonoidHom.comp (fieldPointMap f (X m))

/-- The induced point map acts on both coordinates by the field map. -/
theorem encode_pointEndOf (f : K →+* K) (hm : f m=m) (P : PointGroup) :
    encode (pointEndOf f hm P) = (encode P).map (fun xy => (f xy.1,f xy.2)) := by
  change encode (pointCurveCongr (map_curve_eq f hm) (fieldPointMap f (X m) P)) = _
  rw [encode_pointCurveCongr, encode_fieldPointMap]

theorem pointEndOf_involutive (f : K →+* K) (hm : f m=m)
    (hf : ∀ x : K, f (f x)=x) (P : PointGroup) :
    pointEndOf f hm (pointEndOf f hm P)=P := by
  apply encode_injective (X m)
  rw [encode_pointEndOf, encode_pointEndOf]
  cases P with
  | zero => rfl
  | some x y h =>
    change some (f (f x),f (f y)) = some (x,y)
    rw [hf, hf]

theorem sigmaU_ring_m : sigmaU.toRingHom m = m := sigmaU_m
theorem sigmaV_ring_m : sigmaV.toRingHom m = m := sigmaV_m
theorem sigmaU_ring_involutive (x : K) :
    sigmaU.toRingHom (sigmaU.toRingHom x)=x := sigmaU_involutive x
theorem sigmaV_ring_involutive (x : K) :
    sigmaV.toRingHom (sigmaV.toRingHom x)=x := sigmaV_involutive x

/-- The additive automorphism induced by u↦-u, v↦v. -/
def pointSigmaU : PointGroup ≃+ PointGroup where
  toFun := pointEndOf sigmaU.toRingHom sigmaU_ring_m
  invFun := pointEndOf sigmaU.toRingHom sigmaU_ring_m
  left_inv := pointEndOf_involutive sigmaU.toRingHom sigmaU_ring_m sigmaU_ring_involutive
  right_inv := pointEndOf_involutive sigmaU.toRingHom sigmaU_ring_m sigmaU_ring_involutive
  map_add' := (pointEndOf sigmaU.toRingHom sigmaU_ring_m).map_add

/-- The additive automorphism induced by u↦u, v↦-v. -/
def pointSigmaV : PointGroup ≃+ PointGroup where
  toFun := pointEndOf sigmaV.toRingHom sigmaV_ring_m
  invFun := pointEndOf sigmaV.toRingHom sigmaV_ring_m
  left_inv := pointEndOf_involutive sigmaV.toRingHom sigmaV_ring_m sigmaV_ring_involutive
  right_inv := pointEndOf_involutive sigmaV.toRingHom sigmaV_ring_m sigmaV_ring_involutive
  map_add' := (pointEndOf sigmaV.toRingHom sigmaV_ring_m).map_add

/-- The first point-group action is an involution. -/
theorem pointSigmaU_involutive (P : PointGroup) : pointSigmaU (pointSigmaU P)=P :=
  pointEndOf_involutive sigmaU.toRingHom sigmaU_ring_m sigmaU_ring_involutive P

/-- The second point-group action is an involution. -/
theorem pointSigmaV_involutive (P : PointGroup) : pointSigmaV (pointSigmaV P)=P :=
  pointEndOf_involutive sigmaV.toRingHom sigmaV_ring_m sigmaV_ring_involutive P

/-- The two point-group actions commute. -/
theorem pointSigmaU_pointSigmaV_commute (P : PointGroup) :
    pointSigmaU (pointSigmaV P)=pointSigmaV (pointSigmaU P) := by
  apply encode_injective (X m)
  change encode (pointEndOf sigmaU.toRingHom sigmaU_ring_m
      (pointEndOf sigmaV.toRingHom sigmaV_ring_m P)) =
    encode (pointEndOf sigmaV.toRingHom sigmaV_ring_m
      (pointEndOf sigmaU.toRingHom sigmaU_ring_m P))
  rw [encode_pointEndOf, encode_pointEndOf, encode_pointEndOf, encode_pointEndOf]
  cases P with
  | zero => rfl
  | some x y h =>
    change some (sigmaU (sigmaV x),sigmaU (sigmaV y)) =
      some (sigmaV (sigmaU x),sigmaV (sigmaU y))
    rw [sigmaU_sigmaV_commute, sigmaU_sigmaV_commute]

/-- Encoded coordinates of the first point-group involution. -/
theorem encode_pointSigmaU (P : PointGroup) :
    encode (pointSigmaU P) = (encode P).map (fun xy => (sigmaU xy.1,sigmaU xy.2)) :=
  encode_pointEndOf sigmaU.toRingHom sigmaU_ring_m P

/-- Encoded coordinates of the second point-group involution. -/
theorem encode_pointSigmaV (P : PointGroup) :
    encode (pointSigmaV P) = (encode P).map (fun xy => (sigmaV xy.1,sigmaV xy.2)) :=
  encode_pointEndOf sigmaV.toRingHom sigmaV_ring_m P

theorem sigmaW_ring_m : sigmaW.toRingHom m=m := sigmaW_m
theorem sigmaW_ring_involutive (x : K) : sigmaW.toRingHom (sigmaW.toRingHom x)=x := sigmaW_involutive x
/-- The additive automorphism induced by u↦-u, v↦v. -/
def pointSigmaW : PointGroup ≃+ PointGroup where
  toFun := pointEndOf sigmaW.toRingHom sigmaW_ring_m
  invFun := pointEndOf sigmaW.toRingHom sigmaW_ring_m
  left_inv := pointEndOf_involutive sigmaW.toRingHom sigmaW_ring_m sigmaW_ring_involutive
  right_inv := pointEndOf_involutive sigmaW.toRingHom sigmaW_ring_m sigmaW_ring_involutive
  map_add' := (pointEndOf sigmaW.toRingHom sigmaW_ring_m).map_add


theorem pointSigmaW_involutive (P : PointGroup) : pointSigmaW (pointSigmaW P)=P :=
  pointEndOf_involutive sigmaW.toRingHom sigmaW_ring_m sigmaW_ring_involutive P

theorem encode_pointSigmaW (P : PointGroup) :
    encode (pointSigmaW P)=(encode P).map (fun xy=>(sigmaW xy.1,sigmaW xy.2)) :=
  encode_pointEndOf sigmaW.toRingHom sigmaW_ring_m P

theorem pointSigmaU_pointSigmaW_commute (P : PointGroup) :
    pointSigmaU (pointSigmaW P)=pointSigmaW (pointSigmaU P) := by
  apply encode_injective (X m)
  rw [encode_pointSigmaU,encode_pointSigmaW,encode_pointSigmaW,encode_pointSigmaU]
  cases P with
  | zero => rfl
  | some x y h =>
    change some (sigmaU (sigmaW x),sigmaU (sigmaW y))=some (sigmaW (sigmaU x),sigmaW (sigmaU y))
    rw [sigmaU_sigmaW_commute,sigmaU_sigmaW_commute]

theorem pointSigmaV_pointSigmaW_commute (P : PointGroup) :
    pointSigmaV (pointSigmaW P)=pointSigmaW (pointSigmaV P) := by
  apply encode_injective (X m)
  rw [encode_pointSigmaV,encode_pointSigmaW,encode_pointSigmaW,encode_pointSigmaV]
  cases P with
  | zero => rfl
  | some x y h =>
    change some (sigmaV (sigmaW x),sigmaV (sigmaW y))=some (sigmaW (sigmaV x),sigmaW (sigmaV y))
    rw [sigmaV_sigmaW_commute,sigmaV_sigmaW_commute]

end
end Z2Z4Rank6.ThirdTwistField
