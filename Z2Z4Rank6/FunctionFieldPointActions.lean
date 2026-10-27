import Z2Z4Rank6.FunctionFieldAutomorphisms

/-!
# Sign actions on the generic elliptic point group

The commuting additive involutions used in Remark 4.3 of Manvir Jaswal,
DOI 10.5281/zenodo.23437117, are induced by the constructed
field automorphisms. Their action on the curve coefficients is proved.
-/

namespace Z2Z4Rank6.FunctionField

noncomputable section

set_option maxHeartbeats 1000000

open Common.WeierstrassCoordinates

abbrev PointGroup := (X m).toAffine.Point

private def pointCurveCongr {F : Type*} [Field F] [DecidableEq F]
    {W W' : WeierstrassCurve F} (h : W = W') :
    W.toAffine.Point ≃+ W'.toAffine.Point := by
  subst W'
  exact AddEquiv.refl _

private theorem encode_pointCurveCongr {F : Type*} [Field F] [DecidableEq F]
    {W W' : WeierstrassCurve F} (h : W = W') (P : W.toAffine.Point) :
    encode (pointCurveCongr h P) = encode P := by
  subst W'
  rfl

private theorem map_curve_eq (f : K →+* K) (hm : f m=m) : (X m).map f = X m := by
  ext <;> simp [X, E, a, b, map_ofNat, hm]

/-- A field endomorphism fixing m acts on the point group of X. -/
def pointEndOf (f : K →+* K) (hm : f m=m) : PointGroup →+ PointGroup :=
  (pointCurveCongr (map_curve_eq f hm)).toAddMonoidHom.comp (fieldPointMap f (X m))

/-- The induced point map acts on both coordinates by the field map. -/
theorem encode_pointEndOf (f : K →+* K) (hm : f m=m) (P : PointGroup) :
    encode (pointEndOf f hm P) = (encode P).map (fun xy => (f xy.1,f xy.2)) := by
  change encode (pointCurveCongr (map_curve_eq f hm) (fieldPointMap f (X m) P)) = _
  rw [encode_pointCurveCongr, encode_fieldPointMap]

private theorem pointEndOf_involutive (f : K →+* K) (hm : f m=m)
    (hf : ∀ x : K, f (f x)=x) (P : PointGroup) :
    pointEndOf f hm (pointEndOf f hm P)=P := by
  apply encode_injective (X m)
  rw [encode_pointEndOf, encode_pointEndOf]
  cases P with
  | zero => rfl
  | some x y h =>
    change some (f (f x),f (f y)) = some (x,y)
    rw [hf, hf]

private theorem sigmaU_ring_m : sigmaU.toRingHom m = m := sigmaU_m
private theorem sigmaV_ring_m : sigmaV.toRingHom m = m := sigmaV_m
private theorem sigmaU_ring_involutive (x : K) :
    sigmaU.toRingHom (sigmaU.toRingHom x)=x := sigmaU_involutive x
private theorem sigmaV_ring_involutive (x : K) :
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

/-- The four printed character labels, in the order P1,...,P6. A true entry
means the corresponding involution acts by negation. -/
def pointCharacter : Fin 6 → Bool × Bool :=
  ![(false,false),(false,false),(false,false),(false,true),(true,false),(true,true)]

/-- The six abscissa formulas commute with every field embedding. -/
theorem map_sixX_field {F L : Type*} [Field F] [Field L]
    (f : F →+* L) (t : F) (j : Fin 6) : f (sixX t j)=sixX (f t) j := by
  fin_cases j <;> simp [sixX, p1x, p2x, p3x, p4x, p5x, p6x,
    t4x, t5x, t6x, q1, q2, q12, map_ofNat]

/-- The six ordinate formulas commute with every field embedding. -/
theorem map_sixY_field {F L : Type*} [Field F] [Field L]
    (f : F →+* L) (t r s : F) (j : Fin 6) :
    f (sixY t r s j)=sixY (f t) (f r) (f s) j := by
  fin_cases j <;> simp [sixY, p1y, p2y, p3y, p4y, p5y, p6y,
    t4y, t5y, t6y, twistN, q1, q2, q12, map_ofNat]

private theorem sixY_flipU (j : Fin 6) : sixY m (-u) v j =
    if (pointCharacter j).1 then -sixY m u v j else sixY m u v j := by
  fin_cases j <;> simp [pointCharacter, sixY, p4y, p5y, p6y, div_neg, neg_div]

private theorem sixY_flipV (j : Fin 6) : sixY m u (-v) j =
    if (pointCharacter j).2 then -sixY m u v j else sixY m u v j := by
  fin_cases j <;> simp [pointCharacter, sixY, p4y, p5y, p6y, div_neg, neg_div]

private theorem sigmaU_ring_apply (x : K) : sigmaU.toRingHom x = sigmaU x := rfl
private theorem sigmaV_ring_apply (x : K) : sigmaV.toRingHom x = sigmaV x := rfl

private theorem sigmaU_sixX (j : Fin 6) : sigmaU (sixX m j)=sixX m j := by
  simpa only [sigmaU_ring_apply, sigmaU_m] using map_sixX_field sigmaU.toRingHom m j

private theorem sigmaV_sixX (j : Fin 6) : sigmaV (sixX m j)=sixX m j := by
  simpa only [sigmaV_ring_apply, sigmaV_m] using map_sixX_field sigmaV.toRingHom m j

private theorem sigmaU_sixY (j : Fin 6) : sigmaU (sixY m u v j) =
    if (pointCharacter j).1 then -sixY m u v j else sixY m u v j := by
  have h : sigmaU (sixY m u v j)=sixY m (-u) v j := by
    simpa only [sigmaU_ring_apply, sigmaU_m, sigmaU_u, sigmaU_v] using
      map_sixY_field sigmaU.toRingHom m u v j
  exact h.trans (sixY_flipU j)

private theorem sigmaV_sixY (j : Fin 6) : sigmaV (sixY m u v j) =
    if (pointCharacter j).2 then -sixY m u v j else sixY m u v j := by
  have h : sigmaV (sixY m u v j)=sixY m u (-v) j := by
    simpa only [sigmaV_ring_apply, sigmaV_m, sigmaV_u, sigmaV_v] using
      map_sixY_field sigmaV.toRingHom m u v j
  exact h.trans (sixY_flipV j)

private theorem encode_points (j : Fin 6) :
    encode (points j)=some (sixX m j,sixY m u v j) := rfl

private theorem encode_neg_point (P : PointGroup) :
    encode (-P)=(encode P).map (fun xy => (xy.1,-xy.2)) := by
  cases P with
  | zero => rfl
  | some x y h =>
    change some (x,(X m).toAffine.negY x y)=some (x,-y)
    simp [WeierstrassCurve.Affine.negY, X, E]

/-- u-sign change fixes P1,P2,P3,P4 and negates P5,P6, exactly as
printed in Remark 4.3. This is an equality in the elliptic point group. -/
theorem pointSigmaU_points (j : Fin 6) :
    pointSigmaU (points j)=if (pointCharacter j).1 then -points j else points j := by
  apply encode_injective (X m)
  rw [encode_pointSigmaU, encode_points]
  change some (sigmaU (sixX m j),sigmaU (sixY m u v j)) = _
  rw [sigmaU_sixX, sigmaU_sixY]
  split_ifs
  · rw [encode_neg_point, encode_points]
    rfl
  · rw [encode_points]

/-- v-sign change fixes P1,P2,P3,P5 and negates P4,P6, exactly as
printed in Remark 4.3. This is an equality in the elliptic point group. -/
theorem pointSigmaV_points (j : Fin 6) :
    pointSigmaV (points j)=if (pointCharacter j).2 then -points j else points j := by
  apply encode_injective (X m)
  rw [encode_pointSigmaV, encode_points]
  change some (sigmaV (sixX m j),sigmaV (sixY m u v j)) = _
  rw [sigmaV_sixX, sigmaV_sixY]
  split_ifs
  · rw [encode_neg_point, encode_points]
    rfl
  · rw [encode_points]

end
end Z2Z4Rank6.FunctionField
