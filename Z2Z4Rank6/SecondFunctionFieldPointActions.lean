import Z2Z4Rank6.SecondFunctionFieldAutomorphisms
import Z2Z4Rank6.PointScaling

/-! Additive sign actions on the six printed second-family sections. -/
namespace Z2Z4Rank6.SecondFunctionField
noncomputable section
open Common.WeierstrassCoordinates SecondFamily
set_option maxHeartbeats 1000000

abbrev PointGroup := (SecondFamily.F W).toAffine.Point

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

private theorem map_curve_eq (f : K →+* K) (hW : f W=W) : (SecondFamily.F W).map f = SecondFamily.F W := by
  ext <;> simp [SecondFamily.F, SecondFamily.twistedF, SecondFamily.U, SecondFamily.V,
    SecondFamily.lambda, map_ofNat, hW]

/-- A field endomorphism fixing W acts on the point group of F. -/
def pointEndOf (f : K →+* K) (hW : f W=W) : PointGroup →+ PointGroup :=
  (pointCurveCongr (map_curve_eq f hW)).toAddMonoidHom.comp (fieldPointMap f (SecondFamily.F W))

/-- The induced point map acts on both coordinates by the field map. -/
theorem encode_pointEndOf (f : K →+* K) (hW : f W=W) (P : PointGroup) :
    encode (pointEndOf f hW P) = (encode P).map (fun xy => (f xy.1,f xy.2)) := by
  change encode (pointCurveCongr (map_curve_eq f hW) (fieldPointMap f (SecondFamily.F W) P)) = _
  rw [encode_pointCurveCongr, encode_fieldPointMap]

private theorem pointEndOf_involutive (f : K →+* K) (hW : f W=W)
    (hf : ∀ x : K, f (f x)=x) (P : PointGroup) :
    pointEndOf f hW (pointEndOf f hW P)=P := by
  apply encode_injective (SecondFamily.F W)
  rw [encode_pointEndOf, encode_pointEndOf]
  cases P with
  | zero => rfl
  | some x y h =>
    change some (f (f x),f (f y)) = some (x,y)
    rw [hf, hf]

private theorem sigma2_ring_W : sigma2.toRingHom W = W := sigma2_W
private theorem sigma3_ring_W : sigma3.toRingHom W = W := sigma3_W
private theorem sigma2_ring_involutive (x : K) :
    sigma2.toRingHom (sigma2.toRingHom x)=x := sigma2_involutive x
private theorem sigma3_ring_involutive (x : K) :
    sigma3.toRingHom (sigma3.toRingHom x)=x := sigma3_involutive x

/-- The additive automorphism induced by s₂↦-s₂, s₃↦s₃. -/
def pointSigma2 : PointGroup ≃+ PointGroup where
  toFun := pointEndOf sigma2.toRingHom sigma2_ring_W
  invFun := pointEndOf sigma2.toRingHom sigma2_ring_W
  left_inv := pointEndOf_involutive sigma2.toRingHom sigma2_ring_W sigma2_ring_involutive
  right_inv := pointEndOf_involutive sigma2.toRingHom sigma2_ring_W sigma2_ring_involutive
  map_add' := (pointEndOf sigma2.toRingHom sigma2_ring_W).map_add

/-- The additive automorphism induced by s₂↦s₂, s₃↦-s₃. -/
def pointSigma3 : PointGroup ≃+ PointGroup where
  toFun := pointEndOf sigma3.toRingHom sigma3_ring_W
  invFun := pointEndOf sigma3.toRingHom sigma3_ring_W
  left_inv := pointEndOf_involutive sigma3.toRingHom sigma3_ring_W sigma3_ring_involutive
  right_inv := pointEndOf_involutive sigma3.toRingHom sigma3_ring_W sigma3_ring_involutive
  map_add' := (pointEndOf sigma3.toRingHom sigma3_ring_W).map_add

/-- The first point-group action is an involution. -/
theorem pointSigma2_involutive (P : PointGroup) : pointSigma2 (pointSigma2 P)=P :=
  pointEndOf_involutive sigma2.toRingHom sigma2_ring_W sigma2_ring_involutive P

/-- The second point-group action is an involution. -/
theorem pointSigma3_involutive (P : PointGroup) : pointSigma3 (pointSigma3 P)=P :=
  pointEndOf_involutive sigma3.toRingHom sigma3_ring_W sigma3_ring_involutive P

/-- The two point-group actions commute. -/
theorem pointSigma2_pointSigma3_commute (P : PointGroup) :
    pointSigma2 (pointSigma3 P)=pointSigma3 (pointSigma2 P) := by
  apply encode_injective (SecondFamily.F W)
  change encode (pointEndOf sigma2.toRingHom sigma2_ring_W
      (pointEndOf sigma3.toRingHom sigma3_ring_W P)) =
    encode (pointEndOf sigma3.toRingHom sigma3_ring_W
      (pointEndOf sigma2.toRingHom sigma2_ring_W P))
  rw [encode_pointEndOf, encode_pointEndOf, encode_pointEndOf, encode_pointEndOf]
  cases P with
  | zero => rfl
  | some x y h =>
    change some (sigma2 (sigma3 x),sigma2 (sigma3 y)) =
      some (sigma3 (sigma2 x),sigma3 (sigma2 y))
    rw [sigma2_sigma3_commute, sigma2_sigma3_commute]

/-- Encoded coordinates of the first point-group involution. -/
theorem encode_pointSigma2 (P : PointGroup) :
    encode (pointSigma2 P) = (encode P).map (fun xy => (sigma2 xy.1,sigma2 xy.2)) :=
  encode_pointEndOf sigma2.toRingHom sigma2_ring_W P

/-- Encoded coordinates of the second point-group involution. -/
theorem encode_pointSigma3 (P : PointGroup) :
    encode (pointSigma3 P) = (encode P).map (fun xy => (sigma3 xy.1,sigma3 xy.2)) :=
  encode_pointEndOf sigma3.toRingHom sigma3_ring_W P

/-- True means negation for the s₂ and s₃ signs respectively. -/
def pointCharacter : Fin 6 → Bool × Bool :=
  ![(false,false),(true,false),(true,false),(false,true),(false,true),(true,true)]

theorem encode_points (j : Fin 6) :
    encode (points j)=some (genericBasePoint.sixX j,genericBasePoint.sixY j) := by
  let : (F genericBasePoint.W).IsElliptic := genericFiberElliptic
  exact genericBasePoint.encode_sixPoints W_ne_zero qA_W_ne_zero qB_W_ne_zero j

private theorem encode_neg_point (P : PointGroup) :
    encode (-P)=(encode P).map (fun xy=>(xy.1,-xy.2)) := by
  cases P with
  | zero => rfl
  | some x y h =>
    change some (x,(F W).toAffine.negY x y)=some (x,-y)
    simp [WeierstrassCurve.Affine.negY,F,twistedF]

private theorem sigma2_sixX (j : Fin 6) :
    sigma2 (genericBasePoint.sixX j)=genericBasePoint.sixX j := by
  fin_cases j <;>
    simp [G2Point.sixX,G2Point.untwistedX2,G2Point.untwistedX3,
      G2Point.untwistedX4,G2Point.untwistedX5,G2Point.untwistedX6,
      genericBasePoint,x1,x2,x3,x4,x5,x6,mu,lambda,beta,gamma,qA,qB,qH,sigma,iotaScale,map_ofNat,-sigma3_apply]

private theorem sigma3_sixX (j : Fin 6) :
    sigma3 (genericBasePoint.sixX j)=genericBasePoint.sixX j := by
  fin_cases j <;>
    simp [G2Point.sixX,G2Point.untwistedX2,G2Point.untwistedX3,
      G2Point.untwistedX4,G2Point.untwistedX5,G2Point.untwistedX6,
      genericBasePoint,x1,x2,x3,x4,x5,x6,mu,lambda,beta,gamma,qA,qB,qH,sigma,iotaScale,map_ofNat,-sigma3_apply]

private theorem sigma2_sixY (j : Fin 6) :
    sigma2 (genericBasePoint.sixY j)=
      if (pointCharacter j).1 then -genericBasePoint.sixY j else genericBasePoint.sixY j := by
  fin_cases j <;>
    simp [G2Point.sixY,G2Point.untwistedY2,G2Point.untwistedY3,
      G2Point.untwistedY4,G2Point.untwistedY5,G2Point.untwistedY6,
      genericBasePoint,pointCharacter,y1,y2,y3,y4,y5,y6,f2,f6,
      lambda,beta,gamma,qA,qB,qH,sigma,iotaScale,map_ofNat,div_neg,-sigma3_apply]
  all_goals simp only [neg_div,mul_neg,div_neg]

private theorem sigma3_sixY (j : Fin 6) :
    sigma3 (genericBasePoint.sixY j)=
      if (pointCharacter j).2 then -genericBasePoint.sixY j else genericBasePoint.sixY j := by
  fin_cases j <;>
    simp [G2Point.sixY,G2Point.untwistedY2,G2Point.untwistedY3,
      G2Point.untwistedY4,G2Point.untwistedY5,G2Point.untwistedY6,
      genericBasePoint,pointCharacter,y1,y2,y3,y4,y5,y6,f2,f6,
      lambda,beta,gamma,qA,qB,qH,sigma,iotaScale,map_ofNat,div_neg,-sigma3_apply]
  all_goals simp only [neg_div,mul_neg,div_neg]

theorem pointSigma2_points (j : Fin 6) :
    pointSigma2 (points j)=if (pointCharacter j).1 then -points j else points j := by
  apply encode_injective (F W)
  rw [encode_pointSigma2,encode_points]
  change some (sigma2 (genericBasePoint.sixX j),sigma2 (genericBasePoint.sixY j))=_
  rw [sigma2_sixX,sigma2_sixY]
  split_ifs
  · rw [encode_neg_point,encode_points]
    rfl
  · rw [encode_points]

theorem pointSigma3_points (j : Fin 6) :
    pointSigma3 (points j)=if (pointCharacter j).2 then -points j else points j := by
  apply encode_injective (F W)
  rw [encode_pointSigma3,encode_points]
  change some (sigma3 (genericBasePoint.sixX j),sigma3 (genericBasePoint.sixY j))=_
  rw [sigma3_sixX,sigma3_sixY]
  split_ifs
  · rw [encode_neg_point,encode_points]
    rfl
  · rw [encode_points]

end
end Z2Z4Rank6.SecondFunctionField
