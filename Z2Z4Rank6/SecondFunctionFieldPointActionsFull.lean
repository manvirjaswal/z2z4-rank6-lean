module

public import Z2Z4Rank6.SecondFunctionFieldPointActions
public import Z2Z4Rank6.SecondFunctionFieldAutomorphismsFull

@[expose] public section

/-! The third sign action, completing the eight characters of
the printed degree-eight function-field extension. -/

namespace Z2Z4Rank6.SecondFunctionField
noncomputable section
open SecondFamily Common.WeierstrassCoordinates
set_option maxHeartbeats 1000000

theorem sigma1_ring_W : sigma1.toRingHom W=W := sigma1_W

def pointSigma1 : PointGroup ≃+ PointGroup where
  toFun := pointEndOf sigma1.toRingHom sigma1_ring_W
  invFun := pointEndOf sigma1.toRingHom sigma1_ring_W
  left_inv P := by
    apply encode_injective (F W)
    rw [encode_pointEndOf,encode_pointEndOf]
    cases P with
    | zero => rfl
    | some x y h =>
      change some (sigma1 (sigma1 x),sigma1 (sigma1 y))=some (x,y)
      rw [sigma1_involutive,sigma1_involutive]
  right_inv P := by
    apply encode_injective (F W)
    rw [encode_pointEndOf,encode_pointEndOf]
    cases P with
    | zero => rfl
    | some x y h =>
      change some (sigma1 (sigma1 x),sigma1 (sigma1 y))=some (x,y)
      rw [sigma1_involutive,sigma1_involutive]
  map_add' := (pointEndOf sigma1.toRingHom sigma1_ring_W).map_add

theorem encode_pointSigma1 (P : PointGroup) :
    encode (pointSigma1 P)=(encode P).map (fun xy=>(sigma1 xy.1,sigma1 xy.2)) :=
  encode_pointEndOf sigma1.toRingHom sigma1_ring_W P

theorem pointSigma1_involutive (P : PointGroup) : pointSigma1 (pointSigma1 P)=P := by
  apply encode_injective (F W)
  rw [encode_pointSigma1,encode_pointSigma1]
  cases P with
  | zero => rfl
  | some x y h =>
    change some (sigma1 (sigma1 x),sigma1 (sigma1 y))=some (x,y)
    rw [sigma1_involutive,sigma1_involutive]

theorem pointSigma1_pointSigma2_commute (P : PointGroup) :
    pointSigma1 (pointSigma2 P)=pointSigma2 (pointSigma1 P) := by
  apply encode_injective (F W)
  rw [encode_pointSigma1,encode_pointSigma2,encode_pointSigma2,encode_pointSigma1]
  cases P with
  | zero => rfl
  | some x y h =>
    change some (sigma1 (sigma2 x),sigma1 (sigma2 y))=some (sigma2 (sigma1 x),sigma2 (sigma1 y))
    rw [sigma1_sigma2_commute,sigma1_sigma2_commute]

theorem pointSigma1_pointSigma3_commute (P : PointGroup) :
    pointSigma1 (pointSigma3 P)=pointSigma3 (pointSigma1 P) := by
  apply encode_injective (F W)
  rw [encode_pointSigma1,encode_pointSigma3,encode_pointSigma3,encode_pointSigma1]
  cases P with
  | zero => rfl
  | some x y h =>
    change some (sigma1 (sigma3 x),sigma1 (sigma3 y))=some (sigma3 (sigma1 x),sigma3 (sigma1 y))
    rw [sigma1_sigma3_commute,sigma1_sigma3_commute]

def firstPointSign : Fin 6 → Bool := ![false,false,false,true,true,false]
def fullPointCharacter (j : Fin 6) : Bool × Bool × Bool := (firstPointSign j,pointCharacter j)

private theorem sigma1_sixX (j : Fin 6) :
    sigma1 (genericBasePoint.sixX j)=genericBasePoint.sixX j := by
  fin_cases j <;>
    simp [G2Point.sixX,G2Point.untwistedX2,G2Point.untwistedX3,
      G2Point.untwistedX4,G2Point.untwistedX5,G2Point.untwistedX6,
      genericBasePoint,x1,x2,x3,x4,x5,x6,mu,lambda,beta,gamma,qA,qB,qH,sigma,iotaScale,map_ofNat]

private theorem sigma1_sixY (j : Fin 6) :
    sigma1 (genericBasePoint.sixY j)=
      if firstPointSign j then -genericBasePoint.sixY j else genericBasePoint.sixY j := by
  fin_cases j <;>
    simp [G2Point.sixY,G2Point.untwistedY2,G2Point.untwistedY3,
      G2Point.untwistedY4,G2Point.untwistedY5,G2Point.untwistedY6,
      genericBasePoint,firstPointSign,y1,y2,y3,y4,y5,y6,f2,f6,
      lambda,beta,gamma,qA,qB,qH,sigma,iotaScale,map_ofNat,div_neg]

private theorem encode_neg_point (P : PointGroup) :
    encode (-P)=(encode P).map (fun xy=>(xy.1,-xy.2)) := by
  cases P with
  | zero => rfl
  | some x y h =>
    change some (x,(F W).toAffine.negY x y)=some (x,-y)
    simp [WeierstrassCurve.Affine.negY,F,twistedF]

theorem pointSigma1_points (j : Fin 6) :
    pointSigma1 (points j)=if firstPointSign j then -points j else points j := by
  apply encode_injective (F W)
  rw [encode_pointSigma1,encode_points]
  change some (sigma1 (genericBasePoint.sixX j),sigma1 (genericBasePoint.sixY j))=_
  rw [sigma1_sixX,sigma1_sixY]
  split_ifs
  · rw [encode_neg_point,encode_points]
    rfl
  · rw [encode_points]

end
end Z2Z4Rank6.SecondFunctionField
