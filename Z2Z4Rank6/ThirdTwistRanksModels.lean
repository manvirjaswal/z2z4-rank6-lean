module

public import Z2Z4Rank6.ThirdTwistFieldDecomposition
public import Z2Z4Rank6.ThirdTwistSpecialization
public import Z2Z4Rank6.RankSixAssembly

@[expose] public section

/-! Exact model identities for the eight twist factors of the third-twist
field, and their eight-term point-group rank identity. -/
namespace Z2Z4Rank6.ThirdTwistField
noncomputable section
open scoped TensorProduct
open TwistCharacters
set_option maxHeartbeats 400000

instance genericFiberElliptic : (X m).IsElliptic := by
  have h : ((X FunctionField.m).map (algebraMap FunctionField.K K)).IsElliptic := inferInstance
  have he : (X FunctionField.m).map (algebraMap FunctionField.K K)=X m := by
    ext <;> simp [X,E,a,b,m,map_ofNat]
  rwa [he] at h

/-- The four printed q3-twists are ordered q3,q3*q1,q3*q2,q3*q12. -/
def thirdIndex (χ : Bool × Bool) : Fin 4 :=
  if χ.1 then (if χ.2 then 3 else 1) else (if χ.2 then 2 else 0)

theorem twistCurve_last_false (χ : Bool × Bool) :
    twistCurve (χ.1,χ.2,false)=FunctionField.TwistCharacters.twistCurve χ := by
  rcases χ with ⟨a,b⟩
  simp only [twistCurve,twistD,Bool.false_eq_true,ite_false,mul_one]
  rfl

theorem thirdTwistPolynomial_image (χ : Bool × Bool) :
    GusicTadic.polyToRF (ThirdTwist.twistPolynomial (thirdIndex χ))=
      twistD (χ.1,χ.2,true) := by
  rcases χ with ⟨a,b⟩
  cases a <;> cases b <;>
    simp [thirdIndex,ThirdTwist.twistPolynomial,ThirdTwist.q3Poly,ThirdTwist.q3,
      GusicTadic.q1Poly,GusicTadic.q2Poly,GusicTadic.q12Poly,
      GusicTadic.polyToRF,twistD,FunctionField.TwistCharacters.twistD,
      FunctionField.d1,FunctionField.d2,d3,q1,q2,q12,map_ofNat] <;> ring

theorem twistCurve_last_true (χ : Bool × Bool) :
    twistCurve (χ.1,χ.2,true)=GusicTadic.genericModel
      (ThirdTwist.twistPolynomial (thirdIndex χ)) := by
  rw [ThirdTwist.generic_eq_pointScaling,thirdTwistPolynomial_image]
  ext <;> simp [twistCurve,A,B,PointScaling.curve,mul_assoc]

def splitLastEquiv {R : Type*} [CommSemiring R]
    (M : Bool × Bool × Bool → Type*)
    [∀χ,AddCommMonoid (M χ)] [∀χ,Module R (M χ)] :
    (∀χ,M χ) ≃ₗ[R]
      (∀χ : Bool×Bool,M (χ.1,χ.2,false)) × (∀χ : Bool×Bool,M (χ.1,χ.2,true)) where
  toFun f := (fun χ=>f (χ.1,χ.2,false),fun χ=>f (χ.1,χ.2,true))
  invFun p χ := match χ with
    | (a,b,false) => p.1 (a,b)
    | (a,b,true) => p.2 (a,b)
  left_inv f := by funext ⟨a,b,c⟩; cases c <;> rfl
  right_inv p := by rcases p with ⟨f,g⟩; rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def eightProductEquiv {R : Type*} [CommSemiring R]
    (M : Bool × Bool × Bool → Type*)
    [∀χ,AddCommMonoid (M χ)] [∀χ,Module R (M χ)] :=
  (splitLastEquiv (R:=R) M).trans
    ((RankSixAssembly.fourProductEquiv (R:=R) (fun χ=>M (χ.1,χ.2,false))).prodCongr
      (RankSixAssembly.fourProductEquiv (R:=R) (fun χ=>M (χ.1,χ.2,true))))

theorem rank_eight_twists : Module.rank ℤ PointGroup =
    (Module.rank ℤ (twistPoints (false,false,false))+
      Module.rank ℤ (twistPoints (true,false,false))+
      Module.rank ℤ (twistPoints (false,true,false))+
      Module.rank ℤ (twistPoints (true,true,false)))+
    (Module.rank ℤ (twistPoints (false,false,true))+
      Module.rank ℤ (twistPoints (true,false,true))+
      Module.rank ℤ (twistPoints (false,true,true))+
      Module.rank ℤ (twistPoints (true,true,true))) := by
  rw [group_rank_eq_rationalized_rank PointGroup]
  have e := fullTwistDecomposition.trans
    (eightProductEquiv (R:=ℚ) (fun χ=>ℚ ⊗[ℤ] twistPoints χ))
  rw [e.rank_eq]
  simp only [rank_prod',←group_rank_eq_rationalized_rank]
  ac_rfl

end
end Z2Z4Rank6.ThirdTwistField
