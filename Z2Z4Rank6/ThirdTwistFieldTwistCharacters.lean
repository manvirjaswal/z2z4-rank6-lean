import Z2Z4Rank6.ThirdTwistFieldPointActions
import Z2Z4Rank6.TwistCharacters
import Z2Z4Rank6.ThreeCharacterRationalization
import Z2Z4Rank6.FieldTwistEmbedding

/-! The eight quadratic-twist character groups over the third-twist field. -/
namespace Z2Z4Rank6.ThirdTwistField.TwistCharacters
noncomputable section
open Common.WeierstrassCoordinates
open scoped TensorProduct
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

abbrev baseEmbedding : Base →+* K := algebraMap Base K
def A : Base := (a RatFunc.X)^2+(b RatFunc.X)^2
def B : Base := (a RatFunc.X)^2*(b RatFunc.X)^2

theorem curve_image_eq : PointScaling.curve (baseEmbedding A) (baseEmbedding B)=X m := by
  ext <;> simp [A,B,PointScaling.curve,X,E,a,b,m_eq_base,map_ofNat]

/-- The q12 representative is normalized by 25, exactly as in the paper. -/
def twistD (χ : Bool × Bool × Bool) : Base :=
  FunctionField.TwistCharacters.twistD (χ.1,χ.2.1) * (if χ.2.2 then d3 else 1)

def twistRoot (χ : Bool × Bool × Bool) : K :=
  algebraMap FunctionField.K K (FunctionField.TwistCharacters.twistRoot (χ.1,χ.2.1)) *
    (if χ.2.2 then w else 1)

theorem w_sq_eq_d3 : w^2=baseEmbedding d3 := by
  rw [w_sq]
  simp [baseEmbedding,d3,m_eq_base,map_ofNat]

theorem twistRoot_sq (χ : Bool × Bool × Bool) :
    (twistRoot χ)^2=baseEmbedding (twistD χ) := by
  rw [twistRoot,mul_pow,←map_pow,FunctionField.TwistCharacters.twistRoot_sq,
    ←IsScalarTower.algebraMap_apply Base FunctionField.K K]
  rcases χ with ⟨a,b,c⟩
  cases c <;> simp [twistD,w_sq_eq_d3,baseEmbedding]

theorem twistRoot_ne_zero (χ : Bool × Bool × Bool) : twistRoot χ ≠ 0 := by
  apply mul_ne_zero
  · exact (map_ne_zero _).mpr (FunctionField.TwistCharacters.twistRoot_ne_zero _)
  · cases χ.2.2 <;> simp [w_ne_zero]

theorem twistD_ne_zero (χ : Bool × Bool × Bool) : twistD χ ≠ 0 := by
  intro hd
  have hs := twistRoot_sq χ
  rw [hd,map_zero] at hs
  exact twistRoot_ne_zero χ (sq_eq_zero_iff.mp hs)

theorem sigmaU_twistRoot (χ : Bool × Bool × Bool) :
    sigmaU (twistRoot χ)=if χ.1 then -twistRoot χ else twistRoot χ := by
  rw [twistRoot,map_mul,sigmaU_old,FunctionField.TwistCharacters.sigmaU_twistRoot]
  cases χ.1 <;> cases χ.2.2 <;> simp

theorem sigmaV_twistRoot (χ : Bool × Bool × Bool) :
    sigmaV (twistRoot χ)=if χ.2.1 then -twistRoot χ else twistRoot χ := by
  rw [twistRoot,map_mul,sigmaV_old,FunctionField.TwistCharacters.sigmaV_twistRoot]
  cases χ.2.1 <;> cases χ.2.2 <;> simp

theorem sigmaW_twistRoot (χ : Bool × Bool × Bool) :
    sigmaW (twistRoot χ)=if χ.2.2 then -twistRoot χ else twistRoot χ := by
  rw [twistRoot,map_mul,sigmaW_old]
  have hs : star w= -w := sigmaW_w
  cases χ.2.2 <;> simp [hs]

abbrev twistCurve (χ : Bool × Bool × Bool) : WeierstrassCurve Base :=
  PointScaling.curve (twistD χ*A) ((twistD χ)^2*B)

abbrev twistPoints (χ : Bool × Bool × Bool) := (twistCurve χ).toAffine.Point

theorem twistCurve_eq_long (χ : Bool × Bool × Bool) :
    twistCurve χ=PointScaling.curve (twistD χ*A) ((twistD χ)^2*B) := rfl

def embeddingData (χ : Bool × Bool × Bool) :
    FieldTwistEmbedding.Data baseEmbedding (twistD χ) (twistRoot χ) (twistCurve χ) (X m) :=
  FieldTwistEmbedding.data baseEmbedding A B (twistD χ) (twistRoot χ)
    (twistD_ne_zero χ) (twistRoot_sq χ) (twistCurve χ) (X m)
      (twistCurve_eq_long χ) curve_image_eq

abbrev embed (χ : Bool × Bool × Bool) : twistPoints χ →+ PointGroup :=
  (embeddingData χ).hom

theorem embed_injective (χ : Bool × Bool × Bool) : Function.Injective (embed χ) :=
  (embeddingData χ).injective

private theorem encode_neg_point (P : PointGroup) :
    encode (-P) = (encode P).map (fun xy => (xy.1,-xy.2)) := by
  cases P with
  | zero => rfl
  | some x y h =>
    rw [WeierstrassCurve.Affine.Point.neg_some]
    simp [encode,WeierstrassCurve.Affine.negY,X,E]

abbrev characterSubgroup (χ : Bool × Bool × Bool) : AddSubgroup PointGroup :=
  ThreeCharacterRationalization.characterGroup pointSigmaU.toAddMonoidHom
    pointSigmaV.toAddMonoidHom pointSigmaW.toAddMonoidHom χ

private theorem embed_sign (σ : K ≃ₐ[Base] K) (τ : PointGroup →+ PointGroup)
    (hτ : ∀ P, encode (τ P) = (encode P).map (fun xy => (σ xy.1,σ xy.2)))
    (χ : Bool × Bool × Bool) (ε : Bool)
    (hroot : σ (twistRoot χ) = if ε then -twistRoot χ else twistRoot χ)
    (P : twistPoints χ) :
    τ (embed χ P) = if ε then -(embed χ P) else embed χ P := by
  have hc := (embeddingData χ).coordinates P
  apply encode_injective (X m)
  rw [hτ,hc]
  cases ε
  · rw [ite_eq_right (by decide),hc]
    cases P <;> simp [encode,baseEmbedding,map_div₀,map_mul,σ.commutes,hroot]
  · rw [ite_eq_left (by decide),encode_neg_point,hc]
    cases P <;> simp [encode,baseEmbedding,map_div₀,map_mul,σ.commutes,hroot,mul_neg,div_neg]

theorem embed_mem_characterSubgroup (χ : Bool × Bool × Bool) (P : twistPoints χ) :
    embed χ P ∈ characterSubgroup χ := by
  refine ⟨?_,?_,?_⟩
  · exact embed_sign sigmaU pointSigmaU.toAddMonoidHom encode_pointSigmaU
      χ χ.1 (sigmaU_twistRoot χ) P
  · exact embed_sign sigmaV pointSigmaV.toAddMonoidHom encode_pointSigmaV
      χ χ.2.1 (sigmaV_twistRoot χ) P
  · exact embed_sign sigmaW pointSigmaW.toAddMonoidHom encode_pointSigmaW
      χ χ.2.2 (sigmaW_twistRoot χ) P

def characterEmbedding (χ : Bool × Bool × Bool) : twistPoints χ →+ characterSubgroup χ :=
  (embed χ).codRestrict _ (embed_mem_characterSubgroup χ)

theorem characterEmbedding_injective (χ : Bool × Bool × Bool) :
    Function.Injective (characterEmbedding χ) := by
  intro P Q h
  exact embed_injective χ (congrArg Subtype.val h)

private theorem point_sign_coordinates (σ : K ≃ₐ[Base] K) (τ : PointGroup →+ PointGroup)
    (hτ : ∀ P, encode (τ P) = (encode P).map (fun xy => (σ xy.1,σ xy.2)))
    (ε : Bool) (x y : K) (hN : (X m).toAffine.Nonsingular x y)
    (h : τ (.some x y hN) = if ε then -(.some x y hN) else .some x y hN) :
    σ x = x ∧ σ y = if ε then -y else y := by
  have he := congrArg encode h
  rw [hτ] at he
  cases ε
  · simpa only [Bool.false_eq_true,ite_false,encode,Option.map_some,
      Option.some.injEq,Prod.mk.injEq] using he
  · rw [ite_eq_left (by decide),encode_neg_point] at he
    simpa only [encode,Option.map_some,Option.some.injEq,Prod.mk.injEq,ite_true] using he

private theorem descend_nonsingular_general {F L : Type*} [Field F] [Field L]
    (f : F →+* L) (A B d : F) (r : L) (hr0 : r ≠ 0) (hr : r^2=f d)
    (x y : L) (hN : (PointScaling.curve (f A) (f B)).toAffine.Nonsingular x y)
    (x₀ y₀ : F) (hx : f x₀=f d*x) (hy : f y₀=f d*r*y) :
    (PointScaling.curve (d*A) (d^2*B)).toAffine.Nonsingular x₀ y₀ := by
  have hs := PointScaling.scale_nonsingular (f A) (f B) r hr0 x y hN
  have h3 : r^3=f d*r := by rw [←hr]; ring
  have h4 : r^4=(f d)^2 := by rw [←hr]; ring
  rw [h3,h4,hr] at hs
  apply ((PointScaling.curve (d*A) (d^2*B)).toAffine.map_nonsingular
    (f := f) f.injective x₀ y₀).mp
  change ((PointScaling.curve (d*A) (d^2*B)).map f).toAffine.Nonsingular (f x₀) (f y₀)
  rw [PointScaling.map_curve,map_mul,map_mul,map_pow,hx,hy]
  exact hs

private theorem descend_nonsingular (χ : Bool × Bool × Bool) (x y : K)
    (hN : (X m).toAffine.Nonsingular x y) (x₀ y₀ : Base)
    (hx : baseEmbedding x₀=baseEmbedding (twistD χ)*x)
    (hy : baseEmbedding y₀=baseEmbedding (twistD χ)*twistRoot χ*y) :
    (twistCurve χ).toAffine.Nonsingular x₀ y₀ := by
  rw [twistCurve_eq_long]
  apply descend_nonsingular_general baseEmbedding A B (twistD χ) (twistRoot χ)
    (twistRoot_ne_zero χ) (twistRoot_sq χ) x y _ x₀ y₀ hx hy
  rw [curve_image_eq]
  exact hN

theorem characterEmbedding_surjective (χ : Bool × Bool × Bool) :
    Function.Surjective (characterEmbedding χ) := by
  rintro ⟨P,hP⟩
  cases P with
  | zero =>
    refine ⟨0,?_⟩
    apply Subtype.ext
    exact (embed χ).map_zero
  | some x y hN =>
    have h1 := point_sign_coordinates sigmaU pointSigmaU.toAddMonoidHom
      encode_pointSigmaU χ.1 x y hN hP.1
    have h2 : sigmaV x=x ∧ sigmaV y=if χ.2.1 then -y else y :=
      point_sign_coordinates sigmaV pointSigmaV.toAddMonoidHom
        encode_pointSigmaV χ.2.1 x y hN hP.2.1
    have h3 : sigmaW x=x ∧ sigmaW y=if χ.2.2 then -y else y :=
      point_sign_coordinates sigmaW pointSigmaW.toAddMonoidHom
        encode_pointSigmaW χ.2.2 x y hN hP.2.2
    have h1x : sigmaU (baseEmbedding (twistD χ)*x)=baseEmbedding (twistD χ)*x := by
      rw [map_mul,sigmaU_base,h1.1]
    have h2x : sigmaV (baseEmbedding (twistD χ)*x)=baseEmbedding (twistD χ)*x := by
      rw [map_mul,sigmaV_base,h2.1]
    have h3x : sigmaW (baseEmbedding (twistD χ)*x)=baseEmbedding (twistD χ)*x := by
      rw [map_mul,sigmaW_base,h3.1]
    have h1y : sigmaU (baseEmbedding (twistD χ)*twistRoot χ*y)=
        baseEmbedding (twistD χ)*twistRoot χ*y := by
      rw [map_mul,map_mul,sigmaU_base,sigmaU_twistRoot,h1.2]
      cases χ.1 <;> simp
    have h2y : sigmaV (baseEmbedding (twistD χ)*twistRoot χ*y)=
        baseEmbedding (twistD χ)*twistRoot χ*y := by
      rw [map_mul,map_mul,sigmaV_base,sigmaV_twistRoot,h2.2]
      cases χ.2.1 <;> simp
    have h3y : sigmaW (baseEmbedding (twistD χ)*twistRoot χ*y)=
        baseEmbedding (twistD χ)*twistRoot χ*y := by
      rw [map_mul,map_mul,sigmaW_base,sigmaW_twistRoot,h3.2]
      cases χ.2.2 <;> simp
    obtain ⟨x₀,hx⟩ := (fixed_iff_in_base _).mp ⟨h1x,h2x,h3x⟩
    obtain ⟨y₀,hy⟩ := (fixed_iff_in_base _).mp ⟨h1y,h2y,h3y⟩
    refine ⟨.some x₀ y₀ (descend_nonsingular χ x y hN x₀ y₀ hx hy),?_⟩
    apply Subtype.ext
    apply encode_injective (X m)
    change encode (embed χ (.some x₀ y₀ _)) = _
    have he := (embeddingData χ).coordinates
      (.some x₀ y₀ (descend_nonsingular χ x y hN x₀ y₀ hx hy))
    rw [he]
    have hd : baseEmbedding (twistD χ) ≠ 0 :=
      (map_ne_zero baseEmbedding).mpr (twistD_ne_zero χ)
    simp only [encode,Option.map_some,hx,hy,Option.some.injEq,Prod.mk.injEq]
    constructor <;> field_simp [hd,twistRoot_ne_zero χ]

def characterEquiv (χ : Bool × Bool × Bool) : twistPoints χ ≃+ characterSubgroup χ :=
  AddEquiv.ofBijective (characterEmbedding χ)
    ⟨characterEmbedding_injective χ,characterEmbedding_surjective χ⟩

abbrev fullCharacterSpace (χ : Bool × Bool × Bool) :
    Submodule ℚ (ℚ ⊗[ℤ] PointGroup) :=
  ThreeCharacter.jointSpace (PointScaling.rationalizeHom pointSigmaU.toAddMonoidHom)
    (PointScaling.rationalizeHom pointSigmaV.toAddMonoidHom)
    (PointScaling.rationalizeHom pointSigmaW.toAddMonoidHom) χ

def rationalizedTwistCharacterEquiv (χ : Bool × Bool × Bool) :
    (ℚ ⊗[ℤ] twistPoints χ) ≃ₗ[ℚ] fullCharacterSpace χ :=
  (PointScaling.rationalizeEquiv (characterEquiv χ)).trans
    (ThreeCharacterRationalization.equivCharacterSpace pointSigmaU.toAddMonoidHom
      pointSigmaV.toAddMonoidHom pointSigmaW.toAddMonoidHom
      pointSigmaU_involutive pointSigmaV_involutive pointSigmaW_involutive
      pointSigmaU_pointSigmaV_commute pointSigmaU_pointSigmaW_commute
      pointSigmaV_pointSigmaW_commute χ)

end
end Z2Z4Rank6.ThirdTwistField.TwistCharacters
