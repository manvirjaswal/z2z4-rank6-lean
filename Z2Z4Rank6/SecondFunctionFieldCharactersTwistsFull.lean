import Z2Z4Rank6.SecondFunctionFieldPointActionsFull
import Z2Z4Rank6.SecondFunctionFieldCharactersBase
import Z2Z4Rank6.ThreeCharacterRationalization
import Z2Z4Rank6.FieldTwistEmbedding

/-!
# The eight twist character groups of the second family

Each product of W,qA,qB defines a quadratic twist over
Q(W). Untwisting over Q(G2) identifies its point group with the
corresponding integral three-sign subgroup. Coordinate descent uses the
proved common fixed field. Rationalization gives the eight
character spaces printed in the proof of Theorem 8.1(b).
-/
namespace Z2Z4Rank6.SecondFunctionField.FullTwistCharacters
noncomputable section
open SecondFamily Common.WeierstrassCoordinates
open scoped TensorProduct
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

abbrev baseEmbedding : Base →+* K := algebraMap Base K
def A : Base := U RatFunc.X
def B : Base := (V RatFunc.X)^2

theorem curve_image_eq : PointScaling.curve (baseEmbedding A) (baseEmbedding B) = F W := by
  ext <;> simp [A,B,PointScaling.curve,F,twistedF,U,V,lambda,W,map_ofNat]

def twistD (χ : Bool × Bool × Bool) : Base :=
  (if χ.1 then RatFunc.X else 1) *
    (if χ.2.1 then qA RatFunc.X else 1) * (if χ.2.2 then qB RatFunc.X else 1)

def twistRoot (χ : Bool × Bool × Bool) : K :=
  (if χ.1 then s1 else 1) * (if χ.2.1 then s2 else 1) * (if χ.2.2 then s3 else 1)

theorem twistRoot_sq (χ : Bool × Bool × Bool) :
    (twistRoot χ)^2 = baseEmbedding (twistD χ) := by
  rcases χ with ⟨a,b,c⟩
  cases a <;> cases b <;> cases c <;>
    simp [twistRoot,twistD,mul_pow,s1_sq,s2_sq,s3_sq,
      baseEmbedding,qA,qB,beta,gamma,W,map_ofNat]

theorem twistRoot_ne_zero (χ : Bool × Bool × Bool) : twistRoot χ ≠ 0 := by
  rcases χ with ⟨a,b,c⟩
  cases a <;> cases b <;> cases c <;>
    simp [twistRoot,s1_ne_zero,s2_ne_zero,s3_ne_zero]

theorem twistD_ne_zero (χ : Bool × Bool × Bool) : twistD χ ≠ 0 := by
  intro hd
  have hs := twistRoot_sq χ
  rw [hd,map_zero] at hs
  exact twistRoot_ne_zero χ (sq_eq_zero_iff.mp hs)

theorem sigma1_twistRoot (χ : Bool × Bool × Bool) :
    sigma1 (twistRoot χ) = if χ.1 then -twistRoot χ else twistRoot χ := by
  rcases χ with ⟨a,b,c⟩
  cases a <;> cases b <;> cases c <;>
    simp only [twistRoot,Bool.false_eq_true,ite_false,ite_true,map_mul,map_one,
      sigma1_s1,sigma1_s2,sigma1_s3,neg_mul]

theorem sigma2_twistRoot (χ : Bool × Bool × Bool) :
    sigma2 (twistRoot χ) = if χ.2.1 then -twistRoot χ else twistRoot χ := by
  rcases χ with ⟨a,b,c⟩
  cases a <;> cases b <;> cases c <;>
    simp only [twistRoot,Bool.false_eq_true,ite_false,ite_true,map_mul,map_one,
      sigma2_s1,sigma2_s2,sigma2_s3,mul_neg,neg_mul]

theorem sigma3_twistRoot (χ : Bool × Bool × Bool) :
    sigma3 (twistRoot χ) = if χ.2.2 then -twistRoot χ else twistRoot χ := by
  rcases χ with ⟨a,b,c⟩
  cases a <;> cases b <;> cases c <;>
    simp only [twistRoot,Bool.false_eq_true,ite_false,ite_true,map_mul,map_one,
      sigma3_s1,sigma3_s2,sigma3_s3,mul_neg]

def twistCurve (χ : Bool × Bool × Bool) : WeierstrassCurve Base :=
  twistedF RatFunc.X (twistD χ)

abbrev twistPoints (χ : Bool × Bool × Bool) := (twistCurve χ).toAffine.Point

instance twistCurve_elliptic (χ : Bool × Bool × Bool) : (twistCurve χ).IsElliptic := by
  constructor
  rw [isUnit_iff_ne_zero,twistCurve,twistedF_discriminant]
  exact mul_ne_zero (pow_ne_zero _ (twistD_ne_zero χ))
    (F (RatFunc.X : Base)).isUnit_Δ.ne_zero

theorem twistCurve_eq_long (χ : Bool × Bool × Bool) :
    twistCurve χ = PointScaling.curve (twistD χ*A) ((twistD χ)^2*B) := rfl

def embeddingData (χ : Bool × Bool × Bool) :
    FieldTwistEmbedding.Data baseEmbedding (twistD χ) (twistRoot χ) (twistCurve χ) (F W) :=
  FieldTwistEmbedding.data baseEmbedding A B (twistD χ) (twistRoot χ)
    (twistD_ne_zero χ) (twistRoot_sq χ) (twistCurve χ) (F W)
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
    simp [encode,WeierstrassCurve.Affine.negY,F,twistedF]

abbrev characterSubgroup (χ : Bool × Bool × Bool) : AddSubgroup PointGroup :=
  ThreeCharacterRationalization.characterGroup pointSigma1.toAddMonoidHom
    pointSigma2.toAddMonoidHom pointSigma3.toAddMonoidHom χ

private theorem embed_sign (σ : K ≃ₐ[Base] K) (τ : PointGroup →+ PointGroup)
    (hτ : ∀ P, encode (τ P) = (encode P).map (fun xy => (σ xy.1,σ xy.2)))
    (χ : Bool × Bool × Bool) (ε : Bool)
    (hroot : σ (twistRoot χ) = if ε then -twistRoot χ else twistRoot χ)
    (P : twistPoints χ) :
    τ (embed χ P) = if ε then -(embed χ P) else embed χ P := by
  have hc := (embeddingData χ).coordinates P
  apply encode_injective (F W)
  rw [hτ,hc]
  cases ε
  · rw [ite_eq_right (by decide),hc]
    cases P <;> simp [encode,baseEmbedding,map_div₀,map_mul,σ.commutes,hroot]
  · rw [ite_eq_left (by decide),encode_neg_point,hc]
    cases P <;> simp [encode,baseEmbedding,map_div₀,map_mul,σ.commutes,hroot,mul_neg,div_neg]

theorem embed_mem_characterSubgroup (χ : Bool × Bool × Bool) (P : twistPoints χ) :
    embed χ P ∈ characterSubgroup χ := by
  refine ⟨?_,?_,?_⟩
  · exact embed_sign sigma1 pointSigma1.toAddMonoidHom encode_pointSigma1
      χ χ.1 (sigma1_twistRoot χ) P
  · exact embed_sign sigma2Base pointSigma2.toAddMonoidHom encode_pointSigma2
      χ χ.2.1 (sigma2_twistRoot χ) P
  · exact embed_sign sigma3Base pointSigma3.toAddMonoidHom encode_pointSigma3
      χ χ.2.2 (sigma3_twistRoot χ) P

def characterEmbedding (χ : Bool × Bool × Bool) : twistPoints χ →+ characterSubgroup χ :=
  (embed χ).codRestrict _ (embed_mem_characterSubgroup χ)

theorem characterEmbedding_injective (χ : Bool × Bool × Bool) :
    Function.Injective (characterEmbedding χ) := by
  intro P Q h
  exact embed_injective χ (congrArg Subtype.val h)

private theorem point_sign_coordinates (σ : K ≃ₐ[Base] K) (τ : PointGroup →+ PointGroup)
    (hτ : ∀ P, encode (τ P) = (encode P).map (fun xy => (σ xy.1,σ xy.2)))
    (ε : Bool) (x y : K) (hN : (F W).toAffine.Nonsingular x y)
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
    (hN : (F W).toAffine.Nonsingular x y) (x₀ y₀ : Base)
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
    have h1 := point_sign_coordinates sigma1 pointSigma1.toAddMonoidHom
      encode_pointSigma1 χ.1 x y hN hP.1
    have h2 : sigma2 x=x ∧ sigma2 y=if χ.2.1 then -y else y :=
      point_sign_coordinates sigma2Base pointSigma2.toAddMonoidHom
        encode_pointSigma2 χ.2.1 x y hN hP.2.1
    have h3 : sigma3 x=x ∧ sigma3 y=if χ.2.2 then -y else y :=
      point_sign_coordinates sigma3Base pointSigma3.toAddMonoidHom
        encode_pointSigma3 χ.2.2 x y hN hP.2.2
    have h1x : sigma1 (baseEmbedding (twistD χ)*x)=baseEmbedding (twistD χ)*x := by
      rw [map_mul,sigma1_base,h1.1]
    have h2x : sigma2 (baseEmbedding (twistD χ)*x)=baseEmbedding (twistD χ)*x := by
      rw [map_mul,sigma2_base,h2.1]
    have h3x : sigma3 (baseEmbedding (twistD χ)*x)=baseEmbedding (twistD χ)*x := by
      rw [map_mul,sigma3_base,h3.1]
    have h1y : sigma1 (baseEmbedding (twistD χ)*twistRoot χ*y)=
        baseEmbedding (twistD χ)*twistRoot χ*y := by
      rw [map_mul,map_mul,sigma1_base,sigma1_twistRoot,h1.2]
      cases χ.1 <;> simp
    have h2y : sigma2 (baseEmbedding (twistD χ)*twistRoot χ*y)=
        baseEmbedding (twistD χ)*twistRoot χ*y := by
      rw [map_mul,map_mul,sigma2_base,sigma2_twistRoot,h2.2]
      cases χ.2.1 <;> simp
    have h3y : sigma3 (baseEmbedding (twistD χ)*twistRoot χ*y)=
        baseEmbedding (twistD χ)*twistRoot χ*y := by
      rw [map_mul,map_mul,sigma3_base,sigma3_twistRoot,h3.2]
      cases χ.2.2 <;> simp
    obtain ⟨x₀,hx⟩ := (fixed_iff_in_base _).mp ⟨h1x,h2x,h3x⟩
    obtain ⟨y₀,hy⟩ := (fixed_iff_in_base _).mp ⟨h1y,h2y,h3y⟩
    refine ⟨.some x₀ y₀ (descend_nonsingular χ x y hN x₀ y₀ hx hy),?_⟩
    apply Subtype.ext
    apply encode_injective (F W)
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
  ThreeCharacter.jointSpace (PointScaling.rationalizeHom pointSigma1.toAddMonoidHom)
    (PointScaling.rationalizeHom pointSigma2.toAddMonoidHom)
    (PointScaling.rationalizeHom pointSigma3.toAddMonoidHom) χ

def rationalizedTwistCharacterEquiv (χ : Bool × Bool × Bool) :
    (ℚ ⊗[ℤ] twistPoints χ) ≃ₗ[ℚ] fullCharacterSpace χ :=
  (PointScaling.rationalizeEquiv (characterEquiv χ)).trans
    (ThreeCharacterRationalization.equivCharacterSpace pointSigma1.toAddMonoidHom
      pointSigma2.toAddMonoidHom pointSigma3.toAddMonoidHom
      pointSigma1_involutive pointSigma2_involutive pointSigma3_involutive
      pointSigma1_pointSigma2_commute pointSigma1_pointSigma3_commute
      pointSigma2_pointSigma3_commute χ)

end
end Z2Z4Rank6.SecondFunctionField.FullTwistCharacters
