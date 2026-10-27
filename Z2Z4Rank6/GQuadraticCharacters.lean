import Z2Z4Rank6.GFunctionField
import Z2Z4Rank6.GTwistSelmerData
import Z2Z4Rank6.PointMap
import Z2Z4Rank6.PointScaling
import Z2Z4Rank6.CharacterRationalization

/-!
# Quadratic characters over Q(G)

The quadratic rank decomposition in Proposition 7.2(b) of Jaswal,
DOI: 10.5281/zenodo.23437117. Conjugation acts on the
quadratic field and Weierstrass point group. Coordinate descent
identifies its two sign subgroups with the original and h-twisted groups
over Q(m), before rationalization.
-/

namespace Z2Z4Rank6.GFunctionField.QuadraticCharacters

open Common.WeierstrassCoordinates
open scoped TensorProduct
noncomputable section

abbrev baseEmbedding : Base →+* K := algebraMap Base K
abbrev PointGroup := (X m).toAffine.Point

def conjugation : K ≃ₐ[Base] K :=
  { starRingAut with
    commutes' := by intro c; apply QuadraticAlgebra.ext <;> simp }

@[simp] theorem conjugation_base (r : Base) : conjugation (baseEmbedding r)=baseEmbedding r :=
  conjugation.commutes r

@[simp] theorem conjugation_m : conjugation m=m := conjugation.commutes RatFunc.X

@[simp] theorem conjugation_eta : conjugation eta = -eta := by
  apply QuadraticAlgebra.ext <;> simp [conjugation,eta,QuadraticAlgebra.omega]

theorem conjugation_involutive (z : K) : conjugation (conjugation z)=z := by
  change star (star z)=z
  exact star_star z

theorem fixed_iff_in_base (z : K) :
    conjugation z=z ↔ ∃ b : Base, baseEmbedding b=z := by
  constructor
  · intro hz
    have him : z.im=0 := by
      have hh := congrArg QuadraticAlgebra.im hz
      change -z.im=z.im at hh
      have h2 : (2 : Base)*z.im=0 := by linear_combination -hh
      exact (mul_eq_zero.mp h2).resolve_left (by norm_num)
    refine ⟨z.re, ?_⟩
    apply QuadraticAlgebra.ext
    · rfl
    · exact him.symm
  · rintro ⟨b,rfl⟩
    exact conjugation_base b

theorem exists_base_of_fixed (z : K) (hz : conjugation z=z) :
    ∃ b : Base, baseEmbedding b=z := (fixed_iff_in_base z).mp hz

theorem eta_sq_eq_d : eta^2=baseEmbedding d := by
  rw [eta,sq,QuadraticAlgebra.omega_mul_omega_eq_algebraMap]
  simp only [map_zero,zero_mul,add_zero]

theorem eta_ne_zero : eta ≠ 0 := by
  intro hz
  have hh := congrArg QuadraticAlgebra.im hz
  norm_num [eta,QuadraticAlgebra.omega] at hh

theorem d_ne_zero : d ≠ 0 := by
  intro hz
  apply d_not_isSquare
  exact ⟨0,by simpa only [zero_mul] using hz⟩

private theorem curve_conjugation : (X m).map conjugation.toRingHom=X m := by
  ext <;> simp [X,E,a,b,map_ofNat]

def pointEnd : PointGroup →+ PointGroup :=
  (PointScaling.pointCongr curve_conjugation).toAddMonoidHom.comp
    (fieldPointMap conjugation.toRingHom (X m))

theorem encode_pointEnd (P : PointGroup) :
    encode (pointEnd P)=(encode P).map (fun xy => (conjugation xy.1,conjugation xy.2)) := by
  unfold pointEnd
  rw [AddMonoidHom.comp_apply,AddEquiv.coe_toAddMonoidHom,
    PointScaling.encode_pointCongr,encode_fieldPointMap]
  rfl

theorem pointEnd_involutive (P : PointGroup) : pointEnd (pointEnd P)=P := by
  apply encode_injective (X m)
  rw [encode_pointEnd,encode_pointEnd]
  cases P with
  | zero => rfl
  | some x y h =>
    change some (conjugation (conjugation x),conjugation (conjugation y))=some (x,y)
    rw [conjugation_involutive,conjugation_involutive]

/-- The additive involution induced by η↦-η. -/
def pointConjugation : PointGroup ≃+ PointGroup where
  toFun := pointEnd
  invFun := pointEnd
  left_inv := pointEnd_involutive
  right_inv := pointEnd_involutive
  map_add' := pointEnd.map_add

theorem pointConjugation_involutive (P : PointGroup) :
    pointConjugation (pointConjugation P)=P := pointEnd_involutive P

theorem encode_pointConjugation (P : PointGroup) :
    encode (pointConjugation P)=(encode P).map (fun xy => (conjugation xy.1,conjugation xy.2)) :=
  encode_pointEnd P

def A : Base := (a RatFunc.X)^2+(b RatFunc.X)^2
def B : Base := (a RatFunc.X)^2*(b RatFunc.X)^2

theorem curve_image_eq : PointScaling.curve (baseEmbedding A) (baseEmbedding B)=X m := by
  ext <;> simp [A,B,PointScaling.curve,X,E,a,b,m,map_ofNat]

def twistD (ε : Bool) : Base := if ε then d else 1
def twistRoot (ε : Bool) : K := if ε then eta else 1

theorem twistRoot_sq (ε : Bool) : twistRoot ε^2=baseEmbedding (twistD ε) := by
  cases ε
  · simp [twistRoot,twistD]
  · exact eta_sq_eq_d

theorem twistRoot_ne_zero (ε : Bool) : twistRoot ε≠0 := by
  cases ε
  · exact one_ne_zero
  · exact eta_ne_zero

theorem twistD_ne_zero (ε : Bool) : twistD ε≠0 := by
  cases ε
  · exact one_ne_zero
  · exact d_ne_zero

theorem conjugation_twistRoot (ε : Bool) :
    conjugation (twistRoot ε)=if ε then -twistRoot ε else twistRoot ε := by
  cases ε <;> simp only [twistRoot,Bool.false_eq_true,ite_false,ite_true,map_one,conjugation_eta]

abbrev twistCurve (ε : Bool) : WeierstrassCurve Base :=
  PointScaling.curve (twistD ε*A) (twistD ε^2*B)

def embed (ε : Bool) : (twistCurve ε).toAffine.Point →+ PointGroup :=
  (PointScaling.pointCongr curve_image_eq).toAddMonoidHom.comp
    (PointScaling.baseChangeUntwistHom baseEmbedding A B (twistD ε) (twistRoot ε)
      (twistD_ne_zero ε) (twistRoot_sq ε))

theorem encode_embed (ε : Bool) (P : (twistCurve ε).toAffine.Point) :
    encode (embed ε P)=(encode P).map (fun xy =>
      (baseEmbedding xy.1/baseEmbedding (twistD ε),
        baseEmbedding xy.2/(baseEmbedding (twistD ε)*twistRoot ε))) := by
  unfold embed
  rw [AddMonoidHom.comp_apply,AddEquiv.coe_toAddMonoidHom,
    PointScaling.encode_pointCongr,PointScaling.encode_baseChangeUntwistHom]

theorem embed_injective (ε : Bool) : Function.Injective (embed ε) := by
  intro P Q hPQ
  have hh := congrArg encode hPQ
  rw [encode_embed,encode_embed] at hh
  have hd : baseEmbedding (twistD ε)≠0 := (map_ne_zero baseEmbedding).mpr (twistD_ne_zero ε)
  have hdr := mul_ne_zero hd (twistRoot_ne_zero ε)
  apply encode_injective (twistCurve ε)
  cases P <;> cases Q <;> simp only [encode,Option.map_none,Option.map_some,
    Option.some.injEq,Prod.mk.injEq,reduceCtorEq] at hh ⊢
  exact ⟨baseEmbedding.injective ((div_left_inj' hd).mp hh.1),
    baseEmbedding.injective ((div_left_inj' hdr).mp hh.2)⟩

private theorem encode_neg_point (P : PointGroup) :
    encode (-P)=(encode P).map (fun xy => (xy.1,-xy.2)) := by
  cases P with
  | zero => rfl
  | some x y h =>
    rw [WeierstrassCurve.Affine.Point.neg_some]
    simp [encode,WeierstrassCurve.Affine.negY,X,E]

/-- The sign subgroup, written in the generic character API with the
second involution equal to the identity. -/
def characterSubgroup (ε : Bool) : AddSubgroup PointGroup :=
  CharacterRationalization.characterGroup pointConjugation.toAddMonoidHom
    (AddMonoidHom.id PointGroup) (ε,false)

private theorem embed_sign (ε : Bool) (P : (twistCurve ε).toAffine.Point) :
    pointConjugation (embed ε P)=if ε then -(embed ε P) else embed ε P := by
  apply encode_injective (X m)
  rw [encode_pointConjugation,encode_embed]
  cases ε
  · rw [ite_eq_right (by decide),encode_embed]
    cases P <;> simp [encode,baseEmbedding,map_div₀,map_mul,conjugation.commutes,
      conjugation_twistRoot]
  · rw [ite_eq_left (by decide),encode_neg_point,encode_embed]
    cases P <;> simp [encode,baseEmbedding,map_div₀,map_mul,conjugation.commutes,
      conjugation_twistRoot,mul_neg,div_neg]

theorem embed_mem_characterSubgroup (ε : Bool) (P : (twistCurve ε).toAffine.Point) :
    embed ε P ∈ characterSubgroup ε := by
  change pointConjugation (embed ε P)=(if ε then -(embed ε P) else embed ε P) ∧
    embed ε P=embed ε P
  exact ⟨embed_sign ε P,rfl⟩

def characterEmbedding (ε : Bool) :
    (twistCurve ε).toAffine.Point →+ characterSubgroup ε :=
  (embed ε).codRestrict _ (embed_mem_characterSubgroup ε)

theorem characterEmbedding_injective (ε : Bool) : Function.Injective (characterEmbedding ε) := by
  intro P Q hPQ
  exact embed_injective ε (congrArg Subtype.val hPQ)

private theorem point_sign_coordinates (ε : Bool) (x y : K)
    (hN : (X m).toAffine.Nonsingular x y)
    (h : pointConjugation (.some x y hN)=if ε then -(.some x y hN) else .some x y hN) :
    conjugation x=x ∧ conjugation y=if ε then -y else y := by
  have he := congrArg encode h
  rw [encode_pointConjugation] at he
  cases ε
  · simpa only [Bool.false_eq_true,ite_false,encode,Option.map_some,
      Option.some.injEq,Prod.mk.injEq] using he
  · rw [ite_eq_left (by decide),encode_neg_point] at he
    simpa only [encode,Option.map_some,Option.some.injEq,Prod.mk.injEq,ite_true] using he

private theorem descend_nonsingular_general {F L : Type*} [Field F] [Field L]
    (f : F →+* L) (A B d : F) (r : L) (hr0 : r ≠ 0) (hr : r ^ 2 = f d)
    (x y : L) (hN : (PointScaling.curve (f A) (f B)).toAffine.Nonsingular x y)
    (x₀ y₀ : F) (hx : f x₀ = f d * x) (hy : f y₀ = f d * r * y) :
    (PointScaling.curve (d * A) (d ^ 2 * B)).toAffine.Nonsingular x₀ y₀ := by
  have hs := PointScaling.scale_nonsingular (f A) (f B) r hr0 x y hN
  have h3 : r ^ 3 = f d * r := by rw [← hr]; ring
  have h4 : r ^ 4 = (f d) ^ 2 := by rw [← hr]; ring
  rw [h3, h4, hr] at hs
  apply ((PointScaling.curve (d * A) (d ^ 2 * B)).toAffine.map_nonsingular
    (f := f) f.injective x₀ y₀).mp
  change ((PointScaling.curve (d * A) (d ^ 2 * B)).map f).toAffine.Nonsingular (f x₀) (f y₀)
  rw [PointScaling.map_curve, map_mul, map_mul, map_pow, hx, hy]
  exact hs

private theorem descend_nonsingular (ε : Bool) (x y : K)
    (hN : (X m).toAffine.Nonsingular x y) (x₀ y₀ : Base)
    (hx : baseEmbedding x₀=baseEmbedding (twistD ε)*x)
    (hy : baseEmbedding y₀=baseEmbedding (twistD ε)*twistRoot ε*y) :
    (twistCurve ε).toAffine.Nonsingular x₀ y₀ := by
  apply descend_nonsingular_general baseEmbedding A B (twistD ε) (twistRoot ε)
    (twistRoot_ne_zero ε) (twistRoot_sq ε) x y _ x₀ y₀ hx hy
  rw [curve_image_eq]
  exact hN

/-- Every sign point descends to the corresponding base twist. -/
theorem characterEmbedding_surjective (ε : Bool) : Function.Surjective (characterEmbedding ε) := by
  rintro ⟨P,hP⟩
  cases P with
  | zero =>
    refine ⟨0,?_⟩
    apply Subtype.ext
    exact (embed ε).map_zero
  | some x y hN =>
    have hsign := point_sign_coordinates ε x y hN hP.1
    have hX : conjugation (baseEmbedding (twistD ε)*x)=baseEmbedding (twistD ε)*x := by
      rw [map_mul,conjugation_base,hsign.1]
    have hY : conjugation (baseEmbedding (twistD ε)*twistRoot ε*y)=
        baseEmbedding (twistD ε)*twistRoot ε*y := by
      rw [map_mul,map_mul,conjugation_base,conjugation_twistRoot,hsign.2]
      cases ε <;> simp
    obtain ⟨x₀,hx⟩ := exists_base_of_fixed _ hX
    obtain ⟨y₀,hy⟩ := exists_base_of_fixed _ hY
    refine ⟨.some x₀ y₀ (descend_nonsingular ε x y hN x₀ y₀ hx hy),?_⟩
    apply Subtype.ext
    apply encode_injective (X m)
    change encode (embed ε (.some x₀ y₀ _))=_
    rw [encode_embed]
    have hd : baseEmbedding (twistD ε)≠0 := (map_ne_zero baseEmbedding).mpr (twistD_ne_zero ε)
    simp only [encode,Option.map_some,hx,hy,Option.some.injEq,Prod.mk.injEq]
    constructor <;> field_simp [hd,twistRoot_ne_zero ε]

/-- Base-twist groups are exactly the two integral sign subgroups. -/
def characterEquiv (ε : Bool) :
    (twistCurve ε).toAffine.Point ≃+ characterSubgroup ε :=
  AddEquiv.ofBijective (characterEmbedding ε)
    ⟨characterEmbedding_injective ε,characterEmbedding_surjective ε⟩

theorem twistCurve_false : twistCurve false=RationalFunctionFamily.curve := by
  ext <;> simp [twistCurve,twistD,PointScaling.curve,A,B,RationalFunctionFamily.curve,
    RationalFunctionFamily.parameter,X,E]

theorem polyToRF_h_eq_d : GusicTadic.polyToRF GTwistSelmer.hPolynomial=d := by
  simp [GusicTadic.polyToRF,GTwistSelmer.hPolynomial,d,h,map_ofNat]

theorem twistCurve_true : twistCurve true=GusicTadic.genericModel GTwistSelmer.hPolynomial := by
  ext <;> simp [twistCurve,twistD,PointScaling.curve,A,B,GusicTadic.genericModel,
    GusicTadic.twistModel,polyToRF_h_eq_d,mul_assoc]

end
end Z2Z4Rank6.GFunctionField.QuadraticCharacters
