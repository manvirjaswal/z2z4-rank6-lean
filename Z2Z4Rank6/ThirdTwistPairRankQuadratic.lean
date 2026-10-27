import Mathlib.Algebra.QuadraticAlgebra.Basic
import Z2Z4Rank6.PointMap
import Z2Z4Rank6.PointScaling
import Z2Z4Rank6.CharacterRationalization
import Z2Z4Rank6.GQuadraticLinear
import Mathlib.LinearAlgebra.Dimension.Localization

/-! Quadratic-extension point-group rank decomposition, proved by
coordinate descent and the two conjugation eigenspaces. -/
namespace Z2Z4Rank6.ThirdTwistPairRank.Quadratic
noncomputable section
open Common.WeierstrassCoordinates
open scoped TensorProduct
open scoped Classical
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

structure Data (F : Type*) [Field F] where
  d : F
  nonsquare : ¬ IsSquare d
  A : F
  B : F

variable {F : Type*} [Field F] [CharZero F] [DecidableEq F]
variable (D : Data F)
instance nonsquare : Fact (¬IsSquare D.d) := ⟨D.nonsquare⟩
abbrev K := QuadraticAlgebra F D.d 0
abbrev model : WeierstrassCurve (K D) :=
  PointScaling.curve (algebraMap F (K D) D.A) (algebraMap F (K D) D.B)
def root : K D := QuadraticAlgebra.omega

abbrev baseEmbedding : F →+* (K D) := algebraMap F (K D)
abbrev PointGroup := (model D).toAffine.Point

def conjugation : (K D) ≃ₐ[F] (K D) :=
  { starRingAut with
    commutes' := by intro c; apply QuadraticAlgebra.ext <;> simp }

omit [CharZero F] in
omit [DecidableEq F] in
@[simp] theorem conjugation_base (r : F) : (conjugation D) ((baseEmbedding D) r)=(baseEmbedding D) r :=
  (conjugation D).commutes r

omit [CharZero F] in
omit [DecidableEq F] in
@[simp] theorem conjugation_root : (conjugation D) (root D) = -(root D) := by
  apply QuadraticAlgebra.ext <;> simp [conjugation,root,QuadraticAlgebra.omega]

omit [CharZero F] in
omit [DecidableEq F] in
theorem conjugation_involutive (z : (K D)) : (conjugation D) ((conjugation D) z)=z := by
  change star (star z)=z
  exact star_star z

omit [DecidableEq F] in
theorem fixed_iff_in_base (z : (K D)) :
    (conjugation D) z=z ↔ ∃ b : F, (baseEmbedding D) b=z := by
  constructor
  · intro hz
    have him : z.im=0 := by
      have hh := congrArg QuadraticAlgebra.im hz
      change -z.im=z.im at hh
      have h2 : (2 : F)*z.im=0 := by linear_combination -hh
      exact (mul_eq_zero.mp h2).resolve_left (by norm_num)
    refine ⟨z.re, ?_⟩
    apply QuadraticAlgebra.ext
    · rfl
    · exact him.symm
  · rintro ⟨b,rfl⟩
    exact (conjugation_base D) b

omit [DecidableEq F] in
theorem exists_base_of_fixed (z : (K D)) (hz : (conjugation D) z=z) :
    ∃ b : F, (baseEmbedding D) b=z := ((fixed_iff_in_base D) z).mp hz

omit [CharZero F] in
omit [DecidableEq F] in
theorem eta_sq_eq_d : (root D)^2=(baseEmbedding D) D.d := by
  rw [root,sq,QuadraticAlgebra.omega_mul_omega_eq_algebraMap]
  simp only [map_zero,zero_mul,add_zero]

omit [DecidableEq F] in
theorem eta_ne_zero : (root D) ≠ 0 := by
  intro hz
  have hh := congrArg QuadraticAlgebra.im hz
  norm_num [root,QuadraticAlgebra.omega] at hh

omit [CharZero F] in
omit [DecidableEq F] in
theorem d_ne_zero : D.d ≠ 0 := by
  intro hz
  apply D.nonsquare
  exact ⟨0,by simpa only [zero_mul] using hz⟩

omit [CharZero F] in
omit [DecidableEq F] in
private theorem curve_conjugation : (model D).map (conjugation D).toRingHom=model D := by
  ext <;> simp [model,PointScaling.curve,(conjugation D).commutes]

def pointEnd : (PointGroup D) →+ (PointGroup D) :=
  (PointScaling.pointCongr (curve_conjugation D)).toAddMonoidHom.comp
    (fieldPointMap (conjugation D).toRingHom (model D))

omit [CharZero F] in
theorem encode_pointEnd (P : (PointGroup D)) :
    encode ((pointEnd D) P)=(encode P).map (fun xy => ((conjugation D) xy.1,(conjugation D) xy.2)) := by
  unfold pointEnd
  rw [AddMonoidHom.comp_apply,AddEquiv.coe_toAddMonoidHom,
    PointScaling.encode_pointCongr,encode_fieldPointMap]
  rfl

omit [CharZero F] in
theorem pointEnd_involutive (P : (PointGroup D)) : (pointEnd D) ((pointEnd D) P)=P := by
  apply encode_injective (model D)
  rw [(encode_pointEnd D),(encode_pointEnd D)]
  cases P with
  | zero => rfl
  | some x y h =>
    change some ((conjugation D) ((conjugation D) x),(conjugation D) ((conjugation D) y))=some (x,y)
    rw [(conjugation_involutive D),(conjugation_involutive D)]

/-- The additive involution induced by η↦-η. -/
def pointConjugation : (PointGroup D) ≃+ (PointGroup D) where
  toFun := (pointEnd D)
  invFun := (pointEnd D)
  left_inv := (pointEnd_involutive D)
  right_inv := (pointEnd_involutive D)
  map_add' := (pointEnd D).map_add

omit [CharZero F] in
theorem pointConjugation_involutive (P : (PointGroup D)) :
    (pointConjugation D) ((pointConjugation D) P)=P := (pointEnd_involutive D) P

omit [CharZero F] in
theorem encode_pointConjugation (P : (PointGroup D)) :
    encode ((pointConjugation D) P)=(encode P).map (fun xy => ((conjugation D) xy.1,(conjugation D) xy.2)) :=
  (encode_pointEnd D) P

omit [CharZero F] in
omit [DecidableEq F] in
theorem curve_image_eq : PointScaling.curve ((baseEmbedding D) D.A) ((baseEmbedding D) D.B)=model D := rfl

def twistD (ε : Bool) : F := if ε then D.d else 1
def twistRoot (ε : Bool) : (K D) := if ε then (root D) else 1

omit [CharZero F] in
omit [DecidableEq F] in
theorem twistRoot_sq (ε : Bool) : (twistRoot D) ε^2=(baseEmbedding D) ((twistD D) ε) := by
  cases ε
  · simp [twistRoot,twistD]
  · exact (eta_sq_eq_d D)

omit [DecidableEq F] in
theorem twistRoot_ne_zero (ε : Bool) : (twistRoot D) ε≠0 := by
  cases ε
  · exact one_ne_zero
  · exact (eta_ne_zero D)

omit [DecidableEq F] in
theorem twistD_ne_zero (ε : Bool) : (twistD D) ε≠0 := by
  cases ε
  · exact one_ne_zero
  · exact (d_ne_zero D)

omit [CharZero F] in
omit [DecidableEq F] in
theorem conjugation_twistRoot (ε : Bool) :
    (conjugation D) ((twistRoot D) ε)=if ε then -(twistRoot D) ε else (twistRoot D) ε := by
  cases ε <;> simp only [twistRoot,Bool.false_eq_true,ite_false,ite_true,map_one,(conjugation_root D)]

abbrev twistCurve (ε : Bool) : WeierstrassCurve F :=
  PointScaling.curve ((twistD D) ε*D.A) ((twistD D) ε^2*D.B)

def embed (ε : Bool) : ((twistCurve D) ε).toAffine.Point →+ (PointGroup D) :=
  (PointScaling.pointCongr (curve_image_eq D)).toAddMonoidHom.comp
    (PointScaling.baseChangeUntwistHom (baseEmbedding D) D.A D.B ((twistD D) ε) ((twistRoot D) ε)
      ((twistD_ne_zero D) ε) ((twistRoot_sq D) ε))

theorem encode_embed (ε : Bool) (P : ((twistCurve D) ε).toAffine.Point) :
    encode ((embed D) ε P)=(encode P).map (fun xy =>
      ((baseEmbedding D) xy.1/(baseEmbedding D) ((twistD D) ε),
        (baseEmbedding D) xy.2/((baseEmbedding D) ((twistD D) ε)*(twistRoot D) ε))) := by
  unfold embed
  rw [AddMonoidHom.comp_apply,AddEquiv.coe_toAddMonoidHom,
    PointScaling.encode_pointCongr,PointScaling.encode_baseChangeUntwistHom]

theorem embed_injective (ε : Bool) : Function.Injective ((embed D) ε) := by
  intro P Q hPQ
  have hh := congrArg encode hPQ
  rw [(encode_embed D),(encode_embed D)] at hh
  have hd : (baseEmbedding D) ((twistD D) ε)≠0 := (map_ne_zero (baseEmbedding D)).mpr ((twistD_ne_zero D) ε)
  have hdr := mul_ne_zero hd ((twistRoot_ne_zero D) ε)
  apply encode_injective ((twistCurve D) ε)
  cases P <;> cases Q <;> simp only [encode,Option.map_none,Option.map_some,
    Option.some.injEq,Prod.mk.injEq,reduceCtorEq] at hh ⊢
  exact ⟨(baseEmbedding D).injective ((div_left_inj' hd).mp hh.1),
    (baseEmbedding D).injective ((div_left_inj' hdr).mp hh.2)⟩

omit [CharZero F] in
omit [DecidableEq F] in
private theorem encode_neg_point (P : (PointGroup D)) :
    encode (-P)=(encode P).map (fun xy => (xy.1,-xy.2)) := by
  cases P with
  | zero => rfl
  | some x y h =>
    rw [WeierstrassCurve.Affine.Point.neg_some]
    simp [encode,WeierstrassCurve.Affine.negY,model,PointScaling.curve]

/-- The sign subgroup, written in the generic character API with the
second involution equal to the identity. -/
def characterSubgroup (ε : Bool) : AddSubgroup (PointGroup D) :=
  CharacterRationalization.characterGroup (pointConjugation D).toAddMonoidHom
    (AddMonoidHom.id (PointGroup D)) (ε,false)

private theorem embed_sign (ε : Bool) (P : ((twistCurve D) ε).toAffine.Point) :
    (pointConjugation D) ((embed D) ε P)=if ε then -((embed D) ε P) else (embed D) ε P := by
  apply encode_injective (model D)
  rw [(encode_pointConjugation D),(encode_embed D)]
  cases ε
  · rw [ite_eq_right (by decide),(encode_embed D)]
    cases P <;> simp [encode,baseEmbedding,map_div₀,map_mul,(conjugation D).commutes,
      (conjugation_twistRoot D)]
  · rw [ite_eq_left (by decide),(encode_neg_point D),(encode_embed D)]
    cases P <;> simp [encode,baseEmbedding,map_div₀,map_mul,(conjugation D).commutes,
      (conjugation_twistRoot D),mul_neg,div_neg]

theorem embed_mem_characterSubgroup (ε : Bool) (P : ((twistCurve D) ε).toAffine.Point) :
    (embed D) ε P ∈ (characterSubgroup D) ε := by
  change (pointConjugation D) ((embed D) ε P)=(if ε then -((embed D) ε P) else (embed D) ε P) ∧
    (embed D) ε P=(embed D) ε P
  exact ⟨(embed_sign D) ε P,rfl⟩

def characterEmbedding (ε : Bool) :
    ((twistCurve D) ε).toAffine.Point →+ (characterSubgroup D) ε :=
  ((embed D) ε).codRestrict _ ((embed_mem_characterSubgroup D) ε)

theorem characterEmbedding_injective (ε : Bool) : Function.Injective ((characterEmbedding D) ε) := by
  intro P Q hPQ
  exact (embed_injective D) ε (congrArg Subtype.val hPQ)

omit [CharZero F] in
private theorem point_sign_coordinates (ε : Bool) (x y : (K D))
    (hN : (model D).toAffine.Nonsingular x y)
    (h : (pointConjugation D) (.some x y hN)=if ε then -(.some x y hN) else .some x y hN) :
    (conjugation D) x=x ∧ (conjugation D) y=if ε then -y else y := by
  have he := congrArg encode h
  rw [(encode_pointConjugation D)] at he
  cases ε
  · simpa only [Bool.false_eq_true,ite_false,encode,Option.map_some,
      Option.some.injEq,Prod.mk.injEq] using he
  · rw [ite_eq_left (by decide),(encode_neg_point D)] at he
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

omit [DecidableEq F] in
private theorem descend_nonsingular (ε : Bool) (x y : (K D))
    (hN : (model D).toAffine.Nonsingular x y) (x₀ y₀ : F)
    (hx : (baseEmbedding D) x₀=(baseEmbedding D) ((twistD D) ε)*x)
    (hy : (baseEmbedding D) y₀=(baseEmbedding D) ((twistD D) ε)*(twistRoot D) ε*y) :
    ((twistCurve D) ε).toAffine.Nonsingular x₀ y₀ := by
  apply descend_nonsingular_general (baseEmbedding D) D.A D.B ((twistD D) ε) ((twistRoot D) ε)
    ((twistRoot_ne_zero D) ε) ((twistRoot_sq D) ε) x y _ x₀ y₀ hx hy
  rw [(curve_image_eq D)]
  exact hN

/-- Every sign point descends to the corresponding base twist. -/
theorem characterEmbedding_surjective (ε : Bool) : Function.Surjective ((characterEmbedding D) ε) := by
  rintro ⟨P,hP⟩
  cases P with
  | zero =>
    refine ⟨0,?_⟩
    apply Subtype.ext
    exact ((embed D) ε).map_zero
  | some x y hN =>
    have hsign := (point_sign_coordinates D) ε x y hN hP.1
    have hX : (conjugation D) ((baseEmbedding D) ((twistD D) ε)*x)=(baseEmbedding D) ((twistD D) ε)*x := by
      rw [map_mul,(conjugation_base D),hsign.1]
    have hY : (conjugation D) ((baseEmbedding D) ((twistD D) ε)*(twistRoot D) ε*y)=
        (baseEmbedding D) ((twistD D) ε)*(twistRoot D) ε*y := by
      rw [map_mul,map_mul,(conjugation_base D),(conjugation_twistRoot D),hsign.2]
      cases ε <;> simp
    obtain ⟨x₀,hx⟩ := (exists_base_of_fixed D) _ hX
    obtain ⟨y₀,hy⟩ := (exists_base_of_fixed D) _ hY
    refine ⟨.some x₀ y₀ ((descend_nonsingular D) ε x y hN x₀ y₀ hx hy),?_⟩
    apply Subtype.ext
    apply encode_injective (model D)
    change encode ((embed D) ε (.some x₀ y₀ _))=_
    rw [(encode_embed D)]
    have hd : (baseEmbedding D) ((twistD D) ε)≠0 := (map_ne_zero (baseEmbedding D)).mpr ((twistD_ne_zero D) ε)
    simp only [encode,Option.map_some,hx,hy,Option.some.injEq,Prod.mk.injEq]
    constructor <;> field_simp [hd,(twistRoot_ne_zero D) ε]

/-- Base-twist groups are exactly the two integral sign subgroups. -/
def characterEquiv (ε : Bool) :
    ((twistCurve D) ε).toAffine.Point ≃+ (characterSubgroup D) ε :=
  AddEquiv.ofBijective ((characterEmbedding D) ε)
    ⟨(characterEmbedding_injective D) ε,(characterEmbedding_surjective D) ε⟩



abbrev RationalizedPoints := ℚ ⊗[ℤ] (PointGroup D)

def linearConjugation : (RationalizedPoints D) →ₗ[ℚ] (RationalizedPoints D) :=
  PointScaling.rationalizeHom (pointConjugation D).toAddMonoidHom

omit [CharZero F] in
theorem linearConjugation_involutive :
    (linearConjugation D).comp (linearConjugation D)=LinearMap.id :=
  PointScaling.rationalizeHom_involutive _ (pointConjugation_involutive D)

def characterSpace (ε : Bool) : Submodule ℚ (RationalizedPoints D) :=
  QuadraticLinear.signSpace (linearConjugation D) ε

private theorem rationalize_id (G : Type*) [AddCommGroup G] :
    PointScaling.rationalizeHom (AddMonoidHom.id G)=LinearMap.id := by
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul q P => rfl
  | add x y hx hy => simp only [map_add] at hx hy ⊢; rw [hx,hy]

def rationalizedTwistCharacterEquiv (ε : Bool) :
    (ℚ ⊗[ℤ] ((twistCurve D) ε).toAffine.Point) ≃ₗ[ℚ] (characterSpace D) ε := by
  have e : (ℚ ⊗[ℤ] (characterSubgroup D) ε) ≃ₗ[ℚ] (characterSpace D) ε := by
    have e0 := CharacterRationalization.equivCharacterSpace (pointConjugation D).toAddMonoidHom
      (AddMonoidHom.id (PointGroup D)) (pointConjugation_involutive D)
      (fun _ => rfl) (fun _ => rfl) (ε,false)
    rw [rationalize_id (PointGroup D)] at e0
    exact e0
  exact (PointScaling.rationalizeEquiv ((characterEquiv D) ε)).trans e

/-- The rationalized Q(G) group is the product of the original and
h-twisted rationalized Q(m) groups. -/
def quadraticDecomposition : (RationalizedPoints D) ≃ₗ[ℚ]
    (ℚ ⊗[ℤ] ((twistCurve D) false).toAffine.Point) ×
      (ℚ ⊗[ℤ] ((twistCurve D) true).toAffine.Point) :=
  (QuadraticLinear.decompositionEquiv (linearConjugation D) (linearConjugation_involutive D)).trans
    (((rationalizedTwistCharacterEquiv D) false).symm.prodCongr
      ((rationalizedTwistCharacterEquiv D) true).symm)

private theorem group_rank_eq_rationalized_rank (G : Type*) [AddCommGroup G] :
    Module.rank ℤ G=Module.rank ℚ (ℚ ⊗[ℤ] G) := by
  calc
    Module.rank ℤ G=Module.rank ℤ (ℚ ⊗[ℤ] G) :=
      (IsLocalizedModule.rank_eq (nonZeroDivisors ℤ) le_rfl (TensorProduct.mk ℤ ℚ G 1)).symm
    _ = Module.rank ℚ (ℚ ⊗[ℤ] G) :=
      (IsFractionRing.rank_right_eq ℤ ℚ (ℚ ⊗[ℤ] G)).symm

theorem pointGroup_rank_twist_decomposition : Module.rank ℤ (model D).toAffine.Point=
    Module.rank ℤ ((twistCurve D) false).toAffine.Point+
      Module.rank ℤ ((twistCurve D) true).toAffine.Point := by
  rw [group_rank_eq_rationalized_rank (PointGroup D),(quadraticDecomposition D).rank_eq,rank_prod']
  rw [←group_rank_eq_rationalized_rank,←group_rank_eq_rationalized_rank]


end
end Z2Z4Rank6.ThirdTwistPairRank.Quadratic
