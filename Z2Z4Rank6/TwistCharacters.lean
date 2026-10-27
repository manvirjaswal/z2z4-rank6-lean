module

public import Z2Z4Rank6.FunctionFieldPointActions
public import Z2Z4Rank6.PointScaling

@[expose] public section

/-!
# Quadratic twists and the character subgroups

The descent step underlying Remark 4.3 and Proposition 5.2 of Manvir Jaswal,
"Infinitely many elliptic curves with torsion Z/2Z × Z/4Z and rank at least six",
DOI: 10.5281/zenodo.23437117.

The source groups are rational points over Q(m), and the target is the
point group over the constructed Q(C).
-/

namespace Z2Z4Rank6.FunctionField.TwistCharacters

open Common.WeierstrassCoordinates

noncomputable section

set_option maxHeartbeats 200000

abbrev baseEmbedding : Base →+* K := algebraMap Base K

def A : Base := (a RatFunc.X) ^ 2 + (b RatFunc.X) ^ 2
def B : Base := (a RatFunc.X) ^ 2 * (b RatFunc.X) ^ 2

theorem curve_image_eq :
    PointScaling.curve (baseEmbedding A) (baseEmbedding B) = X m := by
  ext <;> simp [A, B, PointScaling.curve, X, E, a, b, m, map_ofNat]

/-- The four square classes, including the paper's q₁₂=d₁d₂/25. -/
def twistD (χ : Bool × Bool) : Base :=
  if χ.1 then (if χ.2 then d1 * d2 / 25 else d1) else (if χ.2 then d2 else 1)

def twistRoot (χ : Bool × Bool) : K :=
  if χ.1 then (if χ.2 then u * v / 5 else u) else (if χ.2 then v else 1)

theorem twistRoot_sq (χ : Bool × Bool) : twistRoot χ ^ 2 = baseEmbedding (twistD χ) := by
  rcases χ with ⟨ε, δ⟩
  cases ε <;> cases δ <;> simp only [twistRoot, twistD, Bool.false_eq_true,
    ite_false, ite_true]
  · simp
  · exact v_sq_eq_d2
  · exact u_sq_eq_d1
  · rw [div_pow, mul_pow, u_sq_eq_d1, v_sq_eq_d2, map_div₀, map_mul]
    rw [show (5 : K) ^ 2 = 25 by norm_num,
      show baseEmbedding (25 : Base) = (25 : K) from map_natCast baseEmbedding 25]

theorem twistRoot_ne_zero (χ : Bool × Bool) : twistRoot χ ≠ 0 := by
  rcases χ with ⟨ε, δ⟩
  cases ε <;> cases δ <;> simp only [twistRoot, Bool.false_eq_true,
    ite_false, ite_true]
  · exact one_ne_zero
  · exact v_ne_zero
  · exact u_ne_zero
  · exact div_ne_zero (mul_ne_zero u_ne_zero v_ne_zero) (by norm_num)

theorem twistD_ne_zero (χ : Bool × Bool) : twistD χ ≠ 0 := by
  intro hd
  have hh := twistRoot_sq χ
  rw [hd, map_zero] at hh
  exact twistRoot_ne_zero χ (sq_eq_zero_iff.mp hh)

theorem sigmaU_twistRoot (χ : Bool × Bool) :
    sigmaU (twistRoot χ) = if χ.1 then -twistRoot χ else twistRoot χ := by
  rcases χ with ⟨ε, δ⟩
  cases ε <;> cases δ <;> simp only [twistRoot,
    Bool.false_eq_true, ite_false, ite_true, map_one, map_mul, map_div₀, map_ofNat,
    sigmaU_u, sigmaU_v, neg_mul, neg_div]

theorem sigmaV_twistRoot (χ : Bool × Bool) :
    sigmaV (twistRoot χ) = if χ.2 then -twistRoot χ else twistRoot χ := by
  rcases χ with ⟨ε, δ⟩
  cases ε <;> cases δ <;> simp only [twistRoot,
    Bool.false_eq_true, ite_false, ite_true, map_one, map_mul, map_div₀, map_ofNat,
    sigmaV_u, sigmaV_v, mul_neg, neg_div]

abbrev twistCurve (χ : Bool × Bool) : WeierstrassCurve Base :=
  PointScaling.curve (twistD χ * A) (twistD χ ^ 2 * B)

def embed (χ : Bool × Bool) : (twistCurve χ).toAffine.Point →+ PointGroup :=
  (PointScaling.pointCongr (K := K) curve_image_eq).toAddMonoidHom.comp
    (PointScaling.baseChangeUntwistHom (K := Base) (L := K) baseEmbedding A B (twistD χ) (twistRoot χ)
      (twistD_ne_zero χ) (twistRoot_sq χ))

theorem encode_embed (χ : Bool × Bool) (P : (twistCurve χ).toAffine.Point) :
    encode (embed χ P) = (encode P).map (fun xy =>
      (baseEmbedding xy.1 / baseEmbedding (twistD χ),
        baseEmbedding xy.2 / (baseEmbedding (twistD χ) * twistRoot χ))) := by
  unfold embed
  rw [AddMonoidHom.comp_apply]
  rw [AddEquiv.coe_toAddMonoidHom, PointScaling.encode_pointCongr,
    PointScaling.encode_baseChangeUntwistHom]

theorem embed_injective (χ : Bool × Bool) : Function.Injective (embed χ) := by
  intro P Q hPQ
  have hh := congrArg encode hPQ
  rw [encode_embed, encode_embed] at hh
  have hd : baseEmbedding (twistD χ) ≠ 0 :=
    (map_ne_zero baseEmbedding).mpr (twistD_ne_zero χ)
  have hdr := mul_ne_zero hd (twistRoot_ne_zero χ)
  apply encode_injective (twistCurve χ)
  cases P <;> cases Q <;> simp only [encode, Option.map_none, Option.map_some,
    Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at hh ⊢
  exact ⟨baseEmbedding.injective ((div_left_inj' hd).mp hh.1),
      baseEmbedding.injective ((div_left_inj' hdr).mp hh.2)⟩

private theorem encode_neg_point (P : PointGroup) :
    encode (-P) = (encode P).map (fun xy => (xy.1, -xy.2)) := by
  cases P with
  | zero => rfl
  | some x y h =>
    rw [WeierstrassCurve.Affine.Point.neg_some]
    simp [encode, WeierstrassCurve.Affine.negY, X, E]

/-- The joint sign-character subgroup, before tensoring with Q. -/
def characterSubgroup (χ : Bool × Bool) : AddSubgroup PointGroup where
  carrier := {P | pointSigmaU P = (if χ.1 then -P else P) ∧
    pointSigmaV P = (if χ.2 then -P else P)}
  zero_mem' := by simp
  add_mem' := by
    intro P Q hP hQ
    constructor
    · rw [map_add, hP.1, hQ.1]
      cases χ.1 <;> simp [add_comm]
    · rw [map_add, hP.2, hQ.2]
      cases χ.2 <;> simp [add_comm]
  neg_mem' := by
    intro P hP
    constructor
    · rw [map_neg, hP.1]
      cases χ.1 <;> simp
    · rw [map_neg, hP.2]
      cases χ.2 <;> simp

private theorem embed_sign (σ : K ≃ₐ[Base] K) (τ : PointGroup →+ PointGroup)
    (hτ : ∀ P, encode (τ P) = (encode P).map (fun xy => (σ xy.1, σ xy.2)))
    (χ : Bool × Bool) (ε : Bool)
    (hroot : σ (twistRoot χ) = if ε then -twistRoot χ else twistRoot χ)
    (P : (twistCurve χ).toAffine.Point) :
    τ (embed χ P) = if ε then -(embed χ P) else embed χ P := by
  apply encode_injective (X m)
  rw [hτ, encode_embed]
  cases ε
  · rw [ite_eq_right (by decide), encode_embed]
    cases P <;> simp [encode, baseEmbedding, map_div₀, map_mul, σ.commutes, hroot]
  · rw [ite_eq_left (by decide), encode_neg_point, encode_embed]
    cases P <;> simp [encode, baseEmbedding, map_div₀, map_mul, σ.commutes, hroot, mul_neg, div_neg]

theorem embed_mem_characterSubgroup (χ : Bool × Bool) (P : (twistCurve χ).toAffine.Point) :
    embed χ P ∈ characterSubgroup χ := by
  constructor
  · exact embed_sign sigmaU pointSigmaU.toAddMonoidHom encode_pointSigmaU χ χ.1 (sigmaU_twistRoot χ) P
  · exact embed_sign sigmaV pointSigmaV.toAddMonoidHom encode_pointSigmaV χ χ.2 (sigmaV_twistRoot χ) P

def characterEmbedding (χ : Bool × Bool) :
    (twistCurve χ).toAffine.Point →+ characterSubgroup χ :=
  (embed χ).codRestrict (characterSubgroup χ) (embed_mem_characterSubgroup χ)

theorem characterEmbedding_injective (χ : Bool × Bool) : Function.Injective (characterEmbedding χ) := by
  intro P Q hPQ
  exact embed_injective χ (congrArg Subtype.val hPQ)

private theorem point_sign_coordinates (σ : K ≃ₐ[Base] K) (τ : PointGroup →+ PointGroup)
    (hτ : ∀ P, encode (τ P) = (encode P).map (fun xy => (σ xy.1, σ xy.2)))
    (ε : Bool) (x y : K) (hN : (X m).toAffine.Nonsingular x y)
    (h : τ (.some x y hN) = if ε then -(.some x y hN) else .some x y hN) :
    σ x = x ∧ σ y = if ε then -y else y := by
  have he := congrArg encode h
  rw [hτ] at he
  cases ε
  · simpa only [Bool.false_eq_true, ite_false, encode, Option.map_some,
      Option.some.injEq, Prod.mk.injEq] using he
  · rw [ite_eq_left (by decide), encode_neg_point] at he
    simpa only [encode, Option.map_some, Option.some.injEq, Prod.mk.injEq, ite_true] using he

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

private theorem descend_nonsingular (χ : Bool × Bool) (x y : K)
    (hN : (X m).toAffine.Nonsingular x y) (x₀ y₀ : Base)
    (hx : baseEmbedding x₀ = baseEmbedding (twistD χ) * x)
    (hy : baseEmbedding y₀ = baseEmbedding (twistD χ) * twistRoot χ * y) :
    (twistCurve χ).toAffine.Nonsingular x₀ y₀ := by
  apply descend_nonsingular_general baseEmbedding A B (twistD χ) (twistRoot χ)
    (twistRoot_ne_zero χ) (twistRoot_sq χ) x y _ x₀ y₀ hx hy
  rw [curve_image_eq]
  exact hN

/-- Every point with the chosen two signs descends to the corresponding base
quadratic twist. Both finite coordinates are descended by the common fixed-field
criterion, and nonsingularity is preserved under the scaling. -/
theorem characterEmbedding_surjective (χ : Bool × Bool) :
    Function.Surjective (characterEmbedding χ) := by
  rintro ⟨P, hP⟩
  cases P with
  | zero =>
    refine ⟨0, ?_⟩
    apply Subtype.ext
    exact (embed χ).map_zero
  | some x y hN =>
    have hU := point_sign_coordinates sigmaU pointSigmaU.toAddMonoidHom
      encode_pointSigmaU χ.1 x y hN hP.1
    have hV := point_sign_coordinates sigmaV pointSigmaV.toAddMonoidHom
      encode_pointSigmaV χ.2 x y hN hP.2
    have hUx : sigmaU (baseEmbedding (twistD χ) * x) = baseEmbedding (twistD χ) * x := by
      rw [map_mul, sigmaU_base, hU.1]
    have hVx : sigmaV (baseEmbedding (twistD χ) * x) = baseEmbedding (twistD χ) * x := by
      rw [map_mul, sigmaV_base, hV.1]
    have hUy : sigmaU (baseEmbedding (twistD χ) * twistRoot χ * y) =
        baseEmbedding (twistD χ) * twistRoot χ * y := by
      rw [map_mul, map_mul, sigmaU_base, sigmaU_twistRoot, hU.2]
      cases χ.1 <;> simp
    have hVy : sigmaV (baseEmbedding (twistD χ) * twistRoot χ * y) =
        baseEmbedding (twistD χ) * twistRoot χ * y := by
      rw [map_mul, map_mul, sigmaV_base, sigmaV_twistRoot, hV.2]
      cases χ.2 <;> simp
    obtain ⟨x₀, hx⟩ := exists_base_of_fixed _ hUx hVx
    obtain ⟨y₀, hy⟩ := exists_base_of_fixed _ hUy hVy
    refine ⟨.some x₀ y₀ (descend_nonsingular χ x y hN x₀ y₀ hx hy), ?_⟩
    apply Subtype.ext
    apply encode_injective (X m)
    change encode (embed χ (.some x₀ y₀ _)) = _
    rw [encode_embed]
    have hd : baseEmbedding (twistD χ) ≠ 0 :=
      (map_ne_zero baseEmbedding).mpr (twistD_ne_zero χ)
    simp only [encode, Option.map_some, hx, hy, Option.some.injEq, Prod.mk.injEq]
    constructor <;> field_simp [hd, twistRoot_ne_zero χ]

/-- Additive equivalence from each base quadratic twist to its joint
sign-character subgroup in E(Q(C)). -/
def characterEquiv (χ : Bool × Bool) :
    (twistCurve χ).toAffine.Point ≃+ characterSubgroup χ :=
  AddEquiv.ofBijective (characterEmbedding χ)
    ⟨characterEmbedding_injective χ, characterEmbedding_surjective χ⟩

end
end Z2Z4Rank6.FunctionField.TwistCharacters
