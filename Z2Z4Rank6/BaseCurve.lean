import Z2Z4Rank6.Quartic
import Z2Z4Rank6.BaseCurveArithmetic
import Mathlib.Tactic

/-!
# Rational maps for the base curve C

Explicit quartic parametrization from Lemma 4.1 of M. Jaswal,
*Infinitely many elliptic curves with torsion Z/2Z × Z/4Z and rank at least six*,
DOI 10.5281/zenodo.23437117.
-/

namespace Z2Z4Rank6

theorem rational_fifteen_nonsquare : ¬ IsSquare (15 : ℚ) := by norm_num

theorem rational_ten_nonsquare : ¬ IsSquare (10 : ℚ) := by norm_num

theorem rational_conic_denom (k : ℚ) : k^2 - 15 ≠ 0 := by
  intro h
  apply rational_fifteen_nonsquare
  exact ⟨k, by nlinarith⟩

/-- The printed point `(1,35,35)` on C. -/
def baseOrigin : CPoint where
  m := 1
  u := 35
  v := 35
  u_sq := by norm_num
  v_sq := by norm_num

/-- Rational affine points of the printed quartic `eta²=g(k)`. -/
@[ext]
structure QuarticPoint where
  k : ℚ
  eta : ℚ
  equation : eta^2 = quartic k

def quarticToC (P : QuarticPoint) : CPoint where
  m := conicM P.k
  u := conicU P.k
  v := conicV P.k P.eta
  u_sq := conic_identity P.k (rational_conic_denom P.k)
  v_sq := quartic_to_second_conic P.k P.eta (rational_conic_denom P.k) P.equation

theorem conicM_eq_one_iff (k : ℚ) : conicM k = 1 ↔ k = 3/7 := by
  unfold conicM
  rw [div_eq_one_iff_eq (rational_conic_denom k)]
  constructor <;> intro h <;> nlinarith

theorem conic_coordinates_injective :
    Function.Injective (fun k : ℚ => (conicM k, conicU k)) := by
  intro k l h
  have hm : conicM k = conicM l := congrArg Prod.fst h
  have hu : conicU k = conicU l := congrArg Prod.snd h
  by_cases hk : conicM k = 1
  · have hl : conicM l = 1 := hm ▸ hk
    rw [conicM_eq_one_iff] at hk hl
    exact hk.trans hl.symm
  · have hkl : k*(conicM k - 1) = l*(conicM k - 1) := by
      rw [conic_line k (rational_conic_denom k),
        conic_line l (rational_conic_denom l), ← hm] at hu
      linarith
    exact mul_right_cancel₀ (sub_ne_zero.mpr hk) hkl

theorem quarticToC_injective : Function.Injective quarticToC := by
  intro P Q h
  have hk : P.k = Q.k := conic_coordinates_injective
    (congrArg (fun c : CPoint => (c.m,c.u)) h)
  have hv : conicV P.k P.eta = conicV Q.k Q.eta := congrArg CPoint.v h
  have he : P.eta = Q.eta := by
    rw [← hk] at hv
    unfold conicV at hv
    exact (mul_left_cancel₀ (by norm_num : (5 : ℚ) ≠ 0)
      ((div_left_inj' (rational_conic_denom P.k)).mp hv))
  exact QuarticPoint.ext hk he

/-- A rational projective solution with homogenizing coordinate zero has no
nonzero coordinates. This is the paper's no-rational-points-at-infinity check. -/
theorem projective_infinity_trivial (m u v : ℚ)
    (hu : u^2 = 15*m^2) (hv : v^2 = 10*m^2) : m = 0 ∧ u = 0 ∧ v = 0 := by
  have hm : m = 0 := by
    by_contra hm
    apply rational_fifteen_nonsquare
    refine ⟨u/m, ?_⟩
    field_simp
    nlinarith
  constructor
  · exact hm
  · constructor <;> nlinarith [sq_nonneg u, sq_nonneg v]

def quarticToEC (P : QuarticPoint) : RationalPoints EC :=
  .mk ((ec_equation_iff _ _).mpr (quartic_to_ec_equation P.k P.eta P.equation))

/-- The affine chart on E_C where the inverse quartic map is regular. -/
def ecQuarticChart : RationalPoints EC → Prop
  | .zero => False
  | .some x _ _ => x + 82 ≠ 0

def ECQuarticChart := {P : RationalPoints EC // ecQuarticChart P}

def ecToQuartic (P : ECQuarticChart) : QuarticPoint := by
  rcases P with ⟨P,hP⟩
  cases P with
  | zero => exact False.elim hP
  | some x y h =>
    exact ⟨ecToK x y, ecToEta x y,
      ec_to_quartic_equation x y hP ((ec_equation_iff x y).mp h.1)⟩

theorem ecToQuartic_inverse (P : ECQuarticChart) :
    quarticToEC (ecToQuartic P) = P.val := by
  rcases P with ⟨P,hP⟩
  cases P with
  | zero => exact False.elim hP
  | some x y h =>
    simp only [ecToQuartic, quarticToEC, WeierstrassCurve.Affine.Point.mk]
    congr 1
    · exact ec_quartic_x_inverse x y
    · exact ec_quartic_y_inverse x y hP

theorem ecToQuartic_injective : Function.Injective ecToQuartic := by
  intro P Q h
  apply Subtype.ext
  simpa only [ecToQuartic_inverse] using congrArg quarticToEC h

def ecBadPlus : RationalPoints EC :=
  .mk ((ec_equation_iff (-82) 486).mpr (by norm_num))

def ecBadMinus : RationalPoints EC :=
  .mk ((ec_equation_iff (-82) (-486)).mpr (by norm_num))

theorem ecQuarticChart_complement_finite : {P | ¬ ecQuarticChart P}.Finite := by
  apply (Set.toFinite ({0, ecBadPlus, ecBadMinus} : Set (RationalPoints EC))).subset
  intro P hP
  cases P with
  | zero =>
    change (0 : RationalPoints EC) ∈ ({0, ecBadPlus, ecBadMinus} : Set (RationalPoints EC))
    simp
  | some x y h =>
    have hx : x = -82 := by
      change ¬ (x+82 ≠ 0) at hP
      have hx0 : x+82 = 0 := not_ne_iff.mp hP
      linarith
    have he := (ec_equation_iff x y).mp h.1
    have hy : y = 486 ∨ y = -486 := by
      rw [hx] at he
      norm_num at he
      have hf : (y-486)*(y+486) = 0 := by nlinarith
      rcases mul_eq_zero.mp hf with h | h
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
    rcases hy with hy | hy <;> subst x <;> subst y <;>
      simp [ecBadPlus, ecBadMinus, WeierstrassCurve.Affine.Point.mk]

theorem infinite_ECQuarticChart [Infinite (RationalPoints EC)] : Infinite ECQuarticChart := by
  have hinf : {P : RationalPoints EC | ecQuarticChart P}.Infinite := by
    exact Set.infinite_of_finite_compl ecQuarticChart_complement_finite
  exact hinf.to_subtype

theorem infinite_CPoint_of_infinite_EC [Infinite (RationalPoints EC)] : Infinite CPoint := by
  have := infinite_ECQuarticChart
  exact Infinite.of_injective (fun P : ECQuarticChart => quarticToC (ecToQuartic P))
    (quarticToC_injective.comp ecToQuartic_injective)

theorem infinite_CPoint (hSilvermanVII34 : OddPrimeTorsionIntegrality) : Infinite CPoint := by
  have := ec_infinite hSilvermanVII34
  exact infinite_CPoint_of_infinite_EC

def baseC0 : CPoint where
  m := 7401/2399
  u := 88235/2399
  v := 86835/2399
  u_sq := by norm_num
  v_sq := by norm_num

def quarticC0 : QuarticPoint where
  k := 35/41
  eta := -173670/1681
  equation := by norm_num [quartic]

theorem quarticC0_to_C : quarticToC quarticC0 = baseC0 := by
  ext <;> norm_num [quarticToC, quarticC0, baseC0, conicM, conicU, conicV]

def ecC0 : RationalPoints EC :=
  .mk ((ec_equation_iff (-526480/1681) (96843600/68921)).mpr (by norm_num))

theorem quarticC0_to_EC : quarticToEC quarticC0 = ecC0 := by
  simp only [quarticToEC, ecC0, WeierstrassCurve.Affine.Point.mk]
  congr 1 <;> norm_num [quarticX, quarticY, quarticC0]

theorem ecC0_in_chart : ecQuarticChart ecC0 := by
  norm_num [ecQuarticChart, ecC0, WeierstrassCurve.Affine.Point.mk]

end Z2Z4Rank6
