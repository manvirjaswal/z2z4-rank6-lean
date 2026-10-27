module

public import Z2Z4Rank6.SecondW4Models
public import Z2Z4Rank6.ReductionTheory
public import Z2Z4Rank6.TwoDescent
public import Mathlib.GroupTheory.Coset.Card
public import Mathlib.Data.Fintype.EquivFin

@[expose] public section

/-!
# The exact torsion of the qA-twist at W=4

The good reductions at 7 and 13 have 8 and 12 points. Odd-prime torsion
integrality makes reduction injective on the rational torsion:
every nonzero torsion point has integral affine coordinates and hence
reduces to an affine point. The two displayed roots then give the whole
torsion subgroup, isomorphic to Z/2 times Z/2.
-/
namespace Z2Z4Rank6.SecondW4
noncomputable section
open SecondFamily Common.WeierstrassCoordinates

def primes : Fin 2 → ℕ := ![7, 13]
instance prime_fact (i : Fin 2) : Fact (primes i).Prime := by
  constructor
  fin_cases i <;> decide

def reductionCurve (i : Fin 2) : WeierstrassCurve (ZMod (primes i)) :=
  reducedModel (primes i) curveQA

instance reduction_elliptic (i : Fin 2) : (reductionCurve i).IsElliptic := by
  constructor
  fin_cases i <;>
    norm_num [reductionCurve, reducedModel, curveQA, integralQA, primes, residue,
      WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, WeierstrassCurve.b₈, isUnit_iff_ne_zero]
  all_goals decide +kernel

instance reduction_finite (i : Fin 2) : Finite (reductionCurve i).toAffine.Point :=
  Finite.of_equiv (Option (AffineSolutions (reductionCurve i).toAffine))
    (pointCoordinateEquiv (reductionCurve i).toAffine).symm

theorem reduction_card (i : Fin 2) :
    Nat.card (reductionCurve i).toAffine.Point = (![8, 12] : Fin 2 → ℕ) i := by
  have h : reductionCurve i =
      PointScaling.curve (residue (primes i) (8389527940732606 : ℚ))
        (residue (primes i) (3585469245239553794740817047809 : ℚ)) := by
    ext <;> simp [reductionCurve, reducedModel, curveQA, integralQA, PointScaling.curve]
  rw [h]
  have hE : (PointScaling.curve (residue (primes i) (8389527940732606 : ℚ))
      (residue (primes i) (3585469245239553794740817047809 : ℚ))).IsElliptic :=
    h ▸ reduction_elliptic i
  let : (longModel (residue (primes i) (8389527940732606 : ℚ))
      (residue (primes i) (3585469245239553794740817047809 : ℚ)) 0).IsElliptic := hE
  change Nat.card (longModel _ _ 0).Point = _
  rw [card_point_long_linear]
  · fin_cases i <;> decide +kernel
  · rw [ZMod.ringChar_zmod_n]
    fin_cases i <;> decide

private theorem integralAt_of_square {p : ℕ} [Fact p.Prime] (q : ℚ)
    (h : IntegralAt p (q^2)) : IntegralAt p q := by
  unfold IntegralAt at h ⊢
  rw [Rat.den_pow, Nat.cast_pow] at h
  intro hz
  apply h
  rw [hz]
  norm_num

private theorem integral_y {p : ℕ} [Fact p.Prime] (x y : ℚ)
    (h : curveQA.toAffine.Nonsingular x y) (hx : IntegralAt p x) : IntegralAt p y := by
  have he : y^2 = x^3 + 8389527940732606*x^2 + 3585469245239553794740817047809*x := by
    have he := h.1
    rw [WeierstrassCurve.Affine.equation_iff] at he
    simpa [curveQA, integralQA] using he
  apply integralAt_of_square
  rw [he]
  exact ((hx.pow 3).add ((integralAt_natCast _).mul (hx.pow 2))).add
    ((integralAt_natCast _).mul hx)

theorem integral_model_at (p : ℕ) [Fact p.Prime] : IntegralModelAt p curveQA := by
  simp [IntegralModelAt, curveQA, integralQA]
  exact ⟨integralAt_intCast (8389527940732606 : ℤ),
    integralAt_intCast (3585469245239553794740817047809 : ℤ)⟩

/-- A reduction homomorphism embeds the entire rational torsion
subgroup into either of the two displayed finite reduction groups. -/
theorem torsion_reduction_embedding (hOdd : OddPrimeTorsionIntegrality)
    (hReduction : GoodReductionHomomorphisms) (i : Fin 2) :
    ∃ f : AddCommGroup.torsion (RationalPoints curveQA) →+
      (reductionCurve i).toAffine.Point, Function.Injective f := by
  obtain ⟨red, hred⟩ := hReduction (primes i) curveQA inferInstance
    (integral_model_at _) (reduction_elliptic i)
  let f : AddCommGroup.torsion (RationalPoints curveQA) →+
      (reductionCurve i).toAffine.Point :=
    red.comp (AddCommGroup.torsion (RationalPoints curveQA)).subtype
  refine ⟨f, (injective_iff_map_eq_zero f).mpr ?_⟩
  intro T hzero
  apply Subtype.ext
  change T.val = 0
  cases hT : T.val with
  | zero => rfl
  | some x y h =>
    have ht : IsOfFinAddOrder (WeierstrassCurve.Affine.Point.some x y h) := hT ▸ T.property
    have hp2 : primes i ≠ 2 := by fin_cases i <;> decide
    have hxden := hOdd curveQA inferInstance ⟨integralQA, rfl⟩
      (primes i) (prime_fact i).out hp2 x y h ht
    have hx : IntegralAt (primes i) x := by
      intro hz
      exact hxden ((ZMod.natCast_eq_zero_iff _ _).mp hz)
    obtain ⟨hns, he⟩ := hred x y h hx (integral_y x y h hx)
    have hz : red (WeierstrassCurve.Affine.Point.some x y h) = 0 := by
      change red T.val = 0 at hzero
      simpa only [hT] using hzero
    rw [he] at hz
    exact (WeierstrassCurve.Affine.Point.some_ne_zero _ hz).elim

theorem torsion_card_dvd (hOdd : OddPrimeTorsionIntegrality)
    (hReduction : GoodReductionHomomorphisms) (i : Fin 2) :
    Nat.card (AddCommGroup.torsion (RationalPoints curveQA)) ∣ (![8, 12] : Fin 2 → ℕ) i := by
  obtain ⟨f, hf⟩ := torsion_reduction_embedding hOdd hReduction i
  simpa only [reduction_card] using AddSubgroup.card_dvd_of_injective f hf

theorem torsion_finite (hOdd : OddPrimeTorsionIntegrality)
    (hReduction : GoodReductionHomomorphisms) :
    Finite (AddCommGroup.torsion (RationalPoints curveQA)) := by
  obtain ⟨f, hf⟩ := torsion_reduction_embedding hOdd hReduction 0
  exact Finite.of_injective f hf

def e2 : ℚ := -881981589323167/156267624249
def e3 : ℚ := -451693636824103/1406408618241

theorem qA_split : twistedF (4 : ℚ) (qA 4) = splitWeierstrass 0 e2 e3 := by
  ext <;> norm_num [twistedF, qA, U, V, lambda, beta, e2, e3, splitWeierstrass]

def twoZero : (twistedF (4 : ℚ) (qA 4)).toAffine.Point :=
  .mk (x := 0) (y := 0) (by
    rw [twistedF_equation_iff]
    ring)

def twoRoot : (twistedF (4 : ℚ) (qA 4)).toAffine.Point :=
  .mk (x := e2) (y := 0) (by
    rw [twistedF_equation_iff]
    norm_num [e2, qA, U, V, lambda, beta])

theorem twoZero_double : (2 : ℕ) • twoZero = 0 := by
  rw [two_nsmul]
  apply WeierstrassCurve.Affine.Point.add_self_of_Y_eq
  norm_num [twoZero, WeierstrassCurve.Affine.negY, twistedF]

theorem twoRoot_double : (2 : ℕ) • twoRoot = 0 := by
  rw [two_nsmul]
  apply WeierstrassCurve.Affine.Point.add_self_of_Y_eq
  norm_num [twoRoot, WeierstrassCurve.Affine.negY, twistedF]

def orbit (P : (twistedF (4 : ℚ) (qA 4)).toAffine.Point) :
    ℤ →+ (twistedF (4 : ℚ) (qA 4)).toAffine.Point where
  toFun n := n • P
  map_zero' := zero_zsmul P
  map_add' n m := by simp only [add_zsmul]

def twoHom (P : (twistedF (4 : ℚ) (qA 4)).toAffine.Point)
    (h : (2 : ℕ) • P = 0) : ZMod 2 →+ (twistedF (4 : ℚ) (qA 4)).toAffine.Point :=
  ZMod.lift 2 ⟨orbit P, by change (2 : ℤ) • P = 0; simpa only [two_zsmul, two_nsmul] using h⟩

private theorem twoHom_val (P : (twistedF (4 : ℚ) (qA 4)).toAffine.Point)
    (h : (2 : ℕ) • P = 0) (z : ZMod 2) : twoHom P h z = z.val • P := by
  conv_lhs => rw [←ZMod.natCast_zmod_val z, ←Int.cast_natCast z.val]
  rw [twoHom, ZMod.lift_coe]
  simp only [orbit, AddMonoidHom.coe_mk, ZeroHom.coe_mk, natCast_zsmul]

def generators : (ZMod 2 × ZMod 2) →+ (twistedF (4 : ℚ) (qA 4)).toAffine.Point :=
  (twoHom twoZero twoZero_double).coprod (twoHom twoRoot twoRoot_double)

theorem generators_apply (z : ZMod 2 × ZMod 2) :
    generators z = z.1.val • twoZero + z.2.val • twoRoot := by
  simp only [generators, AddMonoidHom.coprod_apply, twoHom_val]

theorem generators_injective : Function.Injective generators := by
  apply (injective_iff_map_eq_zero generators).mpr
  rintro ⟨a, b⟩ h
  rw [generators_apply] at h
  have ha := ZMod.val_lt a
  have hb := ZMod.val_lt b
  have hT0 : twoZero ≠ 0 := WeierstrassCurve.Affine.Point.some_ne_zero _
  have hU0 : twoRoot ≠ 0 := WeierstrassCurve.Affine.Point.some_ne_zero _
  have hne : twoZero ≠ twoRoot := by
    intro he
    have hx := (WeierstrassCurve.Affine.Point.some.inj he).1
    norm_num [e2] at hx
  interval_cases hav : a.val <;> interval_cases hbv : b.val
  all_goals simp only [zero_nsmul, one_nsmul, zero_add, add_zero] at h
  · exact Prod.ext ((ZMod.val_eq_zero a).mp hav) ((ZMod.val_eq_zero b).mp hbv)
  · exact (hU0 h).elim
  · exact (hT0 h).elim
  · exfalso
    apply hne
    have hu : -twoRoot = twoRoot := neg_eq_iff_add_eq_zero.mpr (by
      simpa only [two_nsmul] using twoRoot_double)
    exact (eq_neg_of_add_eq_zero_left h).trans hu

def torsionGenerators : (ZMod 2 × ZMod 2) →+
    AddCommGroup.torsion (RationalPoints (twistedF (4 : ℚ) (qA 4))) :=
  generators.codRestrict _ (fun z => generators.isOfFinAddOrder (isOfFinAddOrder_of_finite z))

theorem torsionGenerators_injective : Function.Injective torsionGenerators := by
  intro x y h
  exact generators_injective (congrArg Subtype.val h)

def torsionScaling :
    AddCommGroup.torsion (RationalPoints (twistedF (4 : ℚ) (qA 4))) ≃+
      AddCommGroup.torsion (RationalPoints curveQA) :=
  (scaleQA.addSubgroupMap _).trans (AddEquiv.addSubgroupCongr scaleQA.map_torsion)

theorem qA_torsion_card (hOdd : OddPrimeTorsionIntegrality)
    (hReduction : GoodReductionHomomorphisms) :
    Nat.card (AddCommGroup.torsion (RationalPoints (twistedF (4 : ℚ) (qA 4)))) = 4 := by
  have hfin := torsion_finite hOdd hReduction
  let : Finite (AddCommGroup.torsion (RationalPoints curveQA)) := hfin
  let : Finite (AddCommGroup.torsion (RationalPoints (twistedF (4 : ℚ) (qA 4)))) :=
    Finite.of_equiv _ torsionScaling.symm.toEquiv
  have hlow : 4 ≤ Nat.card (AddCommGroup.torsion (RationalPoints (twistedF (4 : ℚ) (qA 4)))) := by
    simpa using Nat.card_le_card_of_injective torsionGenerators torsionGenerators_injective
  have hd : Nat.card (AddCommGroup.torsion (RationalPoints curveQA)) ∣ 4 := by
    have h7 := torsion_card_dvd hOdd hReduction 0
    have h13 := torsion_card_dvd hOdd hReduction 1
    simpa using Nat.dvd_gcd h7 h13
  have hu : Nat.card (AddCommGroup.torsion (RationalPoints curveQA)) ≤ 4 :=
    Nat.le_of_dvd (by decide) hd
  rw [←Nat.card_congr torsionScaling.toEquiv] at hu
  exact le_antisymm hu hlow

theorem torsionGenerators_surjective (hOdd : OddPrimeTorsionIntegrality)
    (hReduction : GoodReductionHomomorphisms) : Function.Surjective torsionGenerators := by
  let : Finite (AddCommGroup.torsion (RationalPoints curveQA)) := torsion_finite hOdd hReduction
  let : Finite (AddCommGroup.torsion (RationalPoints (twistedF (4 : ℚ) (qA 4)))) :=
    Finite.of_equiv _ torsionScaling.symm.toEquiv
  let := Fintype.ofFinite (AddCommGroup.torsion (RationalPoints (twistedF (4 : ℚ) (qA 4))))
  apply (Fintype.bijective_iff_injective_and_card torsionGenerators).mpr
    ⟨torsionGenerators_injective, ?_⟩ |>.2
  have hcard : Nat.card (ZMod 2 × ZMod 2) =
      Nat.card (AddCommGroup.torsion (RationalPoints (twistedF (4 : ℚ) (qA 4)))) := by
    rw [qA_torsion_card hOdd hReduction]
    norm_num [Nat.card_eq_fintype_card]
  simpa only [Nat.card_eq_fintype_card] using hcard

theorem qA_torsion_exact (hOdd : OddPrimeTorsionIntegrality)
    (hReduction : GoodReductionHomomorphisms) :
    Nonempty (AddCommGroup.torsion (RationalPoints (twistedF (4 : ℚ) (qA 4))) ≃+
      (ZMod 2 × ZMod 2)) :=
  ⟨(AddEquiv.ofBijective torsionGenerators
    ⟨torsionGenerators_injective, torsionGenerators_surjective hOdd hReduction⟩).symm⟩

theorem qA_torsion_generators (hOdd : OddPrimeTorsionIntegrality)
    (hReduction : GoodReductionHomomorphisms)
    (P : (twistedF (4 : ℚ) (qA 4)).toAffine.Point) (hP : IsOfFinAddOrder P) :
    ∃ z : ZMod 2 × ZMod 2, P = z.1.val • twoZero + z.2.val • twoRoot := by
  obtain ⟨z, hz⟩ := torsionGenerators_surjective hOdd hReduction ⟨P, hP⟩
  exact ⟨z, (congrArg Subtype.val hz).symm.trans (generators_apply z)⟩

end
end Z2Z4Rank6.SecondW4
