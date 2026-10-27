import Z2Z4Rank6.ExampleOriginalDescentDimensions
import Z2Z4Rank6.FirstExampleRankSixSelmerCertificate
import Z2Z4Rank6.SelmerClassSpace

/-! The two halves promised in the printed appendix and their eight
independent complete-descent classes, including the two torsion generators. -/
namespace Z2Z4Rank6.FirstExampleHalving
noncomputable section
open ExampleOriginalDescent Common.WeierstrassCoordinates
set_option maxHeartbeats 1000000
abbrev A := FirstExampleRankSix.A
abbrev B := FirstExampleRankSix.B
abbrev curve := FirstExampleRankSix.curve
def halfX : Fin 2 → ℚ := ![320476677033952803696640, 6311571167229441301188000]
def halfY : Fin 2 → ℚ := ![-13498832212411997744958189743292067840, -78302571738996050747172640026245988000]

theorem half_equation (i : Fin 2) : curve.toAffine.Equation (halfX i) (halfY i) := by
  rw [E_equation_iff]
  fin_cases i <;> norm_num [halfX,halfY,FirstExampleRankSix.A,FirstExampleRankSix.B]

def halves (i : Fin 2) : RationalPoints curve := .mk (half_equation i)

/-- The exact printed-type combination, with the original signed ordinates. -/
theorem half_doubles_1 : (2:ℕ) • halves 0=ExampleOriginalDescent.First.originalPoints 0+ExampleOriginalDescent.First.originalPoints 1+ExampleOriginalDescent.First.originalPoints 5+ExampleOriginalDescent.First.originalPoints 6 := by
  apply encode_injective
  simp only [two_nsmul,encode_add]
  norm_num [halves,halfX,halfY,ExampleOriginalDescent.First.originalPoints,
    ExampleOriginalDescent.First.points,ExampleOriginalDescent.First.two,
    ExampleOriginalDescent.First.four,twoLeft,fourPoint,
    WeierstrassCurve.Affine.Point.mk,encode,coordinateAdd,
    WeierstrassCurve.Affine.slope,WeierstrassCurve.Affine.addX,
    WeierstrassCurve.Affine.addY,WeierstrassCurve.Affine.negY,
    FirstExampleRankSix.curve,E,FirstExampleRankSix.A,FirstExampleRankSix.B,
    ReductionData.rationalX,ReductionData.rationalY]

/-- The exact printed-type combination, with the original signed ordinates. -/
theorem half_doubles_2 : (2:ℕ) • halves 1=ExampleOriginalDescent.First.originalPoints 0+ExampleOriginalDescent.First.originalPoints 3+ExampleOriginalDescent.First.originalPoints 4+ExampleOriginalDescent.First.originalPoints 7 := by
  apply encode_injective
  simp only [two_nsmul,encode_add]
  norm_num [halves,halfX,halfY,ExampleOriginalDescent.First.originalPoints,
    ExampleOriginalDescent.First.points,ExampleOriginalDescent.First.two,
    ExampleOriginalDescent.First.four,twoLeft,fourPoint,
    WeierstrassCurve.Affine.Point.mk,encode,coordinateAdd,
    WeierstrassCurve.Affine.slope,WeierstrassCurve.Affine.addX,
    WeierstrassCurve.Affine.addY,WeierstrassCurve.Affine.negY,
    FirstExampleRankSix.curve,E,FirstExampleRankSix.A,FirstExampleRankSix.B,
    ReductionData.rationalX,ReductionData.rationalY]

def replacementPoints : Fin 8 → RationalPoints curve :=
  ![halves 0,halves 1,ExampleOriginalDescent.First.points 2,
    ExampleOriginalDescent.First.points 3,ExampleOriginalDescent.First.points 4,
    ExampleOriginalDescent.First.points 5,ExampleOriginalDescent.First.two,
    ExampleOriginalDescent.First.four]
def representatives : Fin 8 → ℚ×ℚ := ![(477323690635, 12878492063915), (273117130, 2771341887966730), (-381706270, 842829802530), (-1786289230, 16794992410099170), (1045735167035, 202482486160788618915), (-65221078, 9962274814572294578442), (-1, 38435501818873593148184079), (74719418652274861322, 11399150415960147270378)]
def squareFactors : Fin 8 → ℚ×ℚ := ![(819392, 1967296), (152017740, 141940), (228582592, 5924032), ((212242775216:ℚ)/2399, (110358256:ℚ)/2399), ((80665707584:ℚ)/2467, (5924032:ℚ)/2467), ((1857124283140:ℚ)/2521, (94940:ℚ)/2521), (7037226227200, (1:ℚ)/7037226227200), (560, 80)]
def rawValues : Fin 8 → ℚ×ℚ :=
  ![(halfX 0,halfX 0+A^2),(halfX 1,halfX 1+A^2),
    (ReductionData.rationalX 2,ReductionData.rationalX 2+A^2),
    (ReductionData.rationalX 3,ReductionData.rationalX 3+A^2),
    (ReductionData.rationalX 4,ReductionData.rationalX 4+A^2),
    (ReductionData.rationalX 5,ReductionData.rationalX 5+A^2),
    (-A^2,(A^2-B^2)/A^2),(A*B,A*B+A^2)]

def classes (i : Fin 8) : ClassPair := pairClass (representatives i)

theorem square_factors (i : Fin 8) :
    (rawValues i).1=(representatives i).1*(squareFactors i).1^2 ∧
    (rawValues i).2=(representatives i).2*(squareFactors i).2^2 := by
  fin_cases i <;> norm_num [rawValues,representatives,squareFactors,halfX,
    ReductionData.rationalX,FirstExampleRankSix.A,FirstExampleRankSix.B]

theorem raw_classes (i : Fin 8) : pairClass (rawValues i)=classes i := by
  apply pairClass_factor _ _ (squareFactors i)
  · fin_cases i <;> norm_num [rawValues,halfX,ReductionData.rationalX,
      FirstExampleRankSix.A,FirstExampleRankSix.B]
  · fin_cases i <;> norm_num [representatives]
  · fin_cases i <;> norm_num [squareFactors]
  · exact square_factors i

theorem descent_coordinates (i : Fin 8) :
    completeDescentCoordinates curve 0 (-(A^2)) (-(B^2)) (replacementPoints i)=classes i := by
  rw [←raw_classes i]
  fin_cases i <;> norm_num [replacementPoints,halves,halfX,halfY,
    ExampleOriginalDescent.First.points,ExampleOriginalDescent.First.two,
    ExampleOriginalDescent.First.four,twoLeft,fourPoint,
    WeierstrassCurve.Affine.Point.mk,completeDescentCoordinates,rawValues,pairClass,
    ReductionData.rationalX,ReductionData.rationalY,FirstExampleRankSix.A,FirstExampleRankSix.B]

private theorem valuation_nat_zero_or_one {p n : ℕ} [Fact p.Prime]
    (hn : n≠0) (hp2 : ¬p^2∣n) : padicValNat p n=if p∣n then 1 else 0 := by
  split_ifs with hdiv
  · have hlo : 1≤padicValNat p n := by
      apply (padicValNat_dvd_iff_le hn).mp
      simpa only [pow_one] using hdiv
    have hhi : ¬2≤padicValNat p n := fun h => hp2 ((padicValNat_dvd_iff_le hn).mpr h)
    omega
  · exact padicValNat.eq_zero_of_not_dvd hdiv
local instance prime2 : Fact (Nat.Prime 2) := ⟨by norm_num⟩
local instance prime5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩
local instance prime11 : Fact (Nat.Prime 11) := ⟨by norm_num⟩
local instance prime13 : Fact (Nat.Prime 13) := ⟨by norm_num⟩
local instance prime17 : Fact (Nat.Prime 17) := ⟨by norm_num⟩
local instance prime31 : Fact (Nat.Prime 31) := ⟨by norm_num⟩
local instance prime193 : Fact (Nat.Prime 193) := ⟨by norm_num⟩

def classesParity : ClassPair →+ (Fin 8 → ZMod 2) where
  toFun q := ![squareClassSign q.1, squareClassValuation 2 q.1, squareClassValuation 5 q.1, squareClassValuation 11 q.1, squareClassValuation 13 q.1, squareClassValuation 17 q.1, squareClassValuation 31 q.1, squareClassValuation 193 q.2]
  map_zero' := by ext i; fin_cases i <;> simp
  map_add' q r := by ext i; fin_cases i <;> simp

def classesParityVectors : Fin 8 → Fin 8 → ZMod 2 :=
  ![![0, 0, 1, 1, 0, 1, 0, 1], ![0, 1, 1, 1, 1, 0, 1, 1], ![1, 1, 1, 1, 0, 1, 0, 0], ![1, 1, 1, 1, 0, 0, 0, 1], ![0, 0, 1, 0, 1, 1, 1, 1], ![1, 1, 0, 0, 1, 1, 0, 1], ![1, 0, 0, 0, 0, 0, 0, 1], ![0, 1, 0, 1, 1, 1, 1, 0]]

theorem classes_parity_values (i : Fin 8) :
    classesParity (classes i)=classesParityVectors i := by
  ext j
  fin_cases i <;> fin_cases j <;>
    simp only [classesParity,classes,pairClass,representatives,classesParityVectors,
      AddMonoidHom.coe_mk,ZeroHom.coe_mk]
  all_goals simp (disch := norm_num) only [squareClassValuation_apply,squareClassSign_apply]
  all_goals norm_num [padicValRat_def,padicValInt]
  all_goals try rw [valuation_nat_zero_or_one (by decide) (by decide)]
  all_goals norm_num

theorem classes_independent : LinearIndependent (ZMod 2) classes := by
  apply Fintype.linearIndependent_iff.mpr
  intro n hn
  have hm : ∑ i,n i • classesParityVectors i=0 := by
    have hh := congrArg classesParity hn
    simpa only [map_sum,ZMod.map_smul,classes_parity_values,map_zero] using hh
  have h0:=congrFun hm 0
  have h1:=congrFun hm 1
  have h2:=congrFun hm 2
  have h3:=congrFun hm 3
  have h4:=congrFun hm 4
  have h5:=congrFun hm 5
  have h6:=congrFun hm 6
  have h7:=congrFun hm 7
  norm_num [Fin.sum_univ_succ,classesParityVectors] at h0 h1 h2 h3 h4 h5 h6 h7
  have hC2 : (2 : ZMod 2)=0 := by decide
  have hC4 : (4 : ZMod 2)=0 := by decide
  have hC6 : (6 : ZMod 2)=0 := by decide
  have hC8 : (8 : ZMod 2)=0 := by decide
  intro i
  fin_cases i
  · change n 0=0
    linear_combination (norm := skip) h1+h3+h4+h6
    ring_nf
    repeat' first
      | rw [hC2]
      | rw [hC4]
      | rw [hC6]
      | rw [hC8]
      | rw [mul_zero]
      | rw [sub_zero]
      | rw [zero_sub]
      | rw [neg_zero]
  · change n 1=0
    linear_combination (norm := skip) h2+h3+h6
    ring_nf
    repeat' first
      | rw [hC2]
      | rw [hC4]
      | rw [hC6]
      | rw [hC8]
      | rw [mul_zero]
      | rw [sub_zero]
      | rw [zero_sub]
      | rw [neg_zero]
  · change n 2=0
    linear_combination (norm := skip) h1+h2+h5
    ring_nf
    repeat' first
      | rw [hC2]
      | rw [hC4]
      | rw [hC6]
      | rw [hC8]
      | rw [mul_zero]
      | rw [sub_zero]
      | rw [zero_sub]
      | rw [neg_zero]
  · change n 3=0
    linear_combination (norm := skip) h0+h2+h7
    ring_nf
    repeat' first
      | rw [hC2]
      | rw [hC4]
      | rw [hC6]
      | rw [hC8]
      | rw [mul_zero]
      | rw [sub_zero]
      | rw [zero_sub]
      | rw [neg_zero]
  · change n 4=0
    linear_combination (norm := skip) h0+h4+h5+h7
    ring_nf
    repeat' first
      | rw [hC2]
      | rw [hC4]
      | rw [hC6]
      | rw [hC8]
      | rw [mul_zero]
      | rw [sub_zero]
      | rw [zero_sub]
      | rw [neg_zero]
  · change n 5=0
    linear_combination (norm := skip) h4+h6
    ring_nf
    repeat' first
      | rw [hC2]
      | rw [hC4]
      | rw [hC6]
      | rw [hC8]
      | rw [mul_zero]
      | rw [sub_zero]
      | rw [zero_sub]
      | rw [neg_zero]
  · change n 6=0
    linear_combination (norm := skip) h1+h4+h5+h6+h7
    ring_nf
    repeat' first
      | rw [hC2]
      | rw [hC4]
      | rw [hC6]
      | rw [hC8]
      | rw [mul_zero]
      | rw [sub_zero]
      | rw [zero_sub]
      | rw [neg_zero]
  · change n 7=0
    linear_combination (norm := skip) h0+h2+h3+h4+h5+h7
    ring_nf
    repeat' first
      | rw [hC2]
      | rw [hC4]
      | rw [hC6]
      | rw [hC8]
      | rw [mul_zero]
      | rw [sub_zero]
      | rw [zero_sub]
      | rw [neg_zero]

def replacementSpan : Submodule (ZMod 2) ClassPair :=
  Submodule.span (ZMod 2) (Set.range classes)

def replacementBasis : Module.Basis (Fin 8) (ZMod 2) replacementSpan :=
  Module.Basis.span classes_independent

theorem replacementBasis_coordinates (i : Fin 8) :
    (replacementBasis i : ClassPair)=completeDescentCoordinates curve
      0 (-(A^2)) (-(B^2)) (replacementPoints i) := by
  rw [descent_coordinates]
  exact Module.Basis.coe_span_apply classes_independent i

theorem replacementSpan_finrank : Module.finrank (ZMod 2) replacementSpan=8 := by
  unfold replacementSpan
  convert finrank_span_eq_card classes_independent using 1
  simp only [Fintype.card_fin]

/-- Two rational halves replace the first two original points. The
resulting six points and the original two torsion points give eight independent
classes. -/
theorem printed_halving_and_eight_classes :
    (2:ℕ) • halves 0=ExampleOriginalDescent.First.points 0+
      ExampleOriginalDescent.First.points 1+ExampleOriginalDescent.First.points 5+
      ExampleOriginalDescent.First.two ∧
    (2:ℕ) • halves 1=ExampleOriginalDescent.First.points 0+
      ExampleOriginalDescent.First.points 3+ExampleOriginalDescent.First.points 4+
      ExampleOriginalDescent.First.four ∧
    LinearIndependent (ZMod 2) (fun i => completeDescentCoordinates curve
      0 (-(A^2)) (-(B^2)) (replacementPoints i)) ∧
    Module.finrank (ZMod 2) replacementSpan=8 := by
  refine ⟨half_doubles_1,half_doubles_2,?_,replacementSpan_finrank⟩
  have he : (fun i => completeDescentCoordinates curve 0 (-(A^2)) (-(B^2))
    (replacementPoints i))=classes := funext descent_coordinates
  rw [he]
  exact classes_independent

end
end Z2Z4Rank6.FirstExampleHalving
