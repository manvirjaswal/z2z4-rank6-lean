module

public import Z2Z4Rank6.FirstExampleRankSixLower
public import Z2Z4Rank6.SecondExampleRankSevenParity

@[expose] public section

/-! Exact complete-descent dimensions of the six original printed points,
with the two printed torsion generators. -/
namespace Z2Z4Rank6.ExampleOriginalDescent
noncomputable section
open Common.WeierstrassCoordinates
abbrev ClassPair := RatSquareClassAdd × RatSquareClassAdd

def pairClass (q : ℚ×ℚ) : ClassPair := (squareClass q.1,squareClass q.2)

theorem pairClass_factor (q r s : ℚ×ℚ)
    (hq : q.1≠0 ∧ q.2≠0) (hr : r.1≠0 ∧ r.2≠0) (hs : s.1≠0 ∧ s.2≠0)
    (h : q.1=r.1*s.1^2 ∧ q.2=r.2*s.2^2) : pairClass q=pairClass r := by
  exact Prod.ext (squareClass_eq_of_factor _ _ _ hq.1 hr.1 hs.1 h.1)
    (squareClass_eq_of_factor _ _ _ hq.2 hr.2 hs.2 h.2)

theorem pairClass_mul (q r : ℚ×ℚ) (hq : q.1≠0 ∧ q.2≠0)
    (hr : r.1≠0 ∧ r.2≠0) :
    pairClass (q.1*r.1,q.2*r.2)=pairClass q+pairClass r := by
  exact Prod.ext (squareClass_mul _ _ hq.1 hr.1) (squareClass_mul _ _ hq.2 hr.2)

theorem pairClass_mul_three (q r s : ℚ×ℚ) (hq : q.1≠0 ∧ q.2≠0)
    (hr : r.1≠0 ∧ r.2≠0) (hs : s.1≠0 ∧ s.2≠0) :
    pairClass (q.1*r.1*s.1,q.2*r.2*s.2)=pairClass q+pairClass r+pairClass s := by
  have hh := pairClass_mul (q.1*r.1,q.2*r.2) s
    ⟨mul_ne_zero hq.1 hr.1,mul_ne_zero hq.2 hr.2⟩ hs
  rw [pairClass_mul q r hq hr] at hh
  exact hh

private theorem valuation_nat_zero_or_one {p n : ℕ} [Fact p.Prime]
    (hn : n≠0) (hp2 : ¬p^2∣n) : padicValNat p n=if p∣n then 1 else 0 := by
  split_ifs with hdiv
  · have hlo : 1≤padicValNat p n := by
      apply (padicValNat_dvd_iff_le hn).mp
      simpa only [pow_one] using hdiv
    have hhi : ¬2≤padicValNat p n := fun h => hp2 ((padicValNat_dvd_iff_le hn).mpr h)
    omega
  · exact padicValNat.eq_zero_of_not_dvd hdiv

namespace First
abbrev A := FirstExampleRankSix.A
abbrev B := FirstExampleRankSix.B
abbrev curve := FirstExampleRankSix.curve
theorem point_equation (i : Fin 6) : curve.toAffine.Equation
    (ReductionData.rationalX i) (ReductionData.rationalY i) := by
  rw [E_equation_iff]
  fin_cases i <;> norm_num [ReductionData.rationalX,ReductionData.rationalY,FirstExampleRankSix.A,FirstExampleRankSix.B]

def points (i : Fin 6) : RationalPoints curve := .mk (point_equation i)
def two : RationalPoints curve := twoLeft A B FirstExampleRankSix.factor_nonzero
def four : RationalPoints curve := fourPoint A B FirstExampleRankSix.factor_nonzero

def originalPoints : Fin 8 → RationalPoints curve :=
  ![points 0,points 1,points 2,points 3,points 4,points 5,two,four]

theorem points_eq_printed (i : Fin 6) : points i=FirstExampleRankSix.points i := by
  apply encode_injective
  exact (FirstExampleRankSix.points_coordinates i).symm

def representatives : Fin 8 → ℚ×ℚ := ![(-1, 10366948611111), (-65221078, 2687057178), (-381706270, 842829802530), (-1786289230, 16794992410099170), (1045735167035, 202482486160788618915), (-65221078, 9962274814572294578442), (-1, 38435501818873593148184079), (74719418652274861322, 11399150415960147270378)]
def squareFactors : Fin 8 → ℚ×ℚ := ![((95572918041664:ℚ)/25, (45875008:ℚ)/25), (559393450, 104089950), (228582592, 5924032), ((212242775216:ℚ)/2399, (110358256:ℚ)/2399), ((80665707584:ℚ)/2467, (5924032:ℚ)/2467), ((1857124283140:ℚ)/2521, (94940:ℚ)/2521), (7037226227200, (1:ℚ)/7037226227200), (560, 80)]
def rawValues : Fin 8 → ℚ×ℚ :=
  ![(ReductionData.rationalX 0,ReductionData.rationalX 0+A^2),
    (ReductionData.rationalX 1,ReductionData.rationalX 1+A^2),
    (ReductionData.rationalX 2,ReductionData.rationalX 2+A^2),
    (ReductionData.rationalX 3,ReductionData.rationalX 3+A^2),
    (ReductionData.rationalX 4,ReductionData.rationalX 4+A^2),
    (ReductionData.rationalX 5,ReductionData.rationalX 5+A^2),
    (-A^2,(A^2-B^2)/A^2),(A*B,A*B+A^2)]

def classes (i : Fin 8) : ClassPair := pairClass (representatives i)

theorem square_factors (i : Fin 8) :
    (rawValues i).1=(representatives i).1*(squareFactors i).1^2 ∧
    (rawValues i).2=(representatives i).2*(squareFactors i).2^2 := by
  fin_cases i <;> norm_num [rawValues,representatives,squareFactors,
    ReductionData.rationalX,FirstExampleRankSix.A,FirstExampleRankSix.B]

theorem raw_classes (i : Fin 8) : pairClass (rawValues i)=classes i := by
  apply pairClass_factor _ _ (squareFactors i)
  · fin_cases i <;> norm_num [rawValues,ReductionData.rationalX,FirstExampleRankSix.A,FirstExampleRankSix.B]
  · fin_cases i <;> norm_num [representatives]
  · fin_cases i <;> norm_num [squareFactors]
  · exact square_factors i

theorem descent_coordinates (i : Fin 8) :
    completeDescentCoordinates curve 0 (-(A^2)) (-(B^2)) (originalPoints i)=classes i := by
  rw [←raw_classes i]
  fin_cases i <;> norm_num [originalPoints,points,two,four,twoLeft,fourPoint,
    WeierstrassCurve.Affine.Point.mk,completeDescentCoordinates,rawValues,pairClass,
    ReductionData.rationalX,ReductionData.rationalY,FirstExampleRankSix.A,FirstExampleRankSix.B]

def basisIndices : Fin 6 → Fin 8 := ![0, 1, 2, 3, 4, 5]
def basis (i : Fin 6) : ClassPair := classes (basisIndices i)
local instance prime2 : Fact (Nat.Prime 2) := ⟨by norm_num⟩
local instance prime5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩
local instance prime11 : Fact (Nat.Prime 11) := ⟨by norm_num⟩
local instance prime17 : Fact (Nat.Prime 17) := ⟨by norm_num⟩
local instance prime193 : Fact (Nat.Prime 193) := ⟨by norm_num⟩

def basisParity : ClassPair →+ (Fin 6 → ZMod 2) where
  toFun q := ![squareClassSign q.1, squareClassValuation 2 q.1, squareClassValuation 5 q.1, squareClassValuation 11 q.1, squareClassValuation 17 q.1, squareClassValuation 193 q.2]
  map_zero' := by ext i; fin_cases i <;> simp
  map_add' q r := by ext i; fin_cases i <;> simp

def basisParityVectors : Fin 6 → Fin 6 → ZMod 2 :=
  ![![1, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 1, 0], ![1, 1, 1, 1, 1, 0], ![1, 1, 1, 1, 0, 1], ![0, 0, 1, 0, 1, 1], ![1, 1, 0, 0, 1, 1]]

theorem basis_parity_values (i : Fin 6) :
    basisParity (basis i)=basisParityVectors i := by
  ext j
  fin_cases i <;> fin_cases j <;>
    simp only [basisParity,basis,basisIndices,classes,pairClass,representatives,basisParityVectors,
      AddMonoidHom.coe_mk,ZeroHom.coe_mk]
  all_goals simp (disch := norm_num) only [squareClassValuation_apply,squareClassSign_apply]
  all_goals norm_num [padicValRat_def,padicValInt]
  all_goals try rw [valuation_nat_zero_or_one (by decide) (by decide)]
  all_goals norm_num

theorem basis_independent : LinearIndependent (ZMod 2) basis := by
  apply Fintype.linearIndependent_iff.mpr
  intro n hn
  have hm : ∑ i,n i • basisParityVectors i=0 := by
    have hh := congrArg basisParity hn
    simpa only [map_sum,ZMod.map_smul,basis_parity_values,map_zero] using hh
  have h0:=congrFun hm 0
  have h1:=congrFun hm 1
  have h2:=congrFun hm 2
  have h3:=congrFun hm 3
  have h4:=congrFun hm 4
  have h5:=congrFun hm 5
  norm_num [Fin.sum_univ_succ,basisParityVectors] at h0 h1 h2 h3 h4 h5
  have hC2 : (2 : ZMod 2)=0 := by decide
  have hC4 : (4 : ZMod 2)=0 := by decide
  have hC6 : (6 : ZMod 2)=0 := by decide
  intro i
  fin_cases i
  · change n 0=0
    linear_combination (norm := skip) h0+h1
    ring_nf
    repeat' first
      | rw [hC2]
      | rw [hC4]
      | rw [hC6]
      | rw [mul_zero]
      | rw [sub_zero]
      | rw [zero_sub]
      | rw [neg_zero]
  · change n 1=0
    linear_combination (norm := skip) h3+h4+h5
    ring_nf
    repeat' first
      | rw [hC2]
      | rw [hC4]
      | rw [hC6]
      | rw [mul_zero]
      | rw [sub_zero]
      | rw [zero_sub]
      | rw [neg_zero]
  · change n 2=0
    linear_combination (norm := skip) h1+h2+h4
    ring_nf
    repeat' first
      | rw [hC2]
      | rw [hC4]
      | rw [hC6]
      | rw [mul_zero]
      | rw [sub_zero]
      | rw [zero_sub]
      | rw [neg_zero]
  · change n 3=0
    linear_combination (norm := skip) h1+h2+h3+h4
    ring_nf
    repeat' first
      | rw [hC2]
      | rw [hC4]
      | rw [hC6]
      | rw [mul_zero]
      | rw [sub_zero]
      | rw [zero_sub]
      | rw [neg_zero]
  · change n 4=0
    linear_combination (norm := skip) h2+h3
    ring_nf
    repeat' first
      | rw [hC2]
      | rw [hC4]
      | rw [hC6]
      | rw [mul_zero]
      | rw [sub_zero]
      | rw [zero_sub]
      | rw [neg_zero]
  · change n 5=0
    linear_combination (norm := skip) h1+h4+h5
    ring_nf
    repeat' first
      | rw [hC2]
      | rw [hC4]
      | rw [hC6]
      | rw [mul_zero]
      | rw [sub_zero]
      | rw [zero_sub]
      | rw [neg_zero]

theorem class_relation_6 : classes 6=classes 0+classes 1+classes 5 := by
  calc
    _=pairClass (-4253789015482084, 277514942009740053456226683350541270254427036) := by
      apply pairClass_factor _ _ ((1:ℚ)/65221078, (1:ℚ)/2687057178) <;> norm_num [classes,representatives]
    _=_ := by
      have hh := pairClass_mul_three (representatives 0) (representatives 1) (representatives 5) (by norm_num [representatives]) (by norm_num [representatives]) (by norm_num [representatives])
      norm_num [representatives,classes] at hh ⊢
      exact hh

theorem class_relation_7 : classes 7=classes 0+classes 3+classes 4 := by
  calc
    _=pairClass (1867985466306871533050, 35254797322007362661668160038346351081783681911050) := by
      apply pairClass_factor _ _ ((1:ℚ)/5, (1:ℚ)/55612557649335) <;> norm_num [classes,representatives]
    _=_ := by
      have hh := pairClass_mul_three (representatives 0) (representatives 3) (representatives 4) (by norm_num [representatives]) (by norm_num [representatives]) (by norm_num [representatives])
      norm_num [representatives,classes] at hh ⊢
      exact hh

def originalSpan : Submodule (ZMod 2) ClassPair := Submodule.span (ZMod 2) (Set.range classes)
def basisSpan : Submodule (ZMod 2) ClassPair := Submodule.span (ZMod 2) (Set.range basis)

private theorem basis_mem (i : Fin 6) : basis i∈basisSpan := Submodule.subset_span ⟨i,rfl⟩

theorem originalSpan_eq_basisSpan : originalSpan=basisSpan := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    fin_cases i
    · simpa [basis,basisIndices] using basis_mem 0
    · simpa [basis,basisIndices] using basis_mem 1
    · simpa [basis,basisIndices] using basis_mem 2
    · simpa [basis,basisIndices] using basis_mem 3
    · simpa [basis,basisIndices] using basis_mem 4
    · simpa [basis,basisIndices] using basis_mem 5
    · change classes 6∈basisSpan
      rw [class_relation_6]
      simpa [basis,basisIndices] using Submodule.add_mem _ (Submodule.add_mem _ (basis_mem 0) (basis_mem 1)) (basis_mem 5)
    · change classes 7∈basisSpan
      rw [class_relation_7]
      simpa [basis,basisIndices] using Submodule.add_mem _ (Submodule.add_mem _ (basis_mem 0) (basis_mem 3)) (basis_mem 4)
  · apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact Submodule.subset_span ⟨basisIndices i,rfl⟩

theorem originalSpan_finrank : Module.finrank (ZMod 2) originalSpan=6 := by
  rw [originalSpan_eq_basisSpan]
  unfold basisSpan
  convert finrank_span_eq_card basis_independent using 1
  simp only [Fintype.card_fin]

/-- This dimension is the span of the κ coordinates. -/
theorem original_descent_span_finrank : Module.finrank (ZMod 2)
    (Submodule.span (ZMod 2) (Set.range (fun i =>
      completeDescentCoordinates curve 0 (-(A^2)) (-(B^2)) (originalPoints i))))=6 := by
  have he : (fun i => completeDescentCoordinates curve 0 (-(A^2)) (-(B^2))
      (originalPoints i))=classes := funext descent_coordinates
  rw [he]
  exact originalSpan_finrank

end First

namespace Second
abbrev A := SecondExampleRankSeven.A
abbrev B := SecondExampleRankSeven.B
abbrev curve := SecondExampleRankSeven.curve
theorem point_equation (i : Fin 6) : curve.toAffine.Equation
    (SecondReductionData.rationalX i) (SecondReductionData.rationalY i) := by
  rw [E_equation_iff]
  fin_cases i <;> norm_num [SecondReductionData.rationalX,SecondReductionData.rationalY,SecondExampleRankSeven.A,SecondExampleRankSeven.B]

def points (i : Fin 6) : RationalPoints curve := .mk (point_equation i)
def two : RationalPoints curve := twoLeft A B SecondExampleRankSeven.factor_nonzero
def four : RationalPoints curve := fourPoint A B SecondExampleRankSeven.factor_nonzero

def originalPoints : Fin 8 → RationalPoints curve :=
  ![points 0,points 1,points 2,points 3,points 4,points 5,two,four]

def representatives : Fin 8 → ℚ×ℚ := ![(1, 11640327889), (89290914216438, 71878), (83517906, 139426), (89290914216438, 71878), (-1069123, -83), (1, 1), (-1, -124787684716960258721), (89290914216438, 836683488005542)]
def squareFactors : Fin 8 → ℚ×ℚ := ![((22344670700:ℚ)/3, (207500:ℚ)/3), ((4981470:ℚ)/137977, (294747074330:ℚ)/137977), ((63762816:ℚ)/1805, (2716681856:ℚ)/1805), ((1807708:ℚ)/10643, (66279310612:ℚ)/10643), (2065952, 228972768), ((1838803881600:ℚ)/289, (1843603600000:ℚ)/289), (460019200, (1:ℚ)/460019200), (240, 80)]
def rawValues : Fin 8 → ℚ×ℚ :=
  ![(SecondReductionData.rationalX 0,SecondReductionData.rationalX 0+A^2),
    (SecondReductionData.rationalX 1,SecondReductionData.rationalX 1+A^2),
    (SecondReductionData.rationalX 2,SecondReductionData.rationalX 2+A^2),
    (SecondReductionData.rationalX 3,SecondReductionData.rationalX 3+A^2),
    (SecondReductionData.rationalX 4,SecondReductionData.rationalX 4+A^2),
    (SecondReductionData.rationalX 5,SecondReductionData.rationalX 5+A^2),
    (-A^2,(A^2-B^2)/A^2),(A*B,A*B+A^2)]

def classes (i : Fin 8) : ClassPair := pairClass (representatives i)

theorem square_factors (i : Fin 8) :
    (rawValues i).1=(representatives i).1*(squareFactors i).1^2 ∧
    (rawValues i).2=(representatives i).2*(squareFactors i).2^2 := by
  fin_cases i <;> norm_num [rawValues,representatives,squareFactors,
    SecondReductionData.rationalX,SecondExampleRankSeven.A,SecondExampleRankSeven.B]

theorem raw_classes (i : Fin 8) : pairClass (rawValues i)=classes i := by
  apply pairClass_factor _ _ (squareFactors i)
  · fin_cases i <;> norm_num [rawValues,SecondReductionData.rationalX,SecondExampleRankSeven.A,SecondExampleRankSeven.B]
  · fin_cases i <;> norm_num [representatives]
  · fin_cases i <;> norm_num [squareFactors]
  · exact square_factors i

theorem descent_coordinates (i : Fin 8) :
    completeDescentCoordinates curve 0 (-(A^2)) (-(B^2)) (originalPoints i)=classes i := by
  rw [←raw_classes i]
  fin_cases i <;> norm_num [originalPoints,points,two,four,twoLeft,fourPoint,
    WeierstrassCurve.Affine.Point.mk,completeDescentCoordinates,rawValues,pairClass,
    SecondReductionData.rationalX,SecondReductionData.rationalY,SecondExampleRankSeven.A,SecondExampleRankSeven.B]

def basisIndices : Fin 5 → Fin 8 := ![0, 2, 4, 6, 7]
def basis (i : Fin 5) : ClassPair := classes (basisIndices i)

def existingIndices : Fin 5 → Fin 9 := ![0,1,2,7,8]
theorem basis_independent : LinearIndependent (ZMod 2) basis := by
  have hi : Function.Injective existingIndices := by
    intro i j h
    fin_cases i <;> fin_cases j <;> norm_num [existingIndices] at *
  have he : basis=SecondExampleRankSeven.squareclasses ∘ existingIndices := by
    funext i
    fin_cases i <;> rfl
  rw [he]
  exact SecondExampleRankSeven.squareclasses_independent.comp existingIndices hi

theorem class_relation_1 : classes 1=classes 0+classes 7 := by
  calc
    _=pairClass (89290914216438, 9739270139696707529160838) := by
      apply pairClass_factor _ _ (1, (1:ℚ)/11640327889) <;> norm_num [classes,representatives]
    _=_ := by
      have hh := pairClass_mul (representatives 0) (representatives 7) (by norm_num [representatives]) (by norm_num [representatives])
      norm_num [representatives,classes] at hh ⊢
      exact hh

theorem class_relation_3 : classes 3=classes 0+classes 7 := class_relation_1

theorem class_relation_5 : classes 5=0 := by norm_num [classes,representatives,pairClass,squareClass_one]

def originalSpan : Submodule (ZMod 2) ClassPair := Submodule.span (ZMod 2) (Set.range classes)
def basisSpan : Submodule (ZMod 2) ClassPair := Submodule.span (ZMod 2) (Set.range basis)

private theorem basis_mem (i : Fin 5) : basis i∈basisSpan := Submodule.subset_span ⟨i,rfl⟩

theorem originalSpan_eq_basisSpan : originalSpan=basisSpan := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    fin_cases i
    · simpa [basis,basisIndices] using basis_mem 0
    · change classes 1∈basisSpan
      rw [class_relation_1]
      simpa [basis,basisIndices] using Submodule.add_mem _ (basis_mem 0) (basis_mem 4)
    · simpa [basis,basisIndices] using basis_mem 1
    · change classes 3∈basisSpan
      rw [class_relation_3]
      simpa [basis,basisIndices] using Submodule.add_mem _ (basis_mem 0) (basis_mem 4)
    · simpa [basis,basisIndices] using basis_mem 2
    · change classes 5∈basisSpan
      rw [class_relation_5]; exact Submodule.zero_mem _
    · simpa [basis,basisIndices] using basis_mem 3
    · simpa [basis,basisIndices] using basis_mem 4
  · apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact Submodule.subset_span ⟨basisIndices i,rfl⟩

theorem originalSpan_finrank : Module.finrank (ZMod 2) originalSpan=5 := by
  rw [originalSpan_eq_basisSpan]
  unfold basisSpan
  convert finrank_span_eq_card basis_independent using 1
  simp only [Fintype.card_fin]

/-- This dimension is the span of the κ coordinates. -/
theorem original_descent_span_finrank : Module.finrank (ZMod 2)
    (Submodule.span (ZMod 2) (Set.range (fun i =>
      completeDescentCoordinates curve 0 (-(A^2)) (-(B^2)) (originalPoints i))))=5 := by
  have he : (fun i => completeDescentCoordinates curve 0 (-(A^2)) (-(B^2))
      (originalPoints i))=classes := funext descent_coordinates
  rw [he]
  exact originalSpan_finrank

end Second
end
end Z2Z4Rank6.ExampleOriginalDescent
