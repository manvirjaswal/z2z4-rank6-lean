import Z2Z4Rank6.TwistSelmerDataConstraints

/-!
# Fast exact entries of semantic covering constraints

These formulas retain the proved constraint row and evaluate only the
single quadratic character relevant to an output coordinate. They support
bounded matrix/source comparisons without evaluating characters multiplied
by zero selector entries.
-/

namespace Z2Z4Rank6.TwistSelmer

open scoped BigOperators
noncomputable section

private theorem rawIndex_eq_iff {s : ℕ} (c c' : Fin 3) (j i : Fin s) :
    rawIndex c j=rawIndex c' i ↔ c=c' ∧ j=i := by
  constructor
  · intro h
    have hh := finProdFinEquiv.injective (Fin.succ_inj.mp h)
    exact ⟨congrArg Prod.fst hh,congrArg Prod.snd hh⟩
  · rintro ⟨rfl,rfl⟩
    rfl

private theorem rawIndex_ne_zero {s : ℕ} (c : Fin 3) (i : Fin s) : rawIndex c i≠0 :=
  Fin.succ_ne_zero _

@[simp] theorem selectorRow_raw_zero {s : ℕ} (c : Fin 3) (i : Fin s) :
    selectorRow (rawIndex c i) 0=0 := by
  simp [selectorRow,rawIndex_ne_zero]

@[simp] theorem selectorRow_zero_raw {s : ℕ} (c : Fin 3) (i : Fin s) :
    selectorRow (0 : Fin (BitDimension s)) (rawIndex c i)=0 := by
  simp [selectorRow,rawIndex_ne_zero]

@[simp] theorem selectorRow_raw_raw {s : ℕ} (c c' : Fin 3) (j i : Fin s) :
    selectorRow (rawIndex c j) (rawIndex c' i)=if c=c' ∧ j=i then 1 else 0 := by
  simp [selectorRow,Pi.single_apply,rawIndex_eq_iff,eq_comm,and_comm]

@[simp] theorem characterRow_zero {s : ℕ} (ps : Fin s → ℕ) (c : Fin 3) (p : ℕ) :
    characterRow ps c p 0=signWeight c p := by
  simp only [characterRow,Pi.add_apply,Pi.smul_apply,Finset.sum_apply,
    selectorRow_raw_zero,smul_eq_mul,mul_zero,Finset.sum_const_zero,add_zero]
  simp [selectorRow]

@[simp] theorem characterRow_raw {s : ℕ} (ps : Fin s → ℕ) (c c' : Fin 3)
    (p : ℕ) (i : Fin s) :
    characterRow ps c p (rawIndex c' i)=
      if c=c' then modularParity p (unitPrimeFactor p (ps i)) else 0 := by
  simp only [characterRow,Pi.add_apply,Pi.smul_apply,Finset.sum_apply,smul_eq_mul,
    selectorRow_zero_raw,mul_zero,zero_add,selectorRow_raw_raw]
  by_cases hc : c=c'
  · simp [hc,mul_ite]
  · simp [hc]

def constraintHead {s : ℕ} (ps : Fin s → ℕ) : PrimeConstraint s → ZMod 2
  | .zero _ _ => 0
  | .product _ => 0
  | .character c j _ => signWeight c (ps j)

def constraintTail {s : ℕ} (ps : Fin s → ℕ) : PrimeConstraint s → Fin 3 → Fin s → ZMod 2
  | .zero c j,c',i => if c=c' ∧ j=i then 1 else 0
  | .product j,_,i => if j=i then 1 else 0
  | .character c j w,c',i =>
      (if c=c' then modularParity (ps j) (unitPrimeFactor (ps j) (ps i)) else 0)+
        (if j=i then w c' else 0)

/-- Exact computable entry formula, with one character lookup per column. -/
def constraintEntry {s : ℕ} (ps : Fin s → ℕ) (q : PrimeConstraint s) :
    Fin (BitDimension s) → ZMod 2 :=
  Fin.cons (constraintHead ps q) (fun t =>
    constraintTail ps q (finProdFinEquiv.symm t).1 (finProdFinEquiv.symm t).2)

theorem constraintRow_zero {s : ℕ} (ps : Fin s → ℕ) (q : PrimeConstraint s) :
    constraintRow ps q 0=constraintHead ps q := by
  cases q <;> simp [constraintRow,constraintHead]

theorem constraintRow_raw {s : ℕ} (ps : Fin s → ℕ) (q : PrimeConstraint s)
    (c' : Fin 3) (i : Fin s) :
    constraintRow ps q (rawIndex c' i)=constraintTail ps q c' i := by
  cases q with
  | zero c j => simp [constraintRow,constraintTail]
  | product j =>
    simp only [constraintRow,constraintTail,Finset.sum_apply,selectorRow_raw_raw]
    by_cases h : j=i <;> simp [h]
  | character c j w =>
    simp only [constraintRow,constraintTail,Pi.add_apply,characterRow_raw,
      Finset.sum_apply,Pi.smul_apply,smul_eq_mul,selectorRow_raw_raw]
    by_cases h : j=i <;> simp [h,mul_ite]

/-- The fast formula agrees with the semantic matrix row. -/
theorem constraintRow_eq_constraintEntry {s : ℕ} (ps : Fin s → ℕ) (q : PrimeConstraint s) :
    constraintRow ps q=constraintEntry ps q := by
  funext k
  refine Fin.cases ?_ (fun t => ?_) k
  · simpa only [constraintEntry,Fin.cons_zero] using constraintRow_zero ps q
  · obtain ⟨⟨c',i⟩,rfl⟩ := finProdFinEquiv.surjective t
    simpa only [constraintEntry,Fin.cons_succ,Equiv.symm_apply_apply,rawIndex] using
      constraintRow_raw ps q c' i

end
end Z2Z4Rank6.TwistSelmer
