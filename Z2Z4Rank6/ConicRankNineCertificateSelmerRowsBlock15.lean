module

public import Z2Z4Rank6.ConicRankNineCertificateSelmerData
public import Z2Z4Rank6.TwistSelmerConstraintEntry
public import Z2Z4Rank6.ConicRankNineCertificateCharacter198377

@[expose] public section

/-! Kernel certificate for the rank-nine conic fiber. -/
namespace Z2Z4Rank6.ConicRankNineCertificate.Selmer
open Z2Z4Rank6.TwistSelmer
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem rowsBlock15 : ∀ k : Fin 4,
    let i : Fin 64 := ⟨60+k.val,by omega⟩
    ∀ j : Fin 67,constraints i j=TwistSelmer.constraintEntry primes (primeConstraints i) j := by
  intro k
  dsimp only
  fin_cases k
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j
    rw [←constraintRow_eq_constraintEntry]
    refine Fin.cases ?_ (fun t => ?_) j
    · rw [constraintRow_zero]
      norm_num [constraints,primeConstraints,primes,constraintHead,signWeight,Nat.testBit,parity198377_negOne,parity198377_1,parity198377_2,parity198377_3,parity198377_5,parity198377_7,parity198377_11,parity198377_13,parity198377_17,parity198377_19,parity198377_23,parity198377_31,parity198377_41,parity198377_43,parity198377_53,parity198377_61,parity198377_71,parity198377_89,parity198377_101,parity198377_127,parity198377_193,parity198377_421,parity198377_1289]
    · obtain ⟨⟨c,i⟩,rfl⟩ := (show Fin 3 × Fin 22 ≃ Fin 66 from finProdFinEquiv).surjective t
      change constraints (63 : Fin 64) (rawIndex c i)=constraintRow primes (primeConstraints (63 : Fin 64)) (rawIndex c i)
      rw [constraintRow_raw]
      fin_cases c <;> fin_cases i <;> norm_num [constraints,primeConstraints,primes,
        constraintTail,unitPrimeFactor,rawIndex,finProdFinEquiv,Nat.testBit,parity198377_negOne,parity198377_1,parity198377_2,parity198377_3,parity198377_5,parity198377_7,parity198377_11,parity198377_13,parity198377_17,parity198377_19,parity198377_23,parity198377_31,parity198377_41,parity198377_43,parity198377_53,parity198377_61,parity198377_71,parity198377_89,parity198377_101,parity198377_127,parity198377_193,parity198377_421,parity198377_1289]
end Z2Z4Rank6.ConicRankNineCertificate.Selmer
