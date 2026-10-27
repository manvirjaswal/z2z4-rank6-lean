import Z2Z4Rank6.ThirdTwistSelmer2Data
import Z2Z4Rank6.TwistSelmerDataSieve

/-! Exact certificate for the third-twist paragraph after Proposition 7.2,
Jaswal, DOI 10.5281/zenodo.23437117. -/
namespace Z2Z4Rank6.ThirdTwist.Selmer2
open Z2Z4Rank6.TwistSelmer
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def freeTail (i : Fin 1) : Fin 0 → ZMod 2 :=
  fun j => if i.val.testBit j.val then 1 else 0
def freeChunk (i : Fin 1) : List (Fin 2 → ZMod 2) :=
  (binaryVectors 2).map (fun v => Fin.append v (freeTail i))
def rawChunk : Fin 1 → List ECFullTriple
  | 0 => [(1,1,1),(-24714163,207402551886,-5125780473926561418),(1,24714163,24714163),(-24714163,5125780473926561418,-207402551886)]
def rawPool : List ECFullTriple := (List.finRange 1).flatMap rawChunk
theorem vectors_chunks : binaryVectors 2=(List.finRange 1).flatMap freeChunk := by decide +kernel
theorem decodedChunk_check (i : Fin 1) :
    (freeChunk i).map (fun v => candidate primes (kernelBasis.mulVec v))=rawChunk i := by
  fin_cases i; decide +kernel
theorem rawPool_decode : decodedPool primes kernelBasis=rawPool := by
  rw [decodedPool,vectors_chunks,List.map_flatMap]
  simp only [decodedChunk_check]
  rfl
theorem rawPool_explicit : rawPool=[(1,1,1),(-24714163,207402551886,-5125780473926561418),(1,24714163,24714163),(-24714163,5125780473926561418,-207402551886)] := rfl

end Z2Z4Rank6.ThirdTwist.Selmer2
