module

public import Z2Z4Rank6.TwistSelmerDataSieve
public import Z2Z4Rank6.TwistSelmerDataBitsQ2

@[expose] public section

/-! Bounded exact decoding and mod 8 checks. Jaswal Proposition 5.2,
DOI 10.5281/zenodo.23437117. -/
namespace Z2Z4Rank6.TwistSelmer
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

def q2FreeTail (i : Fin 1) : Fin 0 → ZMod 2 :=
  fun j => if i.val.testBit j.val then 1 else 0

def q2FreeChunk (i : Fin 1) : List (Fin 4 → ZMod 2) :=
  (binaryVectors 4).map (fun v => Fin.append v (q2FreeTail i))

def q2RawChunk : Fin 1 → List ECFullTriple
  | 0 => [(1,1,1),(-630953917,1204355831336421,-230963073),(438955,184582700446,1272027130),(-35935,67567197174,-2428027230447690),(4411561,108750670649014,410556417131014),(-43485942493,97854,-15998262),(30253195,183658903118461,20889525126295),(-158529444535,37501672569,-98494935),(1,35935,35935),(-630953917,837871038915,-8299658028255),(438955,128414290,35398),(-35935,2428027230447690,-67567197174),(4411561,75657903610,285624333610),(-43485942493,3516383490,-11130),(30253195,6599782683561896035,30026603416536433),(-158529444535,26089935,-141576619569)]

def q2RawPool : List ECFullTriple := (List.finRange 1).flatMap q2RawChunk

theorem q2Vectors_chunks : binaryVectors 4=
    (List.finRange 1).flatMap q2FreeChunk := by decide +kernel

theorem q2DecodedChunk_check (i : Fin 1) :
    (q2FreeChunk i).map (fun v => candidate q2Primes (q2KernelBasis.mulVec v))=q2RawChunk i := by
  fin_cases i; decide +kernel

theorem q2RawPool_decode : decodedPool q2Primes q2KernelBasis=q2RawPool := by
  rw [decodedPool,q2Vectors_chunks,List.map_flatMap]
  simp only [q2DecodedChunk_check]
  rfl

def q2FirstChunk : Fin 1 → List ECFullTriple
  | 0 => [(1,1,1),(-35935,67567197174,-2428027230447690),(4411561,108750670649014,410556417131014),(-158529444535,37501672569,-98494935),(1,35935,35935),(-35935,2428027230447690,-67567197174),(4411561,75657903610,285624333610),(-158529444535,26089935,-141576619569)]

def q2StageFirst : List ECFullTriple := (List.finRange 1).flatMap q2FirstChunk

theorem q2FirstChunk_check (i : Fin 1) :
    (q2RawChunk i).filter (splitCoverResiduePossibleFor 8 (r2 1) (r3 1))=q2FirstChunk i := by
  fin_cases i; decide +kernel

theorem q2StageFirst_check :
    q2RawPool.filter (splitCoverResiduePossibleFor 8 (r2 1) (r3 1))=q2StageFirst := by
  simp only [q2RawPool,List.filter_flatMap,q2FirstChunk_check]
  rfl

theorem q2StageFirst_explicit : q2StageFirst=[(1,1,1),(-35935,67567197174,-2428027230447690),(4411561,108750670649014,410556417131014),(-158529444535,37501672569,-98494935),(1,35935,35935),(-35935,2428027230447690,-67567197174),(4411561,75657903610,285624333610),(-158529444535,26089935,-141576619569)] := rfl

end Z2Z4Rank6.TwistSelmer
