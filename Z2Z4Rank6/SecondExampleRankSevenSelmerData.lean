import Z2Z4Rank6.SecondExampleRankSevenData
import Z2Z4Rank6.TwistSelmerDataNecessary
import Mathlib.LinearAlgebra.Matrix.Notation

/-! Exact certificate data for the rank-seven second example after Theorem 8.1,
Jaswal DOI 10.5281/zenodo.23437117. -/
namespace Z2Z4Rank6.SecondExampleRankSeven.Selmer
open Z2Z4Rank6.TwistSelmer
open scoped BigOperators
set_option maxRecDepth 30000

def r2 : ℤ := 11180308689^2
def r3 : ℤ := 460019200^2
def primes : Fin 20 → ℕ := ![2,3,5,7,11,13,17,23,31,53,61,83,89,137,241,401,433,457,1171,2089]

def constraints : Matrix (Fin 59) (Fin 61) (ZMod 2) :=
  let rows : Fin 59 → ℕ := ![16,64,256,1024,8192,16384,32768,65536,262144,1048576,2097152,8388608,4294967296,137438953472,4398046511104,35184372088832,140737488355328,562949953421312,2251799813685248,576460752303423488,2199025352706,4398050705412,8796101410824,17592202821648,35184405643296,70368811286592,140737622573184,281475245146368,562950490292736,1125900980585472,2251801961170944,4503603922341888,9007207844683776,18014415689367552,36028831378735104,72057662757470208,144115325514940416,288230651029880832,576461302059761664,1152922604119523328,105177083289796609,1484166974660411393,111248586498375680,2305249272934694913,515576395426955264,68739267945299969,435358269440,1538749628416,1115374485504,18004685,389690,270531769,1923854,973652,898892,549872,1068996,32616,202544]
  fun i => let bits := rows i; fun j => if bits.testBit j.val then 1 else 0

def kernelBasis : Matrix (Fin 61) (Fin 9) (ZMod 2) :=
  let rows : Fin 61 → ℕ := ![1,2,4,8,0,16,0,32,0,38,0,2,60,0,0,0,0,10,0,22,0,0,4,0,63,16,64,32,27,38,64,2,0,128,256,448,492,0,256,22,128,2,0,8,63,0,64,0,27,0,64,0,60,128,256,448,492,10,256,0,128]
  fun i => let bits := rows i; fun j => if bits.testBit j.val then 1 else 0

def projectionMatrix : Matrix (Fin 9) (Fin 61) (ZMod 2) :=
  let rows : Fin 9 → ℕ := ![1,2,4,8,32,128,67108864,8589934592,17179869184]
  fun i => let bits := rows i; fun j => if bits.testBit j.val then 1 else 0

def eliminator : Matrix (Fin 61) (Fin 59) (ZMod 2) :=
  let rows : Fin 61 → ℕ := ![0,0,0,0,1,0,2,0,4,22878240500952384,8,22517998136853114,24004140407794865,16,32,64,128,13510798882112195,256,19140298416324655,512,1024,2113536,2048,28513308473316979,16809984,0,67174400,34137239569379294,22878240232648000,7970576767601805,22517999210857082,4096,0,0,12489514257572406,13599005375386462,8192,28733331947808,19140573294755887,7965633831128727,1049600,16384,4196352,28513308464928370,32768,33554434,65536,34137239703597018,131072,7970577304472709,262144,24004142555282609,4294967312,8589934624,12489497077703286,13598971015648222,13510867601597123,28595892994080,524288,7965084075314327]
  fun i => let bits := rows i; fun j => if bits.testBit j.val then 1 else 0

def primeConstraints : Fin 59 → PrimeConstraint 20 :=
  ![.zero 0 3,
    .zero 0 5,
    .zero 0 7,
    .zero 0 9,
    .zero 0 12,
    .zero 0 13,
    .zero 0 14,
    .zero 0 15,
    .zero 0 17,
    .zero 0 19,
    .zero 1 0,
    .zero 1 2,
    .zero 1 11,
    .zero 1 16,
    .zero 2 1,
    .zero 2 4,
    .zero 2 6,
    .zero 2 8,
    .zero 2 10,
    .zero 2 18,
    .product 0,
    .product 1,
    .product 2,
    .product 3,
    .product 4,
    .product 5,
    .product 6,
    .product 7,
    .product 8,
    .product 9,
    .product 10,
    .product 11,
    .product 12,
    .product 13,
    .product 14,
    .product 15,
    .product 16,
    .product 17,
    .product 18,
    .product 19,
    .character 2 1 ![0,0,0],
    .character 2 4 ![0,0,0],
    .character 2 6 ![0,0,0],
    .character 2 8 ![0,0,0],
    .character 2 10 ![0,0,0],
    .character 2 18 ![0,0,0],
    .character 1 2 ![0,0,0],
    .character 1 11 ![0,0,0],
    .character 1 16 ![0,0,0],
    .character 0 3 ![0,1,0],
    .character 0 5 ![0,0,0],
    .character 0 7 ![0,1,0],
    .character 0 9 ![0,0,0],
    .character 0 12 ![0,0,0],
    .character 0 13 ![0,0,0],
    .character 0 14 ![0,0,0],
    .character 0 15 ![0,0,0],
    .character 0 17 ![0,0,0],
    .character 0 19 ![0,0,0]]

theorem roots_ordered : 0<r3 ∧ r3<r2 := by norm_num [r2,r3]
theorem primes_injective : Function.Injective primes := by decide +kernel
theorem primes_prime (j : Fin 20) : (primes j).Prime := by
  fin_cases j <;> norm_num [primes]
theorem supportPower (c : Fin 3) :
    rootProduct r2 r3 c∣((∏ i,primes i : ℕ) : ℤ)^20 := by
  fin_cases c <;> norm_num [rootProduct,r2,r3,primes,Fin.prod_univ_succ]

end Z2Z4Rank6.SecondExampleRankSeven.Selmer
