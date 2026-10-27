module

public import Z2Z4Rank6.GExampleRankSixData
public import Z2Z4Rank6.TwistSelmerDataNecessary
public import Mathlib.LinearAlgebra.Matrix.Notation

@[expose] public section

/-! Exact certificate data for the rank-six G-fiber example after Proposition 7.2,
Jaswal DOI 10.5281/zenodo.23437117. -/
namespace Z2Z4Rank6.GExampleRankSix.Selmer
open Z2Z4Rank6.TwistSelmer
open scoped BigOperators
set_option maxRecDepth 30000

def r2 : ℤ := 379291648^2
def r3 : ℤ := 212565977^2
def primes : Fin 18 → ℕ := ![2,3,5,7,13,17,19,23,31,43,53,59,71,73,97,307,4001,5953]

def constraints : Matrix (Fin 52) (Fin 55) (ZMod 2) :=
  let rows : Fin 52 → ℕ := ![4,8,16,2048,32768,65536,131072,262144,8388608,16777216,33554432,67108864,134217728,2147483648,137438953472,70368744177664,281474976710656,1125899906842624,137439477762,274878955524,549757911048,1099515822096,2199031644192,4398063288384,8796126576768,17592253153536,35184506307072,70369012614144,140738025228288,281476050456576,562952100913152,1125904201826304,2251808403652608,4503616807305216,9007233614610432,18014467229220864,28721305301811201,3503181485047809,32061209310134272,33460584448,118320267264,29672079360,112531079168,5193596928,27611103232,1194315,4575981,156558,12792,17180153647,19780,83288]
  fun i => let bits := rows i; fun j => if bits.testBit j.val then 1 else 0

def kernelBasis : Matrix (Fin 55) (Fin 8) (ZMod 2) :=
  let rows : Fin 55 → ℕ := ![1,2,0,0,0,2,4,8,16,32,64,0,112,110,84,0,0,0,0,2,9,75,11,0,0,0,0,0,64,29,112,0,84,51,85,128,174,0,9,75,11,2,4,8,16,32,0,29,0,110,0,51,85,128,174]
  fun i => let bits := rows i; fun j => if bits.testBit j.val then 1 else 0

def projectionMatrix : Matrix (Fin 8) (Fin 55) (ZMod 2) :=
  let rows : Fin 8 → ℕ := ![1,2,64,128,256,512,1024,34359738368]
  fun i => let bits := rows i; fun j => if bits.testBit j.val then 1 else 0

def eliminator : Matrix (Fin 55) (Fin 52) (ZMod 2) :=
  let rows : Fin 55 → ℕ := ![0,0,1,2,4,142102339683732,0,0,0,0,0,8,1269332278271859,1266637395198026,1125899906842633,16,32,64,128,278528,37879255162739,61518889127539,53272417678707,256,512,1024,2048,4096,134250496,1169279002009978,1269331741466483,8192,1125902054457353,141960500763780,4875235871998,0,1308346807648510,16384,37879254638450,61518890176113,53272419775863,142102335489172,8389120,16778240,33556480,67112960,32768,1169278733574514,65536,1266638468948042,131072,141964795731092,4866645937374,17179869248,1308312447910014]
  fun i => let bits := rows i; fun j => if bits.testBit j.val then 1 else 0

def primeConstraints : Fin 52 → PrimeConstraint 18 :=
  ![.zero 0 1,
    .zero 0 2,
    .zero 0 3,
    .zero 0 10,
    .zero 0 14,
    .zero 0 15,
    .zero 0 16,
    .zero 0 17,
    .zero 1 4,
    .zero 1 5,
    .zero 1 6,
    .zero 1 7,
    .zero 1 8,
    .zero 1 12,
    .zero 2 0,
    .zero 2 9,
    .zero 2 11,
    .zero 2 13,
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
    .character 2 9 ![0,0,0],
    .character 2 11 ![0,0,0],
    .character 2 13 ![0,0,0],
    .character 1 4 ![0,0,0],
    .character 1 5 ![0,0,0],
    .character 1 6 ![0,0,0],
    .character 1 7 ![0,0,0],
    .character 1 8 ![0,0,0],
    .character 1 12 ![0,0,0],
    .character 0 1 ![0,1,0],
    .character 0 3 ![0,1,0],
    .character 0 10 ![0,0,0],
    .character 0 14 ![0,0,0],
    .character 0 15 ![0,1,0],
    .character 0 16 ![0,0,0],
    .character 0 17 ![0,0,0]]

theorem roots_ordered : 0<r3 ∧ r3<r2 := by norm_num [r2,r3]
theorem primes_injective : Function.Injective primes := by decide +kernel
theorem primes_prime (j : Fin 18) : (primes j).Prime := by
  fin_cases j <;> norm_num [primes]
theorem supportPower (c : Fin 3) :
    rootProduct r2 r3 c∣((∏ i,primes i : ℕ) : ℤ)^22 := by
  fin_cases c <;> norm_num [rootProduct,r2,r3,primes,Fin.prod_univ_succ]

end Z2Z4Rank6.GExampleRankSix.Selmer
