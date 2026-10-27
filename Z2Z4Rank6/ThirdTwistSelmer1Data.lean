module

public import Z2Z4Rank6.ThirdTwistData
public import Z2Z4Rank6.TwistSelmerDataNecessary
public import Z2Z4Rank6.SparseMatrixCertificate

@[expose] public section

/-! Exact certificate for the third-twist paragraph after Proposition 7.2,
Jaswal, DOI 10.5281/zenodo.23437117. -/
namespace Z2Z4Rank6.ThirdTwist.Selmer1
open Z2Z4Rank6.TwistSelmer
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def r2 : ℤ := ThirdTwist.r2 1
def r3 : ℤ := ThirdTwist.r3 1
def primes : Fin 18 → ℕ := ![2,3,5,7,11,13,17,29,31,61,71,83,97,167,239,409,2473,4969]
def constraints : Matrix (Fin 50) (Fin 55) (ZMod 2) :=
  let rows : Fin 50 → ℕ := ![256,8192,131072,262144,2097152,33554432,268435456,8589934592,1099511627776,2199023255552,4398046511104,35184372088832,140737488355328,137439477762,274878955524,549757911048,1099515822096,2199031644192,4398063288384,8796126576768,17592253153536,35184506307072,70369012614144,140738025228288,281476050456576,562952100913152,1125904201826304,2251808403652608,4503616807305216,9007233614610432,18014467229220864,24607894863347713,26279564854427649,8905631868125184,17273602550267905,29958393322012673,41932029952,76184289280,121043943424,32768,436299,115446644736,137417,40317763584,403312,105725820928,67577510,104920,34359828232,105904]
  fun i => let bits := rows i; fun j => if bits.testBit j.val then 1 else 0

def kernelBasis : Matrix (Fin 55) (Fin 5) (ZMod 2) :=
  let rows : Fin 55 → ℕ := ![1,2,4,8,0,6,6,13,0,8,8,13,15,0,15,0,1,0,0,16,16,0,0,6,6,0,12,8,0,13,31,2,31,0,25,4,2,18,20,8,0,0,0,13,12,0,8,0,16,2,16,0,24,4,2]
  fun i => let bits := rows i; fun j => if bits.testBit j.val then 1 else 0

def projectionMatrix : Matrix (Fin 5) (Fin 55) (ZMod 2) :=
  let rows : Fin 5 → ℕ := ![1,2,4,8,524288]
  fun i => let bits := rows i; fun j => if bits.testBit j.val then 1 else 0

def eliminator : Matrix (Fin 55) (Fin 50) (ZMod 2) :=
  let rows : Fin 55 → ℕ := ![0,0,0,0,169055776353017,655912378860917,250724796530853,1038347364058686,1,573676055374582,53347423323600,252374063972523,1044394678011444,2,1112773449159758,549755813888,32166578694908,4,8,0,105537397411056,16,169055776287737,655912378992501,250724796269733,32,986087978092191,573676053275382,64,252374072365227,989369694574750,1090348896183292,1123700886147044,128,1124158870615954,985559027046154,1090326314055926,8192,105537397394672,32784,256,512,1024,1038347363534366,986087979140766,2048,53347427517840,4096,59427348258474,1090348862628862,11062862683050,549890031744,1094202768776558,985559563917070,1090325240314110]
  fun i => let bits := rows i; fun j => if bits.testBit j.val then 1 else 0

def primeConstraints : Fin 50 → PrimeConstraint 18 :=
  ![.zero 0 7,
    .zero 0 12,
    .zero 0 16,
    .zero 0 17,
    .zero 1 2,
    .zero 1 6,
    .zero 1 9,
    .zero 1 14,
    .zero 2 3,
    .zero 2 4,
    .zero 2 5,
    .zero 2 8,
    .zero 2 10,
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
    .character 2 3 ![0,0,0],
    .character 2 4 ![0,0,0],
    .character 2 5 ![0,0,0],
    .character 2 8 ![0,0,0],
    .character 2 10 ![0,0,0],
    .character 1 2 ![0,0,0],
    .character 1 6 ![0,0,0],
    .character 1 9 ![0,0,0],
    .zero 0 14,
    .character 0 11 ![0,0,0],
    .character 1 11 ![0,1,0],
    .character 0 13 ![0,0,0],
    .character 1 13 ![1,1,0],
    .character 0 15 ![0,0,0],
    .character 1 15 ![0,0,0],
    .character 0 7 ![0,1,0],
    .character 0 12 ![0,0,0],
    .character 0 16 ![0,1,0],
    .character 0 17 ![0,0,0]]
theorem roots_ordered : 0<r3 ∧ r3<r2 := ThirdTwist.roots_ordered 1
theorem roots_nonzero_distinct : r2≠0 ∧ r3≠0 ∧ r2≠r3 := ThirdTwist.roots_nonzero_distinct 1
theorem primes_injective : Function.Injective primes := by decide +kernel
theorem primes_prime (j : Fin 18) : (primes j).Prime := by
  fin_cases j <;> norm_num [primes]
theorem supportPower (c : Fin 3) :
    rootProduct r2 r3 c∣((∏ i,primes i : ℕ) : ℤ)^10 := by
  fin_cases c <;> norm_num [rootProduct,r2,r3,ThirdTwist.r2,ThirdTwist.r3,
    ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes,Fin.prod_univ_succ]

end Z2Z4Rank6.ThirdTwist.Selmer1
