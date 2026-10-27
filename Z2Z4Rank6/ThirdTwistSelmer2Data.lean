import Z2Z4Rank6.ThirdTwistData
import Z2Z4Rank6.TwistSelmerDataNecessary
import Z2Z4Rank6.SparseMatrixCertificate

/-! Exact certificate for the third-twist paragraph after Proposition 7.2,
Jaswal, DOI 10.5281/zenodo.23437117. -/
namespace Z2Z4Rank6.ThirdTwist.Selmer2
open Z2Z4Rank6.TwistSelmer
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def r2 : ℤ := ThirdTwist.r2 2
def r3 : ℤ := ThirdTwist.r3 2
def primes : Fin 18 → ℕ := ![2,3,5,7,11,13,17,29,31,61,71,83,97,167,239,1783,2473,4969]
def constraints : Matrix (Fin 53) (Fin 55) (ZMod 2) :=
  let rows : Fin 53 → ℕ := ![2,4,256,8192,131072,262144,2097152,33554432,268435456,8589934592,1099511627776,2199023255552,4398046511104,35184372088832,140737488355328,137439477762,274878955524,549757911048,1099515822096,2199031644192,4398063288384,8796126576768,17592253153536,35184506307072,70369012614144,140738025228288,281476050456576,562952100913152,1125904201826304,2251808403652608,4503616807305216,9007233614610432,18014467229220864,16,21775965227057153,64,12770002922897409,29958393322012673,8,128,103864074240,32768,440395,114372902912,219337,53202665472,441197,132836818944,1104299,67577510,104920,34359828232,105904]
  fun i => let bits := rows i; fun j => if bits.testBit j.val then 1 else 0

def kernelBasis : Matrix (Fin 55) (Fin 2) (ZMod 2) :=
  let rows : Fin 55 → ℕ := ![1,0,0,0,0,0,0,0,0,0,0,0,1,0,1,0,1,0,0,1,1,0,0,0,0,0,1,0,0,0,2,1,2,0,2,1,1,1,1,0,0,0,0,0,1,0,0,0,3,1,3,0,3,1,1]
  fun i => let bits := rows i; fun j => if bits.testBit j.val then 1 else 0

def projectionMatrix : Matrix (Fin 2) (Fin 55) (ZMod 2) :=
  let rows : Fin 2 → ℕ := ![1,1073741824]
  fun i => let bits := rows i; fun j => if bits.testBit j.val then 1 else 0

def eliminator : Matrix (Fin 55) (Fin 53) (ZMod 2) :=
  let rows : Fin 55 → ℕ := ![0,1,2,274877906944,8589934592,8992259909883180,34359738368,549755813888,4,8926289212216619,3362451138024748,6495740793577629,6497699298664612,8,1145699706077204,2199023255552,1130856299102269,16,32,8140094751217737,7570015849551108,64,8590197760,8992259909360940,34360791040,128,3855040937202989,8926289203836203,256,6495740760006813,0,3939729094749162,5617596540186160,512,4350894222979162,7974482958352403,7418858771841389,8140094751184968,7570015849616646,274878038080,1024,2048,4096,549757911168,3855040941397289,8192,3362451121247276,16384,6497699365773476,3939728960531426,6728111605739044,2199560126976,3221155689115751,7974485105836035,7418854476874061]
  fun i => let bits := rows i; fun j => if bits.testBit j.val then 1 else 0

def primeConstraints : Fin 53 → PrimeConstraint 18 :=
  ![.zero 0 0,
    .zero 0 1,
    .zero 0 7,
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
    .zero 0 3,
    .character 2 4 ![0,0,0],
    .zero 0 5,
    .character 2 8 ![0,0,0],
    .character 2 10 ![0,0,0],
    .zero 0 2,
    .zero 0 6,
    .character 1 9 ![0,0,0],
    .zero 0 14,
    .character 0 11 ![1,0,0],
    .character 1 11 ![0,0,0],
    .character 0 13 ![1,0,0],
    .character 1 13 ![1,0,0],
    .character 0 15 ![0,0,0],
    .character 1 15 ![1,1,0],
    .character 0 1 ![0,1,0],
    .character 0 7 ![0,1,0],
    .character 0 12 ![0,0,0],
    .character 0 16 ![0,1,0],
    .character 0 17 ![0,0,0]]
theorem roots_ordered : 0<r3 ∧ r3<r2 := ThirdTwist.roots_ordered 2
theorem roots_nonzero_distinct : r2≠0 ∧ r3≠0 ∧ r2≠r3 := ThirdTwist.roots_nonzero_distinct 2
theorem primes_injective : Function.Injective primes := by decide +kernel
theorem primes_prime (j : Fin 18) : (primes j).Prime := by
  fin_cases j <;> norm_num [primes]
theorem supportPower (c : Fin 3) :
    rootProduct r2 r3 c∣((∏ i,primes i : ℕ) : ℤ)^10 := by
  fin_cases c <;> norm_num [rootProduct,r2,r3,ThirdTwist.r2,ThirdTwist.r3,
    ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes,Fin.prod_univ_succ]

end Z2Z4Rank6.ThirdTwist.Selmer2
