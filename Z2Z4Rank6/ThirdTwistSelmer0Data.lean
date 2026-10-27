import Z2Z4Rank6.ThirdTwistData
import Z2Z4Rank6.TwistSelmerDataNecessary
import Z2Z4Rank6.SparseMatrixCertificate

/-! Exact certificate for the third-twist paragraph after Proposition 7.2,
Jaswal, DOI 10.5281/zenodo.23437117. -/
namespace Z2Z4Rank6.ThirdTwist.Selmer0
open Z2Z4Rank6.TwistSelmer
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def r2 : ℤ := ThirdTwist.r2 0
def r3 : ℤ := ThirdTwist.r3 0
def primes : Fin 15 → ℕ := ![2,3,5,7,11,17,19,31,37,41,43,47,53,263,346441]
def constraints : Matrix (Fin 40) (Fin 46) (ZMod 2) :=
  let rows : Fin 40 → ℕ := ![2,8,16,512,32768,2097152,4194304,8388608,67108864,34359738368,1099511627776,4398046511104,8796093022208,2147549186,4295098372,8590196744,17180393488,34360786976,68721573952,137443147904,274886295808,549772591616,1099545183232,2199090366464,4398180732928,8796361465856,17592722931712,35185445863424,32,31048318582784,3753801416705,54303419006976,64,128,892469248,1632567296,29849,441188352,5581,2506]
  fun i => let bits := rows i; fun j => if bits.testBit j.val then 1 else 0

def kernelBasis : Matrix (Fin 46) (Fin 6) (ZMod 2) :=
  let rows : Fin 46 → ℕ := ![1,0,2,0,0,0,0,0,4,0,8,4,15,4,2,0,16,32,1,2,0,0,0,0,6,8,0,15,4,34,23,16,34,1,2,0,0,0,4,6,0,4,0,0,32,23]
  fun i => let bits := rows i; fun j => if bits.testBit j.val then 1 else 0

def projectionMatrix : Matrix (Fin 6) (Fin 46) (ZMod 2) :=
  let rows : Fin 6 → ℕ := ![1,4,256,1024,65536,131072]
  fun i => let bits := rows i; fun j => if bits.testBit j.val then 1 else 0

def eliminator : Matrix (Fin 46) (Fin 40) (ZMod 2) :=
  let rows : Fin 46 → ℕ := ![0,1,0,2,4,268435456,4294967296,8589934592,0,8,0,562640715779,287762808834,58956688855,398259105235,16,0,0,555134519233,1030688290388,268567040,32,64,128,798054448916,4195328,256,287779588098,58923138519,757656306147,477030911778,8193,16384,555134486467,1030688224848,512,4295229472,8590458944,1048704,798056546076,1024,562649104643,2048,4096,1017265679408,477165129522]
  fun i => let bits := rows i; fun j => if bits.testBit j.val then 1 else 0

def primeConstraints : Fin 40 → PrimeConstraint 15 :=
  ![.zero 0 0,
    .zero 0 2,
    .zero 0 3,
    .zero 0 8,
    .zero 0 14,
    .zero 1 5,
    .zero 1 6,
    .zero 1 7,
    .zero 1 10,
    .zero 2 4,
    .zero 2 9,
    .zero 2 11,
    .zero 2 12,
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
    .zero 0 4,
    .character 2 9 ![0,0,0],
    .character 2 11 ![0,0,0],
    .character 2 12 ![0,0,0],
    .zero 0 5,
    .zero 0 6,
    .character 1 7 ![0,0,0],
    .character 1 10 ![0,0,0],
    .character 0 13 ![1,0,0],
    .character 1 13 ![0,0,0],
    .character 0 3 ![0,0,0],
    .character 0 8 ![0,0,0]]
theorem roots_ordered : 0<r3 ∧ r3<r2 := ThirdTwist.roots_ordered 0
theorem roots_nonzero_distinct : r2≠0 ∧ r3≠0 ∧ r2≠r3 := ThirdTwist.roots_nonzero_distinct 0
theorem primes_injective : Function.Injective primes := by decide +kernel
theorem primes_prime (j : Fin 15) : (primes j).Prime := by
  fin_cases j <;> norm_num [primes]
theorem supportPower (c : Fin 3) :
    rootProduct r2 r3 c∣((∏ i,primes i : ℕ) : ℤ)^10 := by
  fin_cases c <;> norm_num [rootProduct,r2,r3,ThirdTwist.r2,ThirdTwist.r3,
    ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes,Fin.prod_univ_succ]

end Z2Z4Rank6.ThirdTwist.Selmer0
