import Z2Z4Rank6.ConicRankNineCertificateData
import Z2Z4Rank6.TwistSelmerDataNecessary
import Mathlib.LinearAlgebra.Matrix.Notation

/-! Exact certificate data for the rank-nine fiber in Proposition 7.1,
Dujella–Peral, Construction of high rank elliptic curves, Section 7.2, p. 19. -/
namespace Z2Z4Rank6.ConicRankNineCertificate.Selmer
open Z2Z4Rank6.TwistSelmer
open scoped BigOperators
set_option maxRecDepth 30000

def r2 : ℤ := 95880799729^2
def r3 : ℤ := 46529164800^2
def primes : Fin 22 → ℕ := ![2,3,5,7,11,13,17,19,23,31,41,43,53,61,71,89,101,127,193,421,1289,198377]

def constraints : Matrix (Fin 64) (Fin 67) (ZMod 2) :=
  let rows : Fin 64 → ℕ := ![16,128,256,2048,65536,524288,1048576,2097152,4194304,8388608,16777216,33554432,4294967296,17179869184,549755813888,562949953421312,1125899906842624,9007199254740992,144115188075855872,288230376151711744,576460752303423488,4611686018427387904,35184380477442,70368760954884,140737521909768,281475043819536,562950087639072,1125900175278144,2251800350556288,4503600701112576,9007201402225152,18014402804450304,36028805608900608,72057611217801216,144115222435602432,288230444871204864,576460889742409728,1152921779484819456,2305843558969638912,4611687117939277824,9223374235878555648,18446748471757111296,36893496943514222592,73786993887028445184,53438903937820262401,66352553656840093696,20111809298441437185,109307112846513930240,68845155313101307904,69674908360072232961,105141529481800843265,27396161929216,20945305600000,1497752403968,31268561485824,1486285176832,67325389,2674236,1075686471,4087636,1436136,916290,119012,276492]
  fun i => let bits := rows i; fun j => if bits.testBit j.val then 1 else 0

def kernelBasis : Matrix (Fin 67) (Fin 11) (ZMod 2) :=
  let rows : Fin 67 → ℕ := ![1,2,4,8,0,16,32,0,0,64,50,0,90,128,256,366,0,474,214,0,0,0,0,0,0,0,197,16,32,512,301,64,0,677,0,128,256,366,806,0,214,1024,157,1230,1779,2,4,8,197,0,0,512,301,0,50,677,90,0,0,0,806,474,0,1024,157,1230,1779]
  fun i => let bits := rows i; fun j => if bits.testBit j.val then 1 else 0

def projectionMatrix : Matrix (Fin 11) (Fin 67) (ZMod 2) :=
  let rows : Fin 11 → ℕ := ![1,2,4,8,32,64,512,8192,16384,536870912,2199023255552]
  fun i => let bits := rows i; fun j => if bits.testBit j.val then 1 else 0

def eliminator : Matrix (Fin 67) (Fin 64) (ZMod 2) :=
  let rows : Fin 67 → ℕ := ![0,0,0,0,1,0,0,2,4,0,86018539949739310,8,112811455824090917,0,0,64156750336762846,16,21183523737767503,81716721536597517,32,64,128,256,512,1024,2048,34580901043520383,67141632,134283264,0,72181016939548699,1073872896,4096,61602497868161407,8192,17180131328,34360262656,64156681618334686,72708919709555213,16384,81716171778686477,0,137483263277577755,34883266726676958,92476959047850866,4194816,8389632,16779264,34580901009965950,32768,65536,268435458,72181016402677791,131072,86018542097227054,61602493573194103,112811447234164517,262144,524288,1048576,72708782270601757,21183248859876943,2097152,1099511627808,137485462300833371,34878868680165726,92468162954828402]
  fun i => let bits := rows i; fun j => if bits.testBit j.val then 1 else 0

def primeConstraints : Fin 64 → PrimeConstraint 22 :=
  ![.zero 0 3,
    .zero 0 6,
    .zero 0 7,
    .zero 0 10,
    .zero 0 15,
    .zero 0 18,
    .zero 0 19,
    .zero 0 20,
    .zero 0 21,
    .zero 1 0,
    .zero 1 1,
    .zero 1 2,
    .zero 1 9,
    .zero 1 11,
    .zero 1 16,
    .zero 2 4,
    .zero 2 5,
    .zero 2 8,
    .zero 2 12,
    .zero 2 13,
    .zero 2 14,
    .zero 2 17,
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
    .product 20,
    .product 21,
    .character 2 4 ![0,0,0],
    .character 2 5 ![0,0,0],
    .character 2 8 ![0,0,0],
    .character 2 12 ![0,0,0],
    .character 2 13 ![0,0,0],
    .character 2 14 ![0,0,0],
    .character 2 17 ![0,0,0],
    .character 1 1 ![0,0,0],
    .character 1 2 ![0,0,0],
    .character 1 9 ![0,0,0],
    .character 1 11 ![0,0,0],
    .character 1 16 ![0,0,0],
    .character 0 3 ![0,1,0],
    .character 0 6 ![0,0,0],
    .character 0 7 ![0,1,0],
    .character 0 15 ![0,0,0],
    .character 0 18 ![0,0,0],
    .character 0 19 ![0,0,0],
    .character 0 20 ![0,0,0],
    .character 0 21 ![0,0,0]]

theorem roots_ordered : 0<r3 ∧ r3<r2 := by norm_num [r2,r3]
theorem primes_injective : Function.Injective primes := by decide +kernel
theorem primes_prime (j : Fin 22) : (primes j).Prime := by
  fin_cases j <;> norm_num [primes]
theorem supportPower (c : Fin 3) :
    rootProduct r2 r3 c∣((∏ i,primes i : ℕ) : ℤ)^20 := by
  fin_cases c <;> norm_num [rootProduct,r2,r3,primes,Fin.prod_univ_succ]

end Z2Z4Rank6.ConicRankNineCertificate.Selmer
