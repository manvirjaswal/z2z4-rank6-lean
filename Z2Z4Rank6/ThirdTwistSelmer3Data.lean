import Z2Z4Rank6.ThirdTwistData
import Z2Z4Rank6.TwistSelmerDataNecessary
import Z2Z4Rank6.SparseMatrixCertificate

/-! Exact certificate for the third-twist paragraph after Proposition 7.2,
Jaswal, DOI 10.5281/zenodo.23437117. -/
namespace Z2Z4Rank6.ThirdTwist.Selmer3
open Z2Z4Rank6.TwistSelmer
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def r2 : ℤ := ThirdTwist.r2 3
def r3 : ℤ := ThirdTwist.r3 3
def primes : Fin 20 → ℕ := ![2,3,5,7,13,17,23,31,41,47,53,109,227,547,647,739,1153,9103,16139,24113]
def constraints : Matrix (Fin 57) (Fin 61) (ZMod 2) :=
  let rows : Fin 57 → ℕ := ![8,16,128,16384,131072,1048576,4194304,33554432,67108864,536870912,68719476736,281474976710656,2251799813685248,4503599627370496,36028797018963968,2199025352706,4398050705412,8796101410824,17592202821648,35184405643296,70368811286592,140737622573184,281475245146368,562950490292736,1125900980585472,2251801961170944,4503603922341888,9007207844683776,18014415689367552,36028831378735104,72057662757470208,144115325514940416,288230651029880832,576461302059761664,1152922604119523328,1407625572204412929,1806944006156845056,4096,32768,1696187023360,1732778131456,1817740050432,512,65536,29609,32119981056,1827691,1907881943040,275853,14373879808,348147,914813353984,1484653,14425,17181381599,137438978392,1099511724412]
  fun i => let bits := rows i; fun j => if bits.testBit j.val then 1 else 0

def kernelBasis : Matrix (Fin 61) (Fin 4) (ZMod 2) :=
  let rows : Fin 61 → ℕ := ![1,2,4,0,0,7,7,0,3,0,1,3,0,5,0,0,0,0,2,5,0,8,0,6,5,0,0,5,3,0,13,3,0,13,1,0,0,1,13,9,1,10,4,6,5,7,7,5,0,0,12,0,0,8,1,0,0,1,15,12,1]
  fun i => let bits := rows i; fun j => if bits.testBit j.val then 1 else 0

def projectionMatrix : Matrix (Fin 4) (Fin 61) (ZMod 2) :=
  let rows : Fin 4 → ℕ := ![1,2,4,2097152]
  fun i => let bits := rows i; fun j => if bits.testBit j.val then 1 else 0

def eliminator : Matrix (Fin 61) (Fin 57) (ZMod 2) :=
  let rows : Fin 61 → ℕ := ![0,0,0,1,2,10427768277827592,14645907198836796,4,23147193665848011,4398046511104,96212054722655267,27914538644931313,137438953472,33535516964029134,8,274877906944,8796093022208,16,104084557977531427,14724659719176200,32,0,64,130719814944195118,136856130276633091,128,256,132614763530770233,23147193670044363,512,5004385849697704,27914538678489841,137506070528,19905008791198260,96810189048166115,275414794240,1024,40831738686996530,11854989173016698,100249897449585073,96607764540818123,32768,65600,130719814944064047,136856130276895233,10427768278352008,14645907199885628,132614763528673085,2048,4398054900224,91223373442011531,4096,8192,13954864312752378,96810189316601579,16384,8797166765056,40831740834480162,97907487724010585,94708367435528633,96607781720687339]
  fun i => let bits := rows i; fun j => if bits.testBit j.val then 1 else 0

def primeConstraints : Fin 57 → PrimeConstraint 20 :=
  ![.zero 0 2,
    .zero 0 3,
    .zero 0 6,
    .zero 0 13,
    .zero 0 16,
    .zero 0 19,
    .zero 1 1,
    .zero 1 4,
    .zero 1 5,
    .zero 1 8,
    .zero 1 15,
    .zero 2 7,
    .zero 2 10,
    .zero 2 11,
    .zero 2 14,
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
    .character 2 7 ![0,0,0],
    .character 2 10 ![0,0,0],
    .zero 0 11,
    .zero 0 14,
    .character 1 1 ![0,0,0],
    .character 1 4 ![0,0,0],
    .character 1 5 ![0,0,0],
    .zero 0 8,
    .zero 0 15,
    .character 0 9 ![0,0,0],
    .character 1 9 ![1,1,0],
    .character 0 12 ![1,0,0],
    .character 1 12 ![1,0,0],
    .character 0 17 ![1,0,0],
    .character 1 17 ![0,0,0],
    .character 0 18 ![0,0,0],
    .character 1 18 ![0,1,0],
    .character 0 3 ![0,0,0],
    .character 0 6 ![0,0,0],
    .character 0 13 ![0,1,0],
    .character 0 16 ![0,1,0],
    .character 0 19 ![0,1,0]]
theorem roots_ordered : 0<r3 ∧ r3<r2 := ThirdTwist.roots_ordered 3
theorem roots_nonzero_distinct : r2≠0 ∧ r3≠0 ∧ r2≠r3 := ThirdTwist.roots_nonzero_distinct 3
theorem primes_injective : Function.Injective primes := by decide +kernel
theorem primes_prime (j : Fin 20) : (primes j).Prime := by
  fin_cases j <;> norm_num [primes]
theorem supportPower (c : Fin 3) :
    rootProduct r2 r3 c∣((∏ i,primes i : ℕ) : ℤ)^10 := by
  fin_cases c <;> norm_num [rootProduct,r2,r3,ThirdTwist.r2,ThirdTwist.r3,
    ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes,Fin.prod_univ_succ]

end Z2Z4Rank6.ThirdTwist.Selmer3
