import Z2Z4Rank6.TwistSelmerDataMod27Q1
import Z2Z4Rank6.TwistSelmerDataFilterQ2
import Z2Z4Rank6.TwistSelmerDataMod27Q12

/-! Eight exact surviving canonical triples in each twist fiber.
Jaswal Proposition 5.2, DOI 10.5281/zenodo.23437117. -/
namespace Z2Z4Rank6.TwistSelmer

def q1HighS : ℤ := -214126169044032
def q1SurvivorList : List ECFullTriple := [(1,1,1),(-13830,371746821257,-24191767110),(78595609,6163050332679,16753823082159),(-1086977272470,15695463,-65564992010),(1,13830,13830),(-13830,24191767110,-371746821257),(78595609,44562909130,121141164730),(-1086977272470,24118694810,-42667023)]
def q2SurvivorList : List ECFullTriple := q2StageFirst
def q12SurvivorList : List ECFullTriple := q12StageSecond

theorem q1HighDifference_identity : r3 0-r2 0=(5 : ℤ)^4*q1HighS := by
  norm_num [r2,r3,D,A,B,q1HighS]

theorem q1HighDifference_filter_eq :
    q1StageSecond.filter (highDifferenceTest 5 q1HighS)=q1SurvivorList := by decide +kernel

def survivorList : Fin 3 → List ECFullTriple := ![q1SurvivorList,q2SurvivorList,q12SurvivorList]
def survivors (k : Fin 3) : Finset ECFullTriple := (survivorList k).toFinset

theorem survivors_card (k : Fin 3) : (survivors k).card=8 := by
  fin_cases k <;> decide +kernel

end Z2Z4Rank6.TwistSelmer
