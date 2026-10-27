import Z2Z4Rank6.ECFullSelmerData

/-! # Raw and surviving chunks of the full two-descent candidates -/
namespace Z2Z4Rank6
def ecFullRawCandidateChunk (a : ℤ) : List ECFullTriple :=
  ecFullSecondDivisors.flatMap (fun b => ecFullThirdDivisors.map (fun c => (a,b,c)))
def ecFullCandidateSurvivorChunk (a : ℤ) : List ECFullTriple :=
  ecFullCandidates.filter (fun d => decide (d.1=a))
def ecFullRawTriples : List ECFullTriple :=
  ecDescentDivisors.flatMap ecFullRawCandidateChunk
end Z2Z4Rank6
