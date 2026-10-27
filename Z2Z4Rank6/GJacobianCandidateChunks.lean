import Z2Z4Rank6.GJacobianCandidateChunk00
import Z2Z4Rank6.GJacobianCandidateChunk01
import Z2Z4Rank6.GJacobianCandidateChunk02
import Z2Z4Rank6.GJacobianCandidateChunk03
import Z2Z4Rank6.GJacobianCandidateChunk04
import Z2Z4Rank6.GJacobianCandidateChunk05
import Z2Z4Rank6.GJacobianCandidateChunk06
import Z2Z4Rank6.GJacobianCandidateChunk07
import Z2Z4Rank6.GJacobianCandidateChunk08
import Z2Z4Rank6.GJacobianCandidateChunk09
import Z2Z4Rank6.GJacobianCandidateChunk10
import Z2Z4Rank6.GJacobianCandidateChunk11
import Z2Z4Rank6.GJacobianCandidateChunk12
import Z2Z4Rank6.GJacobianCandidateChunk13
import Z2Z4Rank6.GJacobianCandidateChunk14
import Z2Z4Rank6.GJacobianCandidateChunk15
import Z2Z4Rank6.GJacobianCandidateChunk16
import Z2Z4Rank6.GJacobianCandidateChunk17
import Z2Z4Rank6.GJacobianCandidateChunk18
import Z2Z4Rank6.GJacobianCandidateChunk19
import Z2Z4Rank6.GJacobianCandidateChunk20
import Z2Z4Rank6.GJacobianCandidateChunk21
import Z2Z4Rank6.GJacobianCandidateChunk22
import Z2Z4Rank6.GJacobianCandidateChunk23
import Z2Z4Rank6.GJacobianCandidateChunk24
import Z2Z4Rank6.GJacobianCandidateChunk25
import Z2Z4Rank6.GJacobianCandidateChunk26
import Z2Z4Rank6.GJacobianCandidateChunk27
import Z2Z4Rank6.GJacobianCandidateChunk28
import Z2Z4Rank6.GJacobianCandidateChunk29
import Z2Z4Rank6.GJacobianCandidateChunk30
import Z2Z4Rank6.GJacobianCandidateChunk31
import Z2Z4Rank6.GJacobianCandidateChunk32
import Z2Z4Rank6.GJacobianCandidateChunk33
import Z2Z4Rank6.GJacobianCandidateChunk34
import Z2Z4Rank6.GJacobianCandidateChunk35
import Z2Z4Rank6.GJacobianCandidateChunk36
import Z2Z4Rank6.GJacobianCandidateChunk37
import Z2Z4Rank6.GJacobianCandidateChunk38
import Z2Z4Rank6.GJacobianCandidateChunk39
import Z2Z4Rank6.GJacobianCandidateChunk40
import Z2Z4Rank6.GJacobianCandidateChunk41
import Z2Z4Rank6.GJacobianCandidateChunk42
import Z2Z4Rank6.GJacobianCandidateChunk43
import Z2Z4Rank6.GJacobianCandidateChunk44
import Z2Z4Rank6.GJacobianCandidateChunk45
import Z2Z4Rank6.GJacobianCandidateChunk46
import Z2Z4Rank6.GJacobianCandidateChunk47
import Z2Z4Rank6.GJacobianCandidateChunk48
import Z2Z4Rank6.GJacobianCandidateChunk49
import Z2Z4Rank6.GJacobianCandidateChunk50
import Z2Z4Rank6.GJacobianCandidateChunk51
import Z2Z4Rank6.GJacobianCandidateChunk52
import Z2Z4Rank6.GJacobianCandidateChunk53
import Z2Z4Rank6.GJacobianCandidateChunk54
import Z2Z4Rank6.GJacobianCandidateChunk55
import Z2Z4Rank6.GJacobianCandidateChunk56
import Z2Z4Rank6.GJacobianCandidateChunk57
import Z2Z4Rank6.GJacobianCandidateChunk58
import Z2Z4Rank6.GJacobianCandidateChunk59
import Z2Z4Rank6.GJacobianCandidateChunk60
import Z2Z4Rank6.GJacobianCandidateChunk61
import Z2Z4Rank6.GJacobianCandidateChunk62
import Z2Z4Rank6.GJacobianCandidateChunk63
namespace Z2Z4Rank6
theorem gJacobianCandidate_chunks (a:ℤ) (ha:a∈gJacobianD1) (j:Fin 4):
    (gJacobianRawChunk a j).filter (fun d=>intSquareTest (d.1*d.2.1*d.2.2))=
      gJacobianResultChunk a j := by
  simp only [gJacobianD1,List.mem_cons,List.not_mem_nil,or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · fin_cases j
    · exact gJacobianCandidate_chunk_00
    · exact gJacobianCandidate_chunk_01
    · exact gJacobianCandidate_chunk_02
    · exact gJacobianCandidate_chunk_03
  · fin_cases j
    · exact gJacobianCandidate_chunk_04
    · exact gJacobianCandidate_chunk_05
    · exact gJacobianCandidate_chunk_06
    · exact gJacobianCandidate_chunk_07
  · fin_cases j
    · exact gJacobianCandidate_chunk_08
    · exact gJacobianCandidate_chunk_09
    · exact gJacobianCandidate_chunk_10
    · exact gJacobianCandidate_chunk_11
  · fin_cases j
    · exact gJacobianCandidate_chunk_12
    · exact gJacobianCandidate_chunk_13
    · exact gJacobianCandidate_chunk_14
    · exact gJacobianCandidate_chunk_15
  · fin_cases j
    · exact gJacobianCandidate_chunk_16
    · exact gJacobianCandidate_chunk_17
    · exact gJacobianCandidate_chunk_18
    · exact gJacobianCandidate_chunk_19
  · fin_cases j
    · exact gJacobianCandidate_chunk_20
    · exact gJacobianCandidate_chunk_21
    · exact gJacobianCandidate_chunk_22
    · exact gJacobianCandidate_chunk_23
  · fin_cases j
    · exact gJacobianCandidate_chunk_24
    · exact gJacobianCandidate_chunk_25
    · exact gJacobianCandidate_chunk_26
    · exact gJacobianCandidate_chunk_27
  · fin_cases j
    · exact gJacobianCandidate_chunk_28
    · exact gJacobianCandidate_chunk_29
    · exact gJacobianCandidate_chunk_30
    · exact gJacobianCandidate_chunk_31
  · fin_cases j
    · exact gJacobianCandidate_chunk_32
    · exact gJacobianCandidate_chunk_33
    · exact gJacobianCandidate_chunk_34
    · exact gJacobianCandidate_chunk_35
  · fin_cases j
    · exact gJacobianCandidate_chunk_36
    · exact gJacobianCandidate_chunk_37
    · exact gJacobianCandidate_chunk_38
    · exact gJacobianCandidate_chunk_39
  · fin_cases j
    · exact gJacobianCandidate_chunk_40
    · exact gJacobianCandidate_chunk_41
    · exact gJacobianCandidate_chunk_42
    · exact gJacobianCandidate_chunk_43
  · fin_cases j
    · exact gJacobianCandidate_chunk_44
    · exact gJacobianCandidate_chunk_45
    · exact gJacobianCandidate_chunk_46
    · exact gJacobianCandidate_chunk_47
  · fin_cases j
    · exact gJacobianCandidate_chunk_48
    · exact gJacobianCandidate_chunk_49
    · exact gJacobianCandidate_chunk_50
    · exact gJacobianCandidate_chunk_51
  · fin_cases j
    · exact gJacobianCandidate_chunk_52
    · exact gJacobianCandidate_chunk_53
    · exact gJacobianCandidate_chunk_54
    · exact gJacobianCandidate_chunk_55
  · fin_cases j
    · exact gJacobianCandidate_chunk_56
    · exact gJacobianCandidate_chunk_57
    · exact gJacobianCandidate_chunk_58
    · exact gJacobianCandidate_chunk_59
  · fin_cases j
    · exact gJacobianCandidate_chunk_60
    · exact gJacobianCandidate_chunk_61
    · exact gJacobianCandidate_chunk_62
    · exact gJacobianCandidate_chunk_63
end Z2Z4Rank6
