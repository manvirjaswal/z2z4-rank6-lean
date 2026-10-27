import Z2Z4Rank6.TwistSelmerDataParity

/-! Exact Euler-character certificates using Mathlib's proved modular-power
normalizer (NormNum.PowMod, Apache 2.0, Markus Himmel).
The prime is the largest discriminant-support prime of the rank-nine fiber. -/
namespace Z2Z4Rank6.ConicRankNineCertificate.Selmer
open Z2Z4Rank6.TwistSelmer
theorem parity198377_negOne : modularParity 198377 (-1)=0 := by
  norm_num [modularParity]

theorem parity198377_1 : modularParity 198377 (1)=0 := by
  norm_num [modularParity]

theorem parity198377_2 : modularParity 198377 (2)=0 := by
  norm_num [modularParity]
  reduce_mod_char
  decide +kernel

theorem parity198377_3 : modularParity 198377 (3)=1 := by
  norm_num [modularParity]
  reduce_mod_char
  decide +kernel

theorem parity198377_5 : modularParity 198377 (5)=1 := by
  norm_num [modularParity]
  reduce_mod_char
  decide +kernel

theorem parity198377_7 : modularParity 198377 (7)=0 := by
  norm_num [modularParity]
  reduce_mod_char
  decide +kernel

theorem parity198377_11 : modularParity 198377 (11)=0 := by
  norm_num [modularParity]
  reduce_mod_char
  decide +kernel

theorem parity198377_13 : modularParity 198377 (13)=0 := by
  norm_num [modularParity]
  reduce_mod_char
  decide +kernel

theorem parity198377_17 : modularParity 198377 (17)=0 := by
  norm_num [modularParity]
  reduce_mod_char
  decide +kernel

theorem parity198377_19 : modularParity 198377 (19)=0 := by
  norm_num [modularParity]
  reduce_mod_char
  decide +kernel

theorem parity198377_23 : modularParity 198377 (23)=0 := by
  norm_num [modularParity]
  reduce_mod_char
  decide +kernel

theorem parity198377_31 : modularParity 198377 (31)=0 := by
  norm_num [modularParity]
  reduce_mod_char
  decide +kernel

theorem parity198377_41 : modularParity 198377 (41)=1 := by
  norm_num [modularParity]
  reduce_mod_char
  decide +kernel

theorem parity198377_43 : modularParity 198377 (43)=1 := by
  norm_num [modularParity]
  reduce_mod_char
  decide +kernel

theorem parity198377_53 : modularParity 198377 (53)=1 := by
  norm_num [modularParity]
  reduce_mod_char
  decide +kernel

theorem parity198377_61 : modularParity 198377 (61)=0 := by
  norm_num [modularParity]
  reduce_mod_char
  decide +kernel

theorem parity198377_71 : modularParity 198377 (71)=0 := by
  norm_num [modularParity]
  reduce_mod_char
  decide +kernel

theorem parity198377_89 : modularParity 198377 (89)=0 := by
  norm_num [modularParity]
  reduce_mod_char
  decide +kernel

theorem parity198377_101 : modularParity 198377 (101)=0 := by
  norm_num [modularParity]
  reduce_mod_char
  decide +kernel

theorem parity198377_127 : modularParity 198377 (127)=1 := by
  norm_num [modularParity]
  reduce_mod_char
  decide +kernel

theorem parity198377_193 : modularParity 198377 (193)=0 := by
  norm_num [modularParity]
  reduce_mod_char
  decide +kernel

theorem parity198377_421 : modularParity 198377 (421)=0 := by
  norm_num [modularParity]
  reduce_mod_char
  decide +kernel

theorem parity198377_1289 : modularParity 198377 (1289)=0 := by
  norm_num [modularParity]
  reduce_mod_char
  decide +kernel

end Z2Z4Rank6.ConicRankNineCertificate.Selmer
