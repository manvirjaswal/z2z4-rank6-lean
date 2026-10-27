module

public import Z2Z4Rank6.GQuarticForward

@[expose] public section

/-! Naturality and cubic expansion for the explicit G/JG birational chart,
Proposition 7.2(a), DOI 10.5281/zenodo.23437117. -/
namespace Z2Z4Rank6
section
variable {L M : Type*} [Field L] [Field M]
theorem map_gQuarticM (f : L→+*M) (x y : L) :
    f (gQuarticM x y)=gQuarticM (f x) (f y) := by
  simp [gQuarticM,gQuarticT,gPointedX,gPointedY,pointedInverseT,
    pointedInverseNum,pointedInverseLinear,pointedInverseDen,
    gQuarticA,gQuarticB,gQuarticD,gQuarticQ,map_ofNat]
theorem map_gQuarticEta (f : L→+*M) (x y : L) :
    f (gQuarticEta x y)=gQuarticEta (f x) (f y) := by
  simp [gQuarticEta,gPointedX,gPointedY,pointedInverseEta,pointedInverseT,
    pointedInverseNum,pointedInverseLinear,pointedInverseDen,
    gQuarticA,gQuarticB,gQuarticD,gQuarticQ,map_ofNat]
theorem gJacobian_cubic_factor (x : L) :
    (x+5734)*(x-1666)*(x-4067)=x^3+x^2-26097400*x+38851416548 := by ring
end
end Z2Z4Rank6
