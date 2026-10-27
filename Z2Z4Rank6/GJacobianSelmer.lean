module

public import Z2Z4Rank6.GJacobianCertificate
public import Z2Z4Rank6.GJacobianVector

@[expose] public section

/-! The explicit full two-Selmer model for J_G has dimension 4. -/
namespace Z2Z4Rank6

theorem gJacobian_fullTwoSelmerClasses_eq_space :
    fullTwoSelmerClasses 9801 2401=(gJacobianSelmerSpace:Set _) := by
  rw [fullTwoSelmerClasses,gJacobian_fullTwoSelmerTriples]
  exact gJacobian_survivor_classes_eq_space

theorem gJacobian_fullTwoSelmer_dimension :
    Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (fullTwoSelmerClasses 9801 2401))=4 := by
  rw [gJacobian_fullTwoSelmerClasses_eq_space,Submodule.span_eq]
  exact gJacobianSelmerSpace_finrank

theorem gJacobian_fullTwoSelmerClasses_card : (fullTwoSelmerClasses 9801 2401).ncard=16 := by
  rw [fullTwoSelmerClasses,gJacobian_fullTwoSelmerTriples]
  have hinj:Set.InjOn
      (fun d:ECFullTriple=>(squareClass (d.1:ℚ),squareClass (d.2.1:ℚ)))
      (gJacobianSurvivors.toFinset:Set ECFullTriple) := by
    intro d hd e he hde
    have hd':d∈gJacobianSurvivors := by simpa only [Finset.mem_coe,List.mem_toFinset] using hd
    have he':e∈gJacobianSurvivors := by simpa only [Finset.mem_coe,List.mem_toFinset] using he
    obtain ⟨i,rfl⟩ := (gJacobianSurvivorTriple_mem_iff d).mp hd'
    obtain ⟨j,rfl⟩ := (gJacobianSurvivorTriple_mem_iff e).mp he'
    change gJacobianPairClass ((gJacobianSurvivorTriple i).1,(gJacobianSurvivorTriple i).2.1)=
      gJacobianPairClass ((gJacobianSurvivorTriple j).1,(gJacobianSurvivorTriple j).2.1) at hde
    rw [gJacobian_survivor_class_formula,gJacobian_survivor_class_formula] at hde
    have hc:gJacobianCoefficients i=gJacobianCoefficients j :=
      gJacobian_basis_independent.fintypeLinearCombination_injective hde
    have hi:i=j := (by decide +kernel:Function.Injective gJacobianCoefficients) hc
    rw [hi]
  rw [hinj.ncard_image,Set.ncard_coe_finset,gJacobianSurvivors_card]

end Z2Z4Rank6
