import Z2Z4Rank6.GTorsionCoverDoubleNormalForm

/-! Ordered polynomial basis 1,u,v,uv for arbitrary two-square covers. -/
namespace Z2Z4Rank6.DoubleSquareCover
noncomputable section
@[simp] theorem basisIndex_zero : basisIndex 0=(0,0) := rfl
@[simp] theorem basisIndex_one : basisIndex 1=(1,0) := rfl
@[simp] theorem basisIndex_two : basisIndex 2=(0,1) := rfl
@[simp] theorem basisIndex_three : basisIndex 3=(1,1) := rfl

theorem towerRoot_zero (f : Fin 2→Poly) :
    towerRoot f 0=algebraMap (First f) (Tower f) QuadraticAlgebra.omega := rfl
theorem towerRoot_one (f : Fin 2→Poly) : towerRoot f 1=QuadraticAlgebra.omega := rfl

theorem towerBasis_zero (f : Fin 2→Poly) : towerBasis f 0=1 := by
  simp only [towerBasis,Module.Basis.reindex_apply,Equiv.symm_symm,basisIndex_zero,
    Module.Basis.smulTower_apply,QuadraticAlgebra.basis_apply_zero,one_smul]
theorem towerBasis_one (f : Fin 2→Poly) : towerBasis f 1=towerRoot f 0 := by
  simp only [towerBasis,Module.Basis.reindex_apply,Equiv.symm_symm,basisIndex_one,
    Module.Basis.smulTower_apply,QuadraticAlgebra.basis_apply_one,
    QuadraticAlgebra.basis_apply_zero,Algebra.smul_def,mul_one]
  rfl
theorem towerBasis_two (f : Fin 2→Poly) : towerBasis f 2=towerRoot f 1 := by
  simp only [towerBasis,Module.Basis.reindex_apply,Equiv.symm_symm,basisIndex_two,
    Module.Basis.smulTower_apply,QuadraticAlgebra.basis_apply_one,
    QuadraticAlgebra.basis_apply_zero,one_smul]
  rfl
theorem towerBasis_three (f : Fin 2→Poly) : towerBasis f 3=towerRoot f 0*towerRoot f 1 := by
  simp only [towerBasis,Module.Basis.reindex_apply,Equiv.symm_symm,basisIndex_three,
    Module.Basis.smulTower_apply,QuadraticAlgebra.basis_apply_one,Algebra.smul_def]
  rfl

theorem coordinateBasis_zero (f : Fin 2→Poly) : coordinateBasis f 0=1 := by
  apply (coordinateTowerPolynomialEquiv f).injective
  rw [coordinateBasis_image,towerBasis_zero,map_one]
theorem coordinateBasis_one (f : Fin 2→Poly) : coordinateBasis f 1=root f 0 := by
  apply (coordinateTowerPolynomialEquiv f).injective
  rw [coordinateBasis_image,towerBasis_one,coordinateTowerPolynomialEquiv_apply,coordinateToTower_root]
theorem coordinateBasis_two (f : Fin 2→Poly) : coordinateBasis f 2=root f 1 := by
  apply (coordinateTowerPolynomialEquiv f).injective
  rw [coordinateBasis_image,towerBasis_two,coordinateTowerPolynomialEquiv_apply,coordinateToTower_root]
theorem coordinateBasis_three (f : Fin 2→Poly) : coordinateBasis f 3=root f 0*root f 1 := by
  apply (coordinateTowerPolynomialEquiv f).injective
  rw [coordinateBasis_image,towerBasis_three,map_mul,coordinateTowerPolynomialEquiv_apply,
    coordinateTowerPolynomialEquiv_apply,coordinateToTower_root,coordinateToTower_root]

theorem polynomialToCoordinate_injective (f : Fin 2→Poly) : Function.Injective (polynomialToCoordinate f) := by
  intro p q h
  have hh := congrArg (coordinateToTower f) h
  rw [coordinateToTower_polynomial,coordinateToTower_polynomial] at hh
  exact congrArg (fun z : Tower f=>z.re.re) hh
end
end Z2Z4Rank6.DoubleSquareCover
