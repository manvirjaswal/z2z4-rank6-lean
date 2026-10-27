module

public import Z2Z4Rank6.TripleSquareNormalForm

@[expose] public section

/-! Explicit values of the ordered eight-element normal-form basis. -/
namespace Z2Z4Rank6.TripleSquareCover
noncomputable section
@[simp] theorem basisIndex_zero : basisIndex 0=((0,0),0) := rfl
@[simp] theorem basisIndex_one : basisIndex 1=((1,0),0) := rfl
@[simp] theorem basisIndex_two : basisIndex 2=((0,1),0) := rfl
@[simp] theorem basisIndex_three : basisIndex 3=((1,1),0) := rfl
@[simp] theorem basisIndex_four : basisIndex 4=((0,0),1) := rfl
@[simp] theorem basisIndex_five : basisIndex 5=((1,0),1) := rfl
@[simp] theorem basisIndex_six : basisIndex 6=((0,1),1) := rfl
@[simp] theorem basisIndex_seven : basisIndex 7=((1,1),1) := rfl

@[simp] theorem twoBasis_zero (f : Fin 3→Poly) : twoBasis f (0,0)=1 := by
  simp only [twoBasis,Module.Basis.smulTower_apply,QuadraticAlgebra.basis_apply_zero,one_smul]
@[simp] theorem twoBasis_one (f : Fin 3→Poly) : twoBasis f (1,0)=
    algebraMap (First f) (Second f) QuadraticAlgebra.omega := by
  simp only [twoBasis,Module.Basis.smulTower_apply,QuadraticAlgebra.basis_apply_one,
    QuadraticAlgebra.basis_apply_zero,Algebra.smul_def,mul_one]
@[simp] theorem twoBasis_two (f : Fin 3→Poly) : twoBasis f (0,1)=QuadraticAlgebra.omega := by
  simp only [twoBasis,Module.Basis.smulTower_apply,QuadraticAlgebra.basis_apply_one,
    QuadraticAlgebra.basis_apply_zero,one_smul]
@[simp] theorem twoBasis_three (f : Fin 3→Poly) : twoBasis f (1,1)=
    algebraMap (First f) (Second f) QuadraticAlgebra.omega*QuadraticAlgebra.omega := by
  simp only [twoBasis,Module.Basis.smulTower_apply,QuadraticAlgebra.basis_apply_one,Algebra.smul_def]

theorem towerRoot_zero (f : Fin 3→Poly) : towerRoot f 0=algebraMap (First f) (Tower f) QuadraticAlgebra.omega := rfl
theorem towerRoot_one (f : Fin 3→Poly) : towerRoot f 1=algebraMap (Second f) (Tower f) QuadraticAlgebra.omega := rfl
theorem towerRoot_two (f : Fin 3→Poly) : towerRoot f 2=QuadraticAlgebra.omega := rfl

theorem towerBasis_zero (f : Fin 3→Poly) : towerBasis f 0=1 := by
  simp only [towerBasis,Module.Basis.reindex_apply,Equiv.symm_symm,basisIndex_zero,
    Module.Basis.smulTower_apply,twoBasis_zero,QuadraticAlgebra.basis_apply_zero,one_smul]
theorem towerBasis_one (f : Fin 3→Poly) : towerBasis f 1=towerRoot f 0 := by
  simp only [towerBasis,Module.Basis.reindex_apply,Equiv.symm_symm,basisIndex_one,
    Module.Basis.smulTower_apply,twoBasis_one,QuadraticAlgebra.basis_apply_zero,Algebra.smul_def,mul_one]
  exact (IsScalarTower.algebraMap_apply (First f) (Second f) (Tower f) _).symm
theorem towerBasis_two (f : Fin 3→Poly) : towerBasis f 2=towerRoot f 1 := by
  simp only [towerBasis,Module.Basis.reindex_apply,Equiv.symm_symm,basisIndex_two,
    Module.Basis.smulTower_apply,twoBasis_two,QuadraticAlgebra.basis_apply_zero,Algebra.smul_def,mul_one]
  rfl
theorem towerBasis_three (f : Fin 3→Poly) : towerBasis f 3=towerRoot f 0*towerRoot f 1 := by
  simp only [towerBasis,Module.Basis.reindex_apply,Equiv.symm_symm,basisIndex_three,
    Module.Basis.smulTower_apply,twoBasis_three,QuadraticAlgebra.basis_apply_zero,
    Algebra.smul_def,mul_one,map_mul]
  rw [←IsScalarTower.algebraMap_apply (First f) (Second f) (Tower f)]
  rfl
theorem towerBasis_four (f : Fin 3→Poly) : towerBasis f 4=towerRoot f 2 := by
  simp only [towerBasis,Module.Basis.reindex_apply,Equiv.symm_symm,basisIndex_four,
    Module.Basis.smulTower_apply,twoBasis_zero,QuadraticAlgebra.basis_apply_one,one_smul]
  rfl
theorem towerBasis_five (f : Fin 3→Poly) : towerBasis f 5=towerRoot f 0*towerRoot f 2 := by
  simp only [towerBasis,Module.Basis.reindex_apply,Equiv.symm_symm,basisIndex_five,
    Module.Basis.smulTower_apply,twoBasis_one,QuadraticAlgebra.basis_apply_one,Algebra.smul_def]
  rw [←IsScalarTower.algebraMap_apply (First f) (Second f) (Tower f)]
  rfl
theorem towerBasis_six (f : Fin 3→Poly) : towerBasis f 6=towerRoot f 1*towerRoot f 2 := by
  simp only [towerBasis,Module.Basis.reindex_apply,Equiv.symm_symm,basisIndex_six,
    Module.Basis.smulTower_apply,twoBasis_two,QuadraticAlgebra.basis_apply_one,Algebra.smul_def]
  rfl
theorem towerBasis_seven (f : Fin 3→Poly) : towerBasis f 7=towerRoot f 0*towerRoot f 1*towerRoot f 2 := by
  simp only [towerBasis,Module.Basis.reindex_apply,Equiv.symm_symm,basisIndex_seven,
    Module.Basis.smulTower_apply,twoBasis_three,QuadraticAlgebra.basis_apply_one,Algebra.smul_def,map_mul]
  rw [←IsScalarTower.algebraMap_apply (First f) (Second f) (Tower f)]
  rw [←towerRoot_zero f,←towerRoot_one f,←towerRoot_two f]

theorem coordinateBasis_zero (f : Fin 3→Poly) : coordinateBasis f 0=1 := by
  apply (coordinateTowerPolynomialEquiv f).injective
  rw [coordinateBasis_image,towerBasis_zero,map_one]
theorem coordinateBasis_one (f : Fin 3→Poly) : coordinateBasis f 1=root f 0 := by
  apply (coordinateTowerPolynomialEquiv f).injective
  rw [coordinateBasis_image,towerBasis_one,coordinateTowerPolynomialEquiv_apply,coordinateToTower_root]
theorem coordinateBasis_two (f : Fin 3→Poly) : coordinateBasis f 2=root f 1 := by
  apply (coordinateTowerPolynomialEquiv f).injective
  rw [coordinateBasis_image,towerBasis_two,coordinateTowerPolynomialEquiv_apply,coordinateToTower_root]
theorem coordinateBasis_three (f : Fin 3→Poly) : coordinateBasis f 3=root f 0*root f 1 := by
  apply (coordinateTowerPolynomialEquiv f).injective
  rw [coordinateBasis_image,towerBasis_three,map_mul,coordinateTowerPolynomialEquiv_apply,
    coordinateTowerPolynomialEquiv_apply,coordinateToTower_root,coordinateToTower_root]
theorem coordinateBasis_four (f : Fin 3→Poly) : coordinateBasis f 4=root f 2 := by
  apply (coordinateTowerPolynomialEquiv f).injective
  rw [coordinateBasis_image,towerBasis_four,coordinateTowerPolynomialEquiv_apply,coordinateToTower_root]
theorem coordinateBasis_five (f : Fin 3→Poly) : coordinateBasis f 5=root f 0*root f 2 := by
  apply (coordinateTowerPolynomialEquiv f).injective
  rw [coordinateBasis_image,towerBasis_five,map_mul,coordinateTowerPolynomialEquiv_apply,
    coordinateTowerPolynomialEquiv_apply,coordinateToTower_root,coordinateToTower_root]
theorem coordinateBasis_six (f : Fin 3→Poly) : coordinateBasis f 6=root f 1*root f 2 := by
  apply (coordinateTowerPolynomialEquiv f).injective
  rw [coordinateBasis_image,towerBasis_six,map_mul,coordinateTowerPolynomialEquiv_apply,
    coordinateTowerPolynomialEquiv_apply,coordinateToTower_root,coordinateToTower_root]
theorem coordinateBasis_seven (f : Fin 3→Poly) : coordinateBasis f 7=root f 0*root f 1*root f 2 := by
  apply (coordinateTowerPolynomialEquiv f).injective
  rw [coordinateBasis_image,towerBasis_seven,map_mul,map_mul,coordinateTowerPolynomialEquiv_apply,
    coordinateTowerPolynomialEquiv_apply,coordinateTowerPolynomialEquiv_apply,
    coordinateToTower_root,coordinateToTower_root,coordinateToTower_root]

theorem polynomialToCoordinate_injective (f : Fin 3→Poly) : Function.Injective (polynomialToCoordinate f) := by
  intro p q h
  have hh := congrArg (coordinateToTower f) h
  rw [coordinateToTower_polynomial,coordinateToTower_polynomial] at hh
  have he := congrArg (fun z : Tower f=>z.re.re.re) hh
  exact he
end
end Z2Z4Rank6.TripleSquareCover
