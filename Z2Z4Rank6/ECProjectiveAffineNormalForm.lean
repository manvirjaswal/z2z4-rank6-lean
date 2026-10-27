import Z2Z4Rank6.ECProjectiveAffineCoordinate

/-! Free normal forms of the printed EC affine quotient over Q[x].
The basis is 1,y; the polynomial algebra sends X to the quotient x.
Both universal maps are inverse. -/
namespace Z2Z4Rank6.ECProjectiveAffineFunctionField
noncomputable section
open Polynomial

theorem coordinateToTower_polynomial (p : Poly) :
    coordinateToTower (polynomialToCoordinate p)=algebraMap Poly Tower p := by
  have hh : coordinateToTower.toRingHom.comp polynomialToCoordinate=algebraMap Poly Tower := by
    apply Polynomial.ringHom_ext'
    · exact Subsingleton.elim _ _
    · change coordinateToTower (polynomialToCoordinate Polynomial.X)=towerX
      rw [polynomialToCoordinate_X,coordinateToTower_x]
  exact RingHom.congr_fun hh p

theorem towerToCoordinate_polynomial (p : Poly) :
    towerToCoordinate (algebraMap Poly Tower p)=polynomialToCoordinate p := by
  change towerToCoordinateRing (algebraMap Poly Tower p)=polynomialToCoordinate p
  exact quadraticRingLift_algebraMap _ _ _ _ p

theorem coordinateToTower_comp : coordinateToTower.comp towerToCoordinate=AlgHom.id ℚ Tower := by
  apply AlgHom.ext
  intro z
  have hz : z=algebraMap Poly Tower z.re+algebraMap Poly Tower z.im*towerY := by
    simpa only [Algebra.smul_def,mul_one,towerY] using (QuadraticAlgebra.re_smul_add_im_smul z).symm
  change coordinateToTower (towerToCoordinate z)=z
  calc
    _=coordinateToTower (towerToCoordinate
      (algebraMap Poly Tower z.re+algebraMap Poly Tower z.im*towerY)) := congrArg _ (congrArg _ hz)
    _=algebraMap Poly Tower z.re+algebraMap Poly Tower z.im*towerY := by
      rw [map_add,map_mul,towerToCoordinate_polynomial,towerToCoordinate_polynomial,
        towerToCoordinate_y,map_add,map_mul,coordinateToTower_polynomial,
        coordinateToTower_polynomial,coordinateToTower_y]
    _=z := hz.symm

theorem coordinateToTower_surjective : Function.Surjective coordinateToTower := by
  intro z
  refine ⟨towerToCoordinate z,?_⟩
  exact AlgHom.congr_fun coordinateToTower_comp z

def coordinateTowerEquiv : CoordinateRing≃ₐ[ℚ]Tower :=
  AlgEquiv.ofBijective coordinateToTower ⟨coordinateToTower_injective,coordinateToTower_surjective⟩

instance ecProjectiveAffinePolynomialAlgebra : Algebra Poly CoordinateRing := polynomialToCoordinate.toAlgebra

def coordinateTowerPolynomialEquiv : CoordinateRing≃ₐ[Poly]Tower where
  __ := coordinateTowerEquiv.toRingEquiv
  commutes' := coordinateToTower_polynomial

def coordinateBasis : Module.Basis (Fin 2) Poly CoordinateRing :=
  (QuadraticAlgebra.basis ECFunctionField.cubicPolynomial 0).map
    coordinateTowerPolynomialEquiv.symm.toLinearEquiv

@[simp] theorem coordinateTowerPolynomialEquiv_apply (z : CoordinateRing) :
    coordinateTowerPolynomialEquiv z=coordinateToTower z := rfl

theorem coordinateBasis_image (i : Fin 2) :
    coordinateTowerPolynomialEquiv (coordinateBasis i)=QuadraticAlgebra.basis ECFunctionField.cubicPolynomial 0 i := by
  change coordinateTowerPolynomialEquiv
    (coordinateTowerPolynomialEquiv.symm (QuadraticAlgebra.basis ECFunctionField.cubicPolynomial 0 i))=_
  exact coordinateTowerPolynomialEquiv.apply_symm_apply _

theorem coordinateBasis_zero : coordinateBasis 0=1 := by
  apply coordinateTowerPolynomialEquiv.injective
  rw [coordinateBasis_image,QuadraticAlgebra.basis_apply_zero,map_one]
theorem coordinateBasis_one : coordinateBasis 1=ECProjectiveSchemeAffine.y := by
  apply coordinateTowerPolynomialEquiv.injective
  rw [coordinateBasis_image,QuadraticAlgebra.basis_apply_one,
    coordinateTowerPolynomialEquiv_apply,coordinateToTower_y]
  rfl

instance ecProjectiveAffineModuleFinite : Module.Finite Poly CoordinateRing :=
  Module.Finite.of_basis coordinateBasis
end
end Z2Z4Rank6.ECProjectiveAffineFunctionField
