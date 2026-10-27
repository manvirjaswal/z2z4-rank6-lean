import Common.Elliptic.WeierstrassScheme
import Common.AlgebraicGeometry.ProjValuedPoint

/-!
# The Weierstrass point at infinity over every field

The homogeneous evaluation (0:1:0) defines a field-valued point
of the complete quotient Proj, compatible with its structure map.
Reference: Silverman, The Arithmetic of Elliptic Curves, second edition,
Chapter III, Section 1, pp. 42–46. The quotient and Proj construction is the one used in
WeierstrassScheme.
-/
namespace WeierstrassScheme.Infinity
noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial
set_option backward.isDefEq.respectTransparency false
variable {K : Type} [Field K] (W : WeierstrassCurve K)

def evaluation : CoordinateRing W →ₐ[K] K :=
  Ideal.Quotient.liftₐ (definingIdeal W) (MvPolynomial.aeval ![0,1,0]) (by
    have hker : definingIdeal W ≤ RingHom.ker
        (MvPolynomial.aeval ![(0:K),1,0]).toRingHom := by
      apply Ideal.span_le.mpr
      rintro p (rfl : p=relation W)
      change (MvPolynomial.aeval ![(0:K),1,0]) (relation W)=0
      simp [relation]
    intro p hp
    exact hker hp)

@[simp] theorem evaluation_coordinate (i : Fin 3) :
    evaluation W (coordinate W i)=![(0:K),1,0] i := by
  simp [evaluation,coordinate]

def point : Spec (CommRingCat.of K) ⟶ scheme W :=
  ProjValuedPoint.point (grading W) (evaluation W)
    (by decide : 0<1) (coordinate W 1) (coordinate_degree W 1) (by simp)

theorem point_over : point W≫structureMap W=𝟙 (Spec (CommRingCat.of K)) := by
  simpa [point,structureMap,ProjFieldPoint.structureMap] using
    ProjValuedPoint.point_over (grading W) (evaluation W)
      (by decide : 0<1) (coordinate W 1) (coordinate_degree W 1) (by simp)

end
end WeierstrassScheme.Infinity
