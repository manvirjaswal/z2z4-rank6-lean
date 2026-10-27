import Z2Z4Rank6.SecondTorsionCoverInfinity
import Z2Z4Rank6.ProjectiveBaseSchemeCharts
import Z2Z4Rank6.SecondTorsionSquareLiftData

/-! Spec Q-points of the second signed projective torsion covers are
exactly SecondTorsionHyperelliptic.SquareLift. The affine parameter is s1=t,
and W=t²; no G2 coordinate is forgotten. Infinity would force U²=29.
Source: Jaswal, Theorem 8.1(c), DOI 10.5281/zenodo.23437117. -/
namespace Z2Z4Rank6.SecondTorsionCoverProjectiveRationalPoints
noncomputable section
open scoped Classical
open AlgebraicGeometry CategoryTheory
open SecondTorsionCoverPolynomialData
open SecondTorsionHyperelliptic SecondFamily
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

def rationalAlgHom {A B:Type*} [CommRing A] [CommRing B] [Algebra ℚ A] [Algebra ℚ B]
    (f:A→+*B) : A→ₐ[ℚ]B := ProjectiveBaseSchemeCharts.rationalAlgHom f

abbrev Source := Spec (CommRingCat.of ℚ)
def sourcePoint : Source := ⟨⊥,inferInstance⟩

theorem affine_u_sq (ε:Bool) : (SecondTorsionCoverAffine.u ε)^2=
    29*((SecondTorsionCoverAffine.m ε)^2-
      algebraMap ℚ (SecondTorsionCoverAffine.CoordinateRing ε) (beta:ℚ)) := by
  have h := SecondTorsionCoverAffine.root_sq ε 0
  norm_num [SecondTorsionCoverAffine.radicand,affineRadicand] at h
  norm_num only [map_ofNat] at h
  linear_combination h

theorem affine_v_sq (ε:Bool) : (SecondTorsionCoverAffine.v ε)^2=
    algebraMap ℚ (SecondTorsionCoverAffine.CoordinateRing ε) (-29*(beta:ℚ))*
      ((SecondTorsionCoverAffine.m ε)^2-
        algebraMap ℚ (SecondTorsionCoverAffine.CoordinateRing ε) (gamma:ℚ)) := by
  have h := SecondTorsionCoverAffine.root_sq ε 1
  norm_num [SecondTorsionCoverAffine.radicand,affineRadicand] at h
  norm_num only [map_ofNat] at h
  simp only [map_mul,map_neg,map_ofNat]
  linear_combination h

theorem affine_r_sq (ε:Bool) : (SecondTorsionCoverAffine.r ε)^2=
    -algebraMap ℚ (SecondTorsionCoverAffine.CoordinateRing ε) (SecondTorsionHyperelliptic.sign ε)*
      ((SecondTorsionCoverAffine.m ε)^2-1)*
      ((SecondTorsionCoverAffine.m ε)^2-
        algebraMap ℚ (SecondTorsionCoverAffine.CoordinateRing ε) ((lambda:ℚ)^2)) := by
  have h := SecondTorsionCoverAffine.root_sq ε 2
  norm_num [SecondTorsionCoverAffine.radicand,affineRadicand] at h
  simp only [map_pow]
  linear_combination h

def affinePoint (ε:Bool) (f:SecondTorsionCoverAffine.CoordinateRing ε→ₐ[ℚ]ℚ) : SquareLift ε where
  c:={
    W:=(f (SecondTorsionCoverAffine.m ε))^2
    s1:=f (SecondTorsionCoverAffine.m ε)
    s2:=f (SecondTorsionCoverAffine.u ε)
    s3:=f (SecondTorsionCoverAffine.v ε)
    s1_sq:=rfl
    s2_sq:=by
      have h := congrArg f (affine_u_sq ε)
      simpa only [qA,map_mul,map_sub,map_pow,map_ofNat,AlgHom.commutes,
        Algebra.algebraMap_self_apply] using h
    s3_sq:=by
      have h := congrArg f (affine_v_sq ε)
      simpa only [qB,map_mul,map_sub,map_pow,map_ofNat,AlgHom.commutes,
        Algebra.algebraMap_self_apply] using h}
  r:=f (SecondTorsionCoverAffine.r ε)
  r_sq:=by
    have h := congrArg f (affine_r_sq ε)
    simp only [map_mul,AlgHom.commutes,Algebra.algebraMap_self_apply,map_pow,
      map_sub,map_neg,map_one] at h
    dsimp [V]
    linear_combination h

def evaluation (ε:Bool) (P:SquareLift ε) : SecondTorsionCoverAffine.CoordinateRing ε→ₐ[ℚ]ℚ :=
  TripleSquareCover.lift (affineRadicand ε) P.c.s1 ![P.c.s2,P.c.s3,P.r] (by
    intro i
    fin_cases i
    · norm_num [affineRadicand]
      have h := P.c.s2_sq
      rw [←P.c.s1_sq] at h
      exact h
    · norm_num [affineRadicand]
      have h := P.c.s3_sq
      rw [←P.c.s1_sq] at h
      dsimp [qB] at h
      linear_combination h
    · norm_num [affineRadicand]
      have h := P.r_sq
      rw [←P.c.s1_sq] at h
      dsimp [V] at h
      linear_combination h)

@[simp] theorem evaluation_m (ε:Bool) (P:SquareLift ε) : evaluation ε P (SecondTorsionCoverAffine.m ε)=P.c.s1 := by
  simp [evaluation,SecondTorsionCoverAffine.m]
@[simp] theorem evaluation_u (ε:Bool) (P:SquareLift ε) : evaluation ε P (SecondTorsionCoverAffine.u ε)=P.c.s2 := by
  simp [evaluation,SecondTorsionCoverAffine.u]
@[simp] theorem evaluation_v (ε:Bool) (P:SquareLift ε) : evaluation ε P (SecondTorsionCoverAffine.v ε)=P.c.s3 := by
  simp [evaluation,SecondTorsionCoverAffine.v]
@[simp] theorem evaluation_r (ε:Bool) (P:SquareLift ε) : evaluation ε P (SecondTorsionCoverAffine.r ε)=P.r := by
  simp [evaluation,SecondTorsionCoverAffine.r]

@[simp] theorem affinePoint_evaluation (ε:Bool) (P:SquareLift ε) : affinePoint ε (evaluation ε P)=P := by
  ext <;> simp [affinePoint,P.c.s1_sq]

@[simp] theorem evaluation_affinePoint (ε:Bool) (f:SecondTorsionCoverAffine.CoordinateRing ε→ₐ[ℚ]ℚ) :
    evaluation ε (affinePoint ε f)=f := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i
  · change evaluation ε (affinePoint ε f) (SecondTorsionCoverAffine.m ε)=f (SecondTorsionCoverAffine.m ε)
    simp [affinePoint]
  · change evaluation ε (affinePoint ε f) (SecondTorsionCoverAffine.u ε)=f (SecondTorsionCoverAffine.u ε)
    simp [affinePoint]
  · change evaluation ε (affinePoint ε f) (SecondTorsionCoverAffine.v ε)=f (SecondTorsionCoverAffine.v ε)
    simp [affinePoint]
  · change evaluation ε (affinePoint ε f) (SecondTorsionCoverAffine.r ε)=f (SecondTorsionCoverAffine.r ε)
    simp [affinePoint]

def affineRationalPointEquiv (ε:Bool) : SquareLift ε≃(Source⟶SecondTorsionCoverAffine.scheme ε) where
  toFun P:=Spec.map (CommRingCat.ofHom (evaluation ε P).toRingHom)
  invFun p:=affinePoint ε (rationalAlgHom (Spec.preimage p).hom)
  left_inv P:=by
    change affinePoint ε (rationalAlgHom (Spec.preimage
      (Spec.map (CommRingCat.ofHom (evaluation ε P).toRingHom))).hom)=P
    rw [Spec.preimage_map]
    exact affinePoint_evaluation ε P
  right_inv p:=by
    change Spec.map (CommRingCat.ofHom
      (evaluation ε (affinePoint ε (rationalAlgHom (Spec.preimage p).hom))).toRingHom)=p
    rw [evaluation_affinePoint]
    exact Spec.map_preimage p


end
end Z2Z4Rank6.SecondTorsionCoverProjectiveRationalPoints
