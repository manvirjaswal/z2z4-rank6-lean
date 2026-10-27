module

public import Z2Z4Rank6.ThirdTwistCoverInfinity
public import Z2Z4Rank6.ThirdTwistCoverEquations
public import Z2Z4Rank6.ThirdTwistCoverProjectiveCharts

@[expose] public section

/-! Affine points of the third-twist genus-five base and their Spec maps. -/
namespace Z2Z4Rank6.ThirdTwistCoverPoints
noncomputable section
open scoped Classical
open AlgebraicGeometry CategoryTheory ThirdTwistCoverPolynomialData ThirdTwistCoverEquations

@[ext] structure Point where
  m : ℚ
  u : ℚ
  v : ℚ
  w : ℚ
  u_sq : u^2=5*(3*m^2+242)
  v_sq : v^2=5*(2*m^2+243)
  w_sq : w^2=4*m^2+45

abbrev Source := Spec (CommRingCat.of ℚ)
def sourcePoint : Source := ⟨⊥,inferInstance⟩

def affinePoint (f : ThirdTwistCoverAffine.CoordinateRing→ₐ[ℚ]ℚ) : Point where
  m := f ThirdTwistCoverAffine.m
  u := f ThirdTwistCoverAffine.u
  v := f ThirdTwistCoverAffine.v
  w := f ThirdTwistCoverAffine.r
  u_sq := by
    have h := congrArg f (ThirdTwistCoverAffine.root_sq 0)
    dsimp only [ThirdTwistCoverAffine.radicand] at h
    rw [aeval_affine] at h
    norm_num [binary,map_ofNat] at h
    linear_combination h
  v_sq := by
    have h := congrArg f (ThirdTwistCoverAffine.root_sq 1)
    dsimp only [ThirdTwistCoverAffine.radicand] at h
    rw [aeval_affine] at h
    norm_num [binary,map_ofNat] at h
    linear_combination h
  w_sq := by
    have h := congrArg f (ThirdTwistCoverAffine.root_sq 2)
    dsimp only [ThirdTwistCoverAffine.radicand] at h
    rw [aeval_affine] at h
    simpa [binary,map_ofNat] using h

def evaluation (P : Point) : ThirdTwistCoverAffine.CoordinateRing→ₐ[ℚ]ℚ :=
  TripleSquareCover.lift affineRadicand P.m ![P.u,P.v,P.w] (by
    intro i
    rw [aeval_affine]
    fin_cases i
    · dsimp [binary]; linear_combination P.u_sq
    · dsimp [binary]; linear_combination P.v_sq
    · simpa [binary] using P.w_sq)

@[simp] theorem evaluation_m (P : Point) : evaluation P ThirdTwistCoverAffine.m=P.m := by
  simp [evaluation,ThirdTwistCoverAffine.m]
@[simp] theorem evaluation_u (P : Point) : evaluation P ThirdTwistCoverAffine.u=P.u := by
  simp [evaluation,ThirdTwistCoverAffine.u]
@[simp] theorem evaluation_v (P : Point) : evaluation P ThirdTwistCoverAffine.v=P.v := by
  simp [evaluation,ThirdTwistCoverAffine.v]
@[simp] theorem evaluation_r (P : Point) : evaluation P ThirdTwistCoverAffine.r=P.w := by
  simp [evaluation,ThirdTwistCoverAffine.r]

@[simp] theorem affinePoint_evaluation (P : Point) : affinePoint (evaluation P)=P := by
  ext <;> simp [affinePoint]

@[simp] theorem evaluation_affinePoint (f : ThirdTwistCoverAffine.CoordinateRing→ₐ[ℚ]ℚ) :
    evaluation (affinePoint f)=f := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i
  · change evaluation (affinePoint f) ThirdTwistCoverAffine.m=f ThirdTwistCoverAffine.m
    simp [affinePoint]
  · change evaluation (affinePoint f) ThirdTwistCoverAffine.u=f ThirdTwistCoverAffine.u
    simp [affinePoint]
  · change evaluation (affinePoint f) ThirdTwistCoverAffine.v=f ThirdTwistCoverAffine.v
    simp [affinePoint]
  · change evaluation (affinePoint f) ThirdTwistCoverAffine.r=f ThirdTwistCoverAffine.r
    simp [affinePoint]

def affineRationalPointEquiv : Point≃(Source⟶ThirdTwistCoverAffine.scheme) where
  toFun P := Spec.map (CommRingCat.ofHom (evaluation P).toRingHom)
  invFun p := affinePoint (ThirdTwistCoverProjectiveCharts.rationalAlgHom (Spec.preimage p).hom)
  left_inv P := by
    change affinePoint (ThirdTwistCoverProjectiveCharts.rationalAlgHom (Spec.preimage
      (Spec.map (CommRingCat.ofHom (evaluation P).toRingHom))).hom)=P
    rw [Spec.preimage_map]
    exact affinePoint_evaluation P
  right_inv p := by
    change Spec.map (CommRingCat.ofHom
      (evaluation (affinePoint (ThirdTwistCoverProjectiveCharts.rationalAlgHom (Spec.preimage p).hom))).toRingHom)=p
    rw [evaluation_affinePoint]
    exact Spec.map_preimage p
end
end Z2Z4Rank6.ThirdTwistCoverPoints
