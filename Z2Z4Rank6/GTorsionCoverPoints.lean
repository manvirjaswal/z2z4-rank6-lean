module

public import Z2Z4Rank6.GTorsionCoverInfinity
public import Z2Z4Rank6.GTorsionCoverEquations
public import Z2Z4Rank6.GTorsionCoverProjectiveCharts

@[expose] public section

/-! The printed affine double-cover points and their Spec points. -/
namespace Z2Z4Rank6.GTorsionCoverPoints
noncomputable section
open scoped Classical
open AlgebraicGeometry CategoryTheory
open GTorsionCoverPolynomialData GTorsionCoverEquations

@[ext] structure SquareLift (ε : Bool) where
  c : GQuarticPoint
  r : ℚ
  r_sq : r^2=TorsionHyperelliptic.sign ε*a c.m*b c.m

abbrev Source := Spec (CommRingCat.of ℚ)
def sourcePoint : Source := ⟨⊥,inferInstance⟩

def affinePoint (ε : Bool) (f : GTorsionCoverAffine.CoordinateRing ε→ₐ[ℚ]ℚ) : SquareLift ε where
  c := {
    m := f (GTorsionCoverAffine.m ε)
    eta := f (GTorsionCoverAffine.u ε)
    equation := by
      have h := congrArg f (GTorsionCoverAffine.root_sq ε 0)
      dsimp only [GTorsionCoverAffine.radicand] at h
      rw [aeval_affine] at h
      simpa [GTorsionCoverEquations.binary,gQuartic,map_ofNat] using h }
  r := f (GTorsionCoverAffine.r ε)
  r_sq := by
    have h := congrArg f (GTorsionCoverAffine.root_sq ε 1)
    dsimp only [GTorsionCoverAffine.radicand] at h
    rw [aeval_affine] at h
    simpa [GTorsionCoverEquations.binary,HeightInvariantForms.binaryA,
      HeightInvariantForms.binaryB,a,b,map_ofNat] using h

def evaluation (ε : Bool) (P : SquareLift ε) : GTorsionCoverAffine.CoordinateRing ε→ₐ[ℚ]ℚ :=
  DoubleSquareCover.lift (affineRadicand ε) P.c.m ![P.c.eta,P.r] (by
    intro i
    rw [aeval_affine]
    fin_cases i
    · simpa [binary,gQuartic] using P.c.equation
    · simpa [binary,HeightInvariantForms.binaryA,HeightInvariantForms.binaryB,a,b] using P.r_sq)

@[simp] theorem evaluation_m (ε : Bool) (P : SquareLift ε) :
    evaluation ε P (GTorsionCoverAffine.m ε)=P.c.m := by simp [evaluation,GTorsionCoverAffine.m]
@[simp] theorem evaluation_u (ε : Bool) (P : SquareLift ε) :
    evaluation ε P (GTorsionCoverAffine.u ε)=P.c.eta := by simp [evaluation,GTorsionCoverAffine.u]
@[simp] theorem evaluation_r (ε : Bool) (P : SquareLift ε) :
    evaluation ε P (GTorsionCoverAffine.r ε)=P.r := by simp [evaluation,GTorsionCoverAffine.r]

@[simp] theorem affinePoint_evaluation (ε : Bool) (P : SquareLift ε) :
    affinePoint ε (evaluation ε P)=P := by ext <;> simp [affinePoint]

@[simp] theorem evaluation_affinePoint (ε : Bool) (f : GTorsionCoverAffine.CoordinateRing ε→ₐ[ℚ]ℚ) :
    evaluation ε (affinePoint ε f)=f := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i
  · change evaluation ε (affinePoint ε f) (GTorsionCoverAffine.m ε)=f (GTorsionCoverAffine.m ε)
    simp [affinePoint]
  · change evaluation ε (affinePoint ε f) (GTorsionCoverAffine.u ε)=f (GTorsionCoverAffine.u ε)
    simp [affinePoint]
  · change evaluation ε (affinePoint ε f) (GTorsionCoverAffine.r ε)=f (GTorsionCoverAffine.r ε)
    simp [affinePoint]

def affineRationalPointEquiv (ε : Bool) : SquareLift ε≃(Source⟶GTorsionCoverAffine.scheme ε) where
  toFun P := Spec.map (CommRingCat.ofHom (evaluation ε P).toRingHom)
  invFun p := affinePoint ε (GTorsionCoverProjectiveCharts.rationalAlgHom (Spec.preimage p).hom)
  left_inv P := by
    change affinePoint ε (GTorsionCoverProjectiveCharts.rationalAlgHom (Spec.preimage
      (Spec.map (CommRingCat.ofHom (evaluation ε P).toRingHom))).hom)=P
    rw [Spec.preimage_map]
    exact affinePoint_evaluation ε P
  right_inv p := by
    change Spec.map (CommRingCat.ofHom
      (evaluation ε (affinePoint ε (GTorsionCoverProjectiveCharts.rationalAlgHom (Spec.preimage p).hom))).toRingHom)=p
    rw [evaluation_affinePoint]
    exact Spec.map_preimage p

end
end Z2Z4Rank6.GTorsionCoverPoints
