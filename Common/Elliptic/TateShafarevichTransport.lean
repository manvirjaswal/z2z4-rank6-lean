module

public import Common.Elliptic.TateShafarevichLocal

@[expose] public section

/-!
# Natural elliptic point isomorphisms preserve Sha[2]

An isomorphism is specified on points over every characteristic-zero
field and is natural for coefficient embeddings. This supplies Galois
equivariance and compatibility with the local restriction maps.
-/
namespace Common.Elliptic.TateShafarevich
noncomputable section
open WeierstrassCurve
open scoped Classical

structure NaturalPointEquiv (W V : WeierstrassCurve ℚ) where
  equiv : ∀ (K : Type) [Field K] [CharZero K],
    (W.baseChange K).toAffine.Point ≃+ (V.baseChange K).toAffine.Point
  natural : ∀ (K L : Type) [Field K] [CharZero K] [Field L] [CharZero L]
    (f : K→ₐ[ℚ]L) (P : (W.baseChange K).toAffine.Point),
      equiv L (Affine.Point.map (W' := W.toAffine) f P)=
        Affine.Point.map (W' := V.toAffine) f (equiv K P)

namespace NaturalPointEquiv
variable {W V U : WeierstrassCurve ℚ}

def refl (W : WeierstrassCurve ℚ) : NaturalPointEquiv W W where
  equiv _ := AddEquiv.refl _
  natural := by intros; rfl

def ofEq (h : W=V) : NaturalPointEquiv W V := by
  subst V
  exact refl W

def symm (e : NaturalPointEquiv W V) : NaturalPointEquiv V W where
  equiv K := (e.equiv K).symm
  natural := by
    intro K L _ _ _ _ f P
    apply (e.equiv L).injective
    rw [AddEquiv.apply_symm_apply,e.natural,AddEquiv.apply_symm_apply]

def trans (e : NaturalPointEquiv W V) (d : NaturalPointEquiv V U) :
    NaturalPointEquiv W U where
  equiv K := (e.equiv K).trans (d.equiv K)
  natural := by
    intro K L _ _ _ _ f P
    change d.equiv L (e.equiv L (Affine.Point.map f P))=_
    rw [e.natural,d.natural]
    rfl

def geometric (e : NaturalPointEquiv W V) (K : Type) [Field K] [CharZero K] :
    GeometricPoints W K≃+GeometricPoints V K := e.equiv (AlgebraicClosure K)

theorem geometric_action (e : NaturalPointEquiv W V) (K : Type) [Field K] [CharZero K]
    (σ : GaloisGroup K) (P : GeometricPoints W K) :
    e.geometric K (action W K σ P)=action V K σ (e.geometric K P) :=
  e.natural _ _ ((σ.restrictScalars ℚ).toAlgHom) P

def cocycleMap (e : NaturalPointEquiv W V) (K : Type) [Field K] [CharZero K] :
    cocycles W K→+cocycles V K where
  toFun c := ⟨⟨fun σ=>e.geometric K (c.val σ),
    (continuous_of_discreteTopology : Continuous (e.geometric K)).comp c.val.continuous⟩,by
    intro σ τ
    change e.geometric K (c.val (σ*τ))=_
    rw [c.property,map_add,e.geometric_action]
    rfl⟩
  map_zero' := by ext σ; change e.geometric K 0=0; exact map_zero _
  map_add' c d := by
    ext σ
    change e.geometric K (c.val σ+d.val σ)=e.geometric K (c.val σ)+e.geometric K (d.val σ)
    exact map_add _ _ _

theorem coboundaryMap (e : NaturalPointEquiv W V) (K : Type) [Field K] [CharZero K] :
    coboundaries W K≤(coboundaries V K).comap (e.cocycleMap K) := by
  rintro c ⟨P,hP⟩
  refine ⟨e.geometric K P,?_⟩
  intro σ
  change e.geometric K (c.val σ)=_
  rw [hP,map_sub,e.geometric_action]

def cohomologyMap (e : NaturalPointEquiv W V) (K : Type) [Field K] [CharZero K] :
    H1 W K→+H1 V K :=
  QuotientAddGroup.map (coboundaries W K) (coboundaries V K)
    (e.cocycleMap K) (e.coboundaryMap K)

theorem cohomologyMap_inverse (e : NaturalPointEquiv W V) (K : Type)
    [Field K] [CharZero K] (x : H1 W K) :
    e.symm.cohomologyMap K (e.cohomologyMap K x)=x := by
  induction x using QuotientAddGroup.induction_on with
  | H c =>
      change cohomologyClass W K (e.symm.cocycleMap K (e.cocycleMap K c))=
        cohomologyClass W K c
      congr 1
      ext σ
      exact (e.geometric K).symm_apply_apply (c.val σ)

def cohomologyEquiv (e : NaturalPointEquiv W V) (K : Type) [Field K] [CharZero K] :
    H1 W K≃+H1 V K where
  toFun := e.cohomologyMap K
  invFun := e.symm.cohomologyMap K
  left_inv := e.cohomologyMap_inverse K
  right_inv := e.symm.cohomologyMap_inverse K
  map_add' := (e.cohomologyMap K).map_add

theorem localRestriction_cohomologyMap (e : NaturalPointEquiv W V)
    (v : RationalPlace) (f : ClosureEmbedding v) (x : H1 W ℚ) :
    localRestriction V v f (e.cohomologyMap ℚ x)=
      e.cohomologyMap v.completion (localRestriction W v f x) := by
  induction x using QuotientAddGroup.induction_on with
  | H c =>
      change cohomologyClass V v.completion
          (cocycleRestriction V v f (e.cocycleMap ℚ c))=
        cohomologyClass V v.completion
          (e.cocycleMap v.completion (cocycleRestriction W v f c))
      congr 1
      ext σ
      exact (e.natural _ _ f (c.val (galoisRestriction v f σ))).symm

def shaMap (e : NaturalPointEquiv W V) : sha W→+sha V where
  toFun x := ⟨e.cohomologyMap ℚ x.val,by
    rw [mem_sha_iff]
    intro v f
    rw [e.localRestriction_cohomologyMap]
    rw [(mem_sha_iff W x.val).mp x.property v f,map_zero]⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' x y := Subtype.ext (map_add _ _ _)

def shaEquiv (e : NaturalPointEquiv W V) : sha W≃+sha V where
  toFun := e.shaMap
  invFun := e.symm.shaMap
  left_inv x := Subtype.ext (e.cohomologyMap_inverse ℚ x.val)
  right_inv x := Subtype.ext (e.symm.cohomologyMap_inverse ℚ x.val)
  map_add' := e.shaMap.map_add

def shaTwoMap (e : NaturalPointEquiv W V) : shaTwo W→+shaTwo V where
  toFun x := ⟨e.shaMap x.val,by
    change (2 : ℕ) • e.shaMap x.val=0
    rw [←map_nsmul,x.property,map_zero]⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' x y := Subtype.ext (map_add _ _ _)

def shaTwoEquiv (e : NaturalPointEquiv W V) : shaTwo W≃+shaTwo V where
  toFun := e.shaTwoMap
  invFun := e.symm.shaTwoMap
  left_inv x := Subtype.ext (Subtype.ext (e.cohomologyMap_inverse ℚ x.val.val))
  right_inv x := Subtype.ext (Subtype.ext (e.symm.cohomologyMap_inverse ℚ x.val.val))
  map_add' := e.shaTwoMap.map_add

theorem shaTwo_subsingleton (e : NaturalPointEquiv W V) (h : Subsingleton (shaTwo V)) :
    Subsingleton (shaTwo W) := by
  let := h
  exact Function.Injective.subsingleton e.shaTwoEquiv.injective

end NaturalPointEquiv
end
end Common.Elliptic.TateShafarevich
