module

public import Z2Z4Rank6.RigidRationalPlace
public import Z2Z4Rank6.LaurentRootIntegral
public import Z2Z4Rank6.FunctionFieldPointPlace

@[expose] public section

/-!
# All normalized rational places of Q(C) are C points

The converse to the explicit point-place construction is proved here.
The two root images are integral because their squares are power series;
constants reconstruct a rational CPoint. Prescribed nonzero constants
fix the two roots, and m,u,v generate the entire field.
-/
namespace Z2Z4Rank6.CPointPlaceEquiv
noncomputable section
open Polynomial

abbrev PS := PowerSeries ℚ
abbrev LS := LaurentSeries ℚ
abbrev Place := RigidRationalPlace FunctionField.K

def parameterSeries (v : Place) : PS := UnivariateLocal.mSeries v.parameter

@[simp] theorem parameterSeries_constant (v : Place) :
    PowerSeries.constantCoeff (parameterSeries v)=v.parameter := by
  simp [parameterSeries]

@[simp] theorem embedding_m (v : Place) :
    v.embedding FunctionField.m=algebraMap PS LS (parameterSeries v) := v.rigid

theorem embedding_u_sq (v : Place) :
    (v.embedding FunctionField.u)^2=algebraMap PS LS (q1 ((parameterSeries v)^2)) := by
  have h := congrArg v.embedding FunctionField.u_sq
  simpa only [q1,map_pow,map_mul,map_add,map_ofNat,embedding_m] using h

theorem embedding_v_sq (v : Place) :
    (v.embedding FunctionField.v)^2=algebraMap PS LS (q2 ((parameterSeries v)^2)) := by
  have h := congrArg v.embedding FunctionField.v_sq
  simpa only [q2,map_pow,map_mul,map_add,map_ofNat,embedding_m] using h

def uSeries (v : Place) : PS := Classical.choose
  (exists_powerSeries_of_square (v.embedding FunctionField.u)
    (q1 ((parameterSeries v)^2)) (embedding_u_sq v))
def vSeries (v : Place) : PS := Classical.choose
  (exists_powerSeries_of_square (v.embedding FunctionField.v)
    (q2 ((parameterSeries v)^2)) (embedding_v_sq v))

theorem uSeries_image (v : Place) : algebraMap PS LS (uSeries v)=v.embedding FunctionField.u :=
  Classical.choose_spec (exists_powerSeries_of_square (v.embedding FunctionField.u)
    (q1 ((parameterSeries v)^2)) (embedding_u_sq v))
theorem vSeries_image (v : Place) : algebraMap PS LS (vSeries v)=v.embedding FunctionField.v :=
  Classical.choose_spec (exists_powerSeries_of_square (v.embedding FunctionField.v)
    (q2 ((parameterSeries v)^2)) (embedding_v_sq v))

theorem uSeries_sq (v : Place) : (uSeries v)^2=q1 ((parameterSeries v)^2) := by
  apply IsFractionRing.injective PS LS
  rw [map_pow,uSeries_image,embedding_u_sq]

theorem vSeries_sq (v : Place) : (vSeries v)^2=q2 ((parameterSeries v)^2) := by
  apply IsFractionRing.injective PS LS
  rw [map_pow,vSeries_image,embedding_v_sq]

def toCPoint (v : Place) : CPoint where
  m:=v.parameter
  u:=PowerSeries.constantCoeff (uSeries v)
  v:=PowerSeries.constantCoeff (vSeries v)
  u_sq:=by
    have h := congrArg PowerSeries.constantCoeff (uSeries_sq v)
    simpa [q1,map_ofNat] using h
  v_sq:=by
    have h := congrArg PowerSeries.constantCoeff (vSeries_sq v)
    simpa [q2,map_ofNat] using h

@[simp] theorem toCPoint_m (v : Place) : (toCPoint v).m=v.parameter := rfl

def fromCPoint (c : CPoint) : Place where
  parameter:=c.m
  embedding:=FunctionFieldPointPlace.embeddingAlgHom c
  rigid:=FunctionFieldPointPlace.embeddingAlgHom_parameter c

@[simp] theorem fromCPoint_parameter (c : CPoint) : (fromCPoint c).parameter=c.m := rfl

theorem toCPoint_fromCPoint (c : CPoint) : toCPoint (fromCPoint c)=c := by
  apply CPoint.ext
  · rfl
  · have he : algebraMap PS LS (uSeries (fromCPoint c))=
        algebraMap PS LS (FunctionFieldPointPlace.uSeries c) := by
      rw [uSeries_image]
      exact FunctionFieldPointPlace.embedding_u c
    have he' := (IsFractionRing.injective PS LS) he
    change PowerSeries.constantCoeff (uSeries (fromCPoint c))=c.u
    rw [he',FunctionFieldPointPlace.uSeries_constant]
  · have he : algebraMap PS LS (vSeries (fromCPoint c))=
        algebraMap PS LS (FunctionFieldPointPlace.vSeries c) := by
      rw [vSeries_image]
      exact FunctionFieldPointPlace.embedding_v c
    have he' := (IsFractionRing.injective PS LS) he
    change PowerSeries.constantCoeff (vSeries (fromCPoint c))=c.v
    rw [he',FunctionFieldPointPlace.vSeries_constant]

theorem forward_uSeries (v : Place) :
    FunctionFieldPointPlace.uSeries (toCPoint v)=uSeries v := by
  apply powerSeries_square_root_unique
  · rw [(FunctionFieldPointPlace.uSeries_spec (toCPoint v)).1,uSeries_sq]
    rfl
  · rw [FunctionFieldPointPlace.uSeries_constant]
    rfl
  · exact (toCPoint v).u_ne_zero

theorem forward_vSeries (v : Place) :
    FunctionFieldPointPlace.vSeries (toCPoint v)=vSeries v := by
  apply powerSeries_square_root_unique
  · rw [(FunctionFieldPointPlace.vSeries_spec (toCPoint v)).1,vSeries_sq]
    rfl
  · rw [FunctionFieldPointPlace.vSeries_constant]
    rfl
  · exact (toCPoint v).v_ne_zero

theorem functionField_algHom_ext {L : Type*} [Field L] [Algebra ℚ L]
    (f g : FunctionField.K→ₐ[ℚ]L)
    (hm : f FunctionField.m=g FunctionField.m)
    (hu : f FunctionField.u=g FunctionField.u)
    (hv : f FunctionField.v=g FunctionField.v) : f=g := by
  apply AlgHom.ext
  intro z
  have hz : z∈IntermediateField.adjoin ℚ
      ({FunctionField.m,FunctionField.u,FunctionField.v} : Set FunctionField.K) := by
    rw [FunctionField.field_adjoin_coordinates_eq_top]
    trivial
  induction hz using IntermediateField.adjoin_induction with
  | mem z hz =>
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl
    · exact hm
    · exact hu
    · exact hv
  | algebraMap q => rw [f.commutes,g.commutes]
  | add x y hx hy ihx ihy => simp only [map_add,ihx,ihy]
  | inv x hx ih => simp only [map_inv₀,ih]
  | mul x y hx hy ihx ihy => simp only [map_mul,ihx,ihy]

theorem fromCPoint_toCPoint (v : Place) : fromCPoint (toCPoint v)=v := by
  apply RigidRationalPlace.embedding_injective
  apply functionField_algHom_ext
  · change FunctionFieldPointPlace.embedding (toCPoint v) FunctionField.m=v.embedding FunctionField.m
    rw [FunctionFieldPointPlace.embedding_m,embedding_m]
    rfl
  · change FunctionFieldPointPlace.embedding (toCPoint v) FunctionField.u=v.embedding FunctionField.u
    rw [FunctionFieldPointPlace.embedding_u,forward_uSeries,uSeries_image]
  · change FunctionFieldPointPlace.embedding (toCPoint v) FunctionField.v=v.embedding FunctionField.v
    rw [FunctionFieldPointPlace.embedding_v,forward_vSeries,vSeries_image]

/-- Every normalized rational Laurent place is uniquely the place of
a rational C point, with the same rational parameter. -/
def equiv : CPoint ≃ RigidRationalPlace FunctionField.K where
  toFun:=fromCPoint
  invFun:=toCPoint
  left_inv:=toCPoint_fromCPoint
  right_inv:=fromCPoint_toCPoint

end
end Z2Z4Rank6.CPointPlaceEquiv
