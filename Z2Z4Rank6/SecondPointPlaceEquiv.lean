import Z2Z4Rank6.SecondPointPlaceIntegral

/-! Nonbranch G2 rational points are exactly the normalized rational
Laurent places of its constructed degree-eight function field. -/
namespace Z2Z4Rank6.SecondPointPlaceEquiv
noncomputable section
open SecondFamily

def fromPoint (P : Point) : Place where
  parameter:=P.val.W
  embedding:=SecondFunctionFieldPointPlace.embeddingAlgHom P
  rigid:=SecondFunctionFieldPointPlace.embeddingAlgHom_parameter P
@[simp] theorem fromPoint_parameter (P : Point) : (fromPoint P).parameter=P.val.W := rfl

theorem toPoint_fromPoint (P : Point) : toPoint (fromPoint P)=P := by
  apply Subtype.ext
  apply G2Point.ext
  · rfl
  · have he : algebraMap PS LS (s1Series (fromPoint P))=
        algebraMap PS LS (SecondFunctionFieldPointPlace.s1Series P) := by
      rw [s1Series_image]
      exact SecondFunctionFieldPointPlace.embedding_s1 P
    have he' := (IsFractionRing.injective PS LS) he
    change PowerSeries.constantCoeff (s1Series (fromPoint P))=P.val.s1
    rw [he',SecondFunctionFieldPointPlace.s1Series_constant]
  · have he : algebraMap PS LS (s2Series (fromPoint P))=
        algebraMap PS LS (SecondFunctionFieldPointPlace.s2Series P) := by
      rw [s2Series_image]
      exact SecondFunctionFieldPointPlace.embedding_s2 P
    have he' := (IsFractionRing.injective PS LS) he
    change PowerSeries.constantCoeff (s2Series (fromPoint P))=P.val.s2
    rw [he',SecondFunctionFieldPointPlace.s2Series_constant]
  · have he : algebraMap PS LS (s3Series (fromPoint P))=
        algebraMap PS LS (SecondFunctionFieldPointPlace.s3Series P) := by
      rw [s3Series_image]
      exact SecondFunctionFieldPointPlace.embedding_s3 P
    have he' := (IsFractionRing.injective PS LS) he
    change PowerSeries.constantCoeff (s3Series (fromPoint P))=P.val.s3
    rw [he',SecondFunctionFieldPointPlace.s3Series_constant]

theorem forward_s1Series (v : Place) :
    SecondFunctionFieldPointPlace.s1Series (toPoint v)=s1Series v := by
  apply powerSeries_square_root_unique
  · rw [(SecondFunctionFieldPointPlace.s1Series_spec (toPoint v)).1,s1Series_sq]
    rfl
  · rw [SecondFunctionFieldPointPlace.s1Series_constant]
    rfl
  · exact s1_constant_ne_zero v

theorem forward_s2Series (v : Place) :
    SecondFunctionFieldPointPlace.s2Series (toPoint v)=s2Series v := by
  apply powerSeries_square_root_unique
  · rw [(SecondFunctionFieldPointPlace.s2Series_spec (toPoint v)).1,s2Series_sq]
    rfl
  · rw [SecondFunctionFieldPointPlace.s2Series_constant]
    rfl
  · exact s2_constant_ne_zero v

theorem forward_s3Series (v : Place) :
    SecondFunctionFieldPointPlace.s3Series (toPoint v)=s3Series v := by
  apply powerSeries_square_root_unique
  · rw [(SecondFunctionFieldPointPlace.s3Series_spec (toPoint v)).1,s3Series_sq]
    rfl
  · rw [SecondFunctionFieldPointPlace.s3Series_constant]
    rfl
  · exact s3_constant_ne_zero v

theorem functionField_algHom_ext {L : Type*} [Field L] [Algebra ℚ L]
    (f g : SecondFunctionField.K→ₐ[ℚ]L)
    (hW : f SecondFunctionField.W=g SecondFunctionField.W)
    (h1 : f SecondFunctionField.s1=g SecondFunctionField.s1)
    (h2 : f SecondFunctionField.s2=g SecondFunctionField.s2)
    (h3 : f SecondFunctionField.s3=g SecondFunctionField.s3) : f=g := by
  apply AlgHom.ext
  intro z
  have hz : z∈IntermediateField.adjoin ℚ
      ({SecondFunctionField.W,SecondFunctionField.s1,SecondFunctionField.s2,
        SecondFunctionField.s3}:Set SecondFunctionField.K) := by
    rw [SecondFunctionField.field_adjoin_coordinates_eq_top]
    trivial
  induction hz using IntermediateField.adjoin_induction with
  | mem z hz =>
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hz
    rcases hz with rfl|rfl|rfl|rfl
    · exact hW
    · exact h1
    · exact h2
    · exact h3
  | algebraMap q => rw [f.commutes,g.commutes]
  | add x y hx hy ihx ihy => simp only [map_add,ihx,ihy]
  | inv x hx ih => simp only [map_inv₀,ih]
  | mul x y hx hy ihx ihy => simp only [map_mul,ihx,ihy]

theorem fromPoint_toPoint (v : Place) : fromPoint (toPoint v)=v := by
  apply RigidRationalPlace.embedding_injective
  apply functionField_algHom_ext
  · change SecondFunctionFieldPointPlace.embedding (toPoint v) SecondFunctionField.W=
      v.embedding SecondFunctionField.W
    rw [SecondFunctionFieldPointPlace.embedding_W,embedding_W]
    rfl
  · change SecondFunctionFieldPointPlace.embedding (toPoint v) SecondFunctionField.s1=
      v.embedding SecondFunctionField.s1
    rw [SecondFunctionFieldPointPlace.embedding_s1,forward_s1Series,s1Series_image]
  · change SecondFunctionFieldPointPlace.embedding (toPoint v) SecondFunctionField.s2=
      v.embedding SecondFunctionField.s2
    rw [SecondFunctionFieldPointPlace.embedding_s2,forward_s2Series,s2Series_image]
  · change SecondFunctionFieldPointPlace.embedding (toPoint v) SecondFunctionField.s3=
      v.embedding SecondFunctionField.s3
    rw [SecondFunctionFieldPointPlace.embedding_s3,forward_s3Series,s3Series_image]

/-- The entire normalized-place space, with no unproved solubility or
regularity condition, is parametrized by the nonbranch G2 points. -/
def equiv : Point ≃ RigidRationalPlace SecondFunctionField.K where
  toFun:=fromPoint
  invFun:=toPoint
  left_inv:=toPoint_fromPoint
  right_inv:=fromPoint_toPoint
end
end Z2Z4Rank6.SecondPointPlaceEquiv
