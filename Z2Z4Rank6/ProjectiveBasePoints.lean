module

public import Z2Z4Rank6.BaseCurve
public import Mathlib.LinearAlgebra.Projectivization.Basic

@[expose] public section

/-!
# Rational projective points on C

The intersection u²=15m²+1210z², v²=10m²+1215z² is defined in Mathlib's
Projectivization ℚ (Fin 4→ℚ). Its equations descend under scaling. There are
no rational points with z=0, and normalization gives an equivalence
with the affine CPoint type. This is a projective-coordinate statement.
Source: Jaswal, DOI 10.5281/zenodo.23437117.
-/
namespace Z2Z4Rank6.ProjectiveBasePoints
noncomputable section

abbrev Coordinates := Fin 4→ℚ
abbrev Space := Projectivization ℚ Coordinates

def quadric1 (v : Coordinates) : ℚ := v 1^2-15*v 0^2-1210*v 3^2
def quadric2 (v : Coordinates) : ℚ := v 2^2-10*v 0^2-1215*v 3^2
def Equations (v : Coordinates) : Prop := quadric1 v=0 ∧ quadric2 v=0

theorem quadric1_smul (t : ℚ) (v : Coordinates) : quadric1 (t • v)=t^2*quadric1 v := by
  simp only [quadric1,Pi.smul_apply,smul_eq_mul]
  ring

theorem quadric2_smul (t : ℚ) (v : Coordinates) : quadric2 (t • v)=t^2*quadric2 v := by
  simp only [quadric2,Pi.smul_apply,smul_eq_mul]
  ring

theorem equations_smul_iff (t : ℚ) (ht : t≠0) (v : Coordinates) :
    Equations (t • v)↔Equations v := by
  simp only [Equations,quadric1_smul,quadric2_smul,mul_eq_zero,pow_eq_zero_iff (by decide : (2:ℕ)≠0),ht,false_or]

/-- The homogeneous equations descended to projective space. -/
def OnCurve : Space→Prop :=
  Projectivization.lift (fun v : {v : Coordinates // v≠0} => Equations v.val) (by
    intro a b t h
    have ht : t≠0 := by
      intro hz
      apply a.property
      simpa only [hz,zero_smul] using h
    apply propext
    change Equations a.val↔Equations b.val
    rw [h]
    exact equations_smul_iff t ht b.val)

@[simp] theorem onCurve_mk (v : Coordinates) (hv : v≠0) :
    OnCurve (Projectivization.mk ℚ v hv)↔Equations v := Iff.rfl

/-- Points of the homogeneous intersection, as a subtype of Mathlib's
projective space rather than a separate quotient. -/
abbrev Point := {P : Space // OnCurve P}

theorem representative_equations (P : Point) : Equations P.val.rep := by
  have h := P.property
  rw [←Projectivization.mk_rep P.val] at h
  exact (onCurve_mk _ _).mp h

theorem equations_z_ne_zero (v : Coordinates) (hv : v≠0) (hE : Equations v) : v 3≠0 := by
  intro hz
  have h1 : v 1^2=15*v 0^2 := by
    have he := hE.1
    simp only [quadric1,hz,zero_pow (by decide : (2:ℕ)≠0),mul_zero,sub_zero] at he
    exact sub_eq_zero.mp he
  have h2 : v 2^2=10*v 0^2 := by
    have he := hE.2
    simp only [quadric2,hz,zero_pow (by decide : (2:ℕ)≠0),mul_zero,sub_zero] at he
    exact sub_eq_zero.mp he
  have hi := projective_infinity_trivial (v 0) (v 1) (v 2) h1 h2
  apply hv
  ext i
  fin_cases i <;> simp [hi.1,hi.2.1,hi.2.2,hz]

theorem z_ne_zero (P : Point) : P.val.rep 3≠0 :=
  equations_z_ne_zero _ P.val.rep_nonzero (representative_equations P)

def toAffine (P : Point) : CPoint where
  m:=P.val.rep 0/P.val.rep 3
  u:=P.val.rep 1/P.val.rep 3
  v:=P.val.rep 2/P.val.rep 3
  u_sq:=by
    have hz := z_ne_zero P
    have he := (representative_equations P).1
    unfold quadric1 at he
    field_simp
    linear_combination he
  v_sq:=by
    have hz := z_ne_zero P
    have he := (representative_equations P).2
    unfold quadric2 at he
    field_simp
    linear_combination he

def affineVector (c : CPoint) : Coordinates := ![c.m,c.u,c.v,1]

theorem affineVector_ne_zero (c : CPoint) : affineVector c≠0 := by
  intro h
  have he := congrFun h 3
  norm_num [affineVector] at he

theorem affineVector_equations (c : CPoint) : Equations (affineVector c) := by
  constructor
  · norm_num [quadric1,affineVector]
    linear_combination c.u_sq
  · norm_num [quadric2,affineVector]
    linear_combination c.v_sq

def fromAffine (c : CPoint) : Point :=
  ⟨Projectivization.mk ℚ (affineVector c) (affineVector_ne_zero c),
    (onCurve_mk _ _).mpr (affineVector_equations c)⟩

theorem normalized_representative (P : Point) :
    affineVector (toAffine P)=(P.val.rep 3)⁻¹ • P.val.rep := by
  have hz := z_ne_zero P
  ext i
  fin_cases i <;> simp [affineVector,toAffine,Pi.smul_apply,smul_eq_mul,div_eq_mul_inv,mul_comm,hz]

theorem fromAffine_toAffine (P : Point) : fromAffine (toAffine P)=P := by
  apply Subtype.ext
  change Projectivization.mk ℚ (affineVector (toAffine P)) _=P.val
  rw [←Projectivization.mk_rep P.val]
  apply (Projectivization.mk_eq_mk_iff ℚ _ _ _ _).mpr
  refine ⟨Units.mk0 ((P.val.rep 3)⁻¹) (inv_ne_zero (z_ne_zero P)),?_⟩
  change (P.val.rep 3)⁻¹ • P.val.rep=affineVector (toAffine P)
  exact (normalized_representative P).symm

theorem toAffine_fromAffine (c : CPoint) : toAffine (fromAffine c)=c := by
  obtain ⟨a,ha⟩ := Projectivization.exists_smul_eq_mk_rep ℚ (affineVector c) (affineVector_ne_zero c)
  have hn : (a:ℚ)≠0 := Units.ne_zero a
  apply CPoint.ext
  · change (Projectivization.mk ℚ (affineVector c) _).rep 0/
      (Projectivization.mk ℚ (affineVector c) _).rep 3=c.m
    rw [←ha]
    simp [affineVector,Units.smul_def,hn]
  · change (Projectivization.mk ℚ (affineVector c) _).rep 1/
      (Projectivization.mk ℚ (affineVector c) _).rep 3=c.u
    rw [←ha]
    simp [affineVector,Units.smul_def,hn]
  · change (Projectivization.mk ℚ (affineVector c) _).rep 2/
      (Projectivization.mk ℚ (affineVector c) _).rep 3=c.v
    rw [←ha]
    simp [affineVector,Units.smul_def,hn]

/-- Normalization z=1 is an equivalence of the homogeneous rational
intersection with the affine three-coordinate point type. -/
def equivAffine : Point ≃ CPoint where
  toFun:=toAffine
  invFun:=fromAffine
  left_inv:=fromAffine_toAffine
  right_inv:=toAffine_fromAffine

theorem infinite_projective_points (hSilvermanVII34 : OddPrimeTorsionIntegrality) : Infinite Point := by
  let : Infinite CPoint := infinite_CPoint hSilvermanVII34
  exact Infinite.of_injective fromAffine equivAffine.symm.injective

end
end Z2Z4Rank6.ProjectiveBasePoints
