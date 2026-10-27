module

public import Z2Z4Rank6.Quartic
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Tactic

@[expose] public section

/-!
# Local coordinate maps from E_C to C

The quartic coordinate changes from Lemma 4.1 of M. Jaswal,
*Infinitely many elliptic curves with torsion Z/2Z × Z/4Z and rank at least six*,
DOI 10.5281/zenodo.23437117, viewed over a topological field.
Continuity at the printed base point is the coordinate input needed to pull
the congruence neighborhoods of Proposition 6.2 back to E_C.
-/

namespace Z2Z4Rank6

/-- Affine E_C coordinates are sent to `(m,(u,v))` by the quartic maps. -/
def ecCoordinatesToC {K : Type*} [Field K] (z : K × K) : K × (K × K) :=
  let k := ecToK z.1 z.2
  let eta := ecToEta z.1 z.2
  (conicM k, (conicU k, conicV k eta))

/-- The E_C affine coordinates corresponding to the printed point c0. -/
def ecCoordinatesC0 {K : Type*} [Field K] : K × K :=
  (-526480/1681, 96843600/68921)

theorem ecCoordinatesC0_to_k {K : Type*} [Field K] [CharZero K] :
    ecToK (ecCoordinatesC0 (K := K)).1 (ecCoordinatesC0 (K := K)).2 = 35/41 := by
  norm_num [ecToK, ecCoordinatesC0]

theorem ecCoordinatesC0_to_eta {K : Type*} [Field K] [CharZero K] :
    ecToEta (ecCoordinatesC0 (K := K)).1 (ecCoordinatesC0 (K := K)).2 = -173670/1681 := by
  norm_num [ecToEta, ecToK, ecCoordinatesC0]

theorem ecCoordinatesC0_x_denom {K : Type*} [Field K] [CharZero K] :
    (ecCoordinatesC0 (K := K)).1 + 82 ≠ 0 := by
  norm_num [ecCoordinatesC0]

theorem ecCoordinatesC0_k_denom {K : Type*} [Field K] [CharZero K] :
    (ecToK (ecCoordinatesC0 (K := K)).1 (ecCoordinatesC0 (K := K)).2)^2 - 15 ≠ 0 := by
  rw [ecCoordinatesC0_to_k]
  norm_num

theorem ecCoordinatesToC_c0 {K : Type*} [Field K] [CharZero K] :
    ecCoordinatesToC (ecCoordinatesC0 (K := K)) =
      (7401/2399, (88235/2399, 86835/2399)) := by
  unfold ecCoordinatesToC
  rw [ecCoordinatesC0_to_k, ecCoordinatesC0_to_eta]
  norm_num [conicM, conicU, conicV]

theorem ecCoordinatesC0_equation {K : Type*} [Field K] [CharZero K] :
    (ecCoordinatesC0 (K := K)).2^2 = (ecCoordinatesC0 (K := K)).1^3 +
      (ecCoordinatesC0 (K := K)).1^2 - 137620*(ecCoordinatesC0 (K := K)).1 - 10504000 := by
  norm_num [ecCoordinatesC0]

theorem ecCoordinatesToC_equations {K : Type*} [Field K] [CharZero K]
    (z : K × K) (hx : z.1 + 82 ≠ 0)
    (hk : (ecToK z.1 z.2)^2 - 15 ≠ 0)
    (he : z.2^2 = z.1^3 + z.1^2 - 137620*z.1 - 10504000) :
    (ecCoordinatesToC z).2.1^2 = 5*(3*(ecCoordinatesToC z).1^2 + 242) ∧
    (ecCoordinatesToC z).2.2^2 = 5*(2*(ecCoordinatesToC z).1^2 + 243) := by
  exact ⟨conic_identity _ hk,
    quartic_to_second_conic _ _ hk (ec_to_quartic_equation z.1 z.2 hx he)⟩

section Naturality

variable {K L : Type*} [Field K] [Field L] (f : K →+* L)

theorem map_ecToK (x y : K) : f (ecToK x y) = ecToK (f x) (f y) := by
  simp [ecToK, map_ofNat]

theorem map_ecToEta (x y : K) : f (ecToEta x y) = ecToEta (f x) (f y) := by
  simp [ecToEta, map_ecToK, map_ofNat]

theorem map_conicM (k : K) : f (conicM k) = conicM (f k) := by simp [conicM, map_ofNat]

theorem map_conicU (k : K) : f (conicU k) = conicU (f k) := by simp [conicU, map_ofNat]

theorem map_conicV (k eta : K) : f (conicV k eta) = conicV (f k) (f eta) := by
  simp [conicV, map_ofNat]

theorem map_ecCoordinatesToC (z : K × K) :
    Prod.map f (Prod.map f f) (ecCoordinatesToC z) =
      ecCoordinatesToC (Prod.map f f z) := by
  simp [ecCoordinatesToC, map_conicM, map_conicU, map_conicV, map_ecToK, map_ecToEta]

theorem map_ecCoordinatesC0 :
    Prod.map f f (ecCoordinatesC0 (K := K)) = ecCoordinatesC0 (K := L) := by
  simp [ecCoordinatesC0, map_ofNat]

end Naturality

section Continuity

variable {K : Type*} [Field K] [CharZero K] [TopologicalSpace K]
  [IsTopologicalRing K] [ContinuousInv₀ K]

theorem ecToK_continuousAt (z : K × K) (hx : z.1 + 82 ≠ 0) :
    ContinuousAt (fun w : K × K => ecToK w.1 w.2) z := by
  unfold ecToK
  fun_prop (disch := exact mul_ne_zero (by norm_num : (7 : K) ≠ 0) hx)

theorem ecToEta_continuousAt (z : K × K) (hx : z.1 + 82 ≠ 0) :
    ContinuousAt (fun w : K × K => ecToEta w.1 w.2) z := by
  have hk := ecToK_continuousAt z hx
  unfold ecToEta
  fun_prop

omit [CharZero K] in
theorem conicM_continuousAt (k : K) (hk : k^2 - 15 ≠ 0) :
    ContinuousAt (conicM (K := K)) k := by
  unfold conicM
  fun_prop (disch := exact hk)

omit [CharZero K] in
theorem conicU_continuousAt (k : K) (hk : k^2 - 15 ≠ 0) :
    ContinuousAt (conicU (K := K)) k := by
  unfold conicU
  fun_prop (disch := exact hk)

omit [CharZero K] in
theorem conicV_continuousAt (z : K × K) (hk : z.1^2 - 15 ≠ 0) :
    ContinuousAt (fun w : K × K => conicV w.1 w.2) z := by
  unfold conicV
  fun_prop (disch := exact hk)

theorem ecCoordinatesToC_continuousAt (z : K × K) (hx : z.1 + 82 ≠ 0)
    (hk : (ecToK z.1 z.2)^2 - 15 ≠ 0) :
    ContinuousAt (ecCoordinatesToC (K := K)) z := by
  have hK := ecToK_continuousAt z hx
  have hE := ecToEta_continuousAt z hx
  have hM := (conicM_continuousAt (ecToK z.1 z.2) hk).comp
    (f := fun w : K × K => ecToK w.1 w.2) hK
  have hU := (conicU_continuousAt (ecToK z.1 z.2) hk).comp
    (f := fun w : K × K => ecToK w.1 w.2) hK
  have hV := (conicV_continuousAt (ecToK z.1 z.2, ecToEta z.1 z.2) hk).comp
    (f := fun w : K × K => (ecToK w.1 w.2, ecToEta w.1 w.2)) (hK.prodMk hE)
  exact hM.prodMk (hU.prodMk hV)

theorem ecCoordinatesToC_continuousAt_c0 :
    ContinuousAt (ecCoordinatesToC (K := K)) (ecCoordinatesC0 (K := K)) :=
  ecCoordinatesToC_continuousAt _ ecCoordinatesC0_x_denom ecCoordinatesC0_k_denom

end Continuity

end Z2Z4Rank6
