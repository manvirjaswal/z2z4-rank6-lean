import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.DirectSum.Finite
import Mathlib.Tactic

/-!
# Four character spaces of commuting involutions

The rational linear algebra in Remark 4.3 and the rank decomposition in
Proposition 5.2 of Manvir Jaswal, "Infinitely many elliptic curves with torsion
Z/2Z × Z/4Z and rank at least six",
DOI: 10.5281/zenodo.23437117.

These results concern arbitrary rational vector spaces and commuting linear
involutions. Identifying the particular elliptic-curve tensor space and its
twists with these eigenspaces is a separate arithmetic step.
-/

namespace Z2Z4Rank6.Biquadratic

open scoped BigOperators DirectSum

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

/-- `false` denotes the positive character and `true` the negative character. -/
def characterSign (ε : Bool) : ℚ := if ε then -1 else 1

/-- The simultaneous character eigenspace for the two sign changes. -/
def jointSpace (σ τ : V →ₗ[ℚ] V) (χ : Bool × Bool) : Submodule ℚ V :=
  Module.End.eigenspace σ (characterSign χ.1) ⊓ Module.End.eigenspace τ (characterSign χ.2)

theorem mem_jointSpace (σ τ : V →ₗ[ℚ] V) (χ : Bool × Bool) (v : V) :
    v ∈ jointSpace σ τ χ ↔
      σ v = characterSign χ.1 • v ∧ τ v = characterSign χ.2 • v := by
  simp only [jointSpace, Submodule.mem_inf, Module.End.mem_eigenspace_iff]

/-- The projector `(1/4)(1+εσ)(1+δτ)`, with the character signs specified by χ. -/
def projector (σ τ : V →ₗ[ℚ] V) (χ : Bool × Bool) : V →ₗ[ℚ] V :=
  (1 / 4 : ℚ) • ((LinearMap.id + characterSign χ.1 • σ).comp
    (LinearMap.id + characterSign χ.2 • τ))

theorem projector_apply (σ τ : V →ₗ[ℚ] V) (χ : Bool × Bool) (v : V) :
    projector σ τ χ v = (1/4 : ℚ) •
      (v + characterSign χ.2 • τ v + characterSign χ.1 • σ v +
        (characterSign χ.1 * characterSign χ.2) • σ (τ v)) := by
  simp only [projector, LinearMap.smul_apply, LinearMap.comp_apply,
    LinearMap.add_apply, LinearMap.id_apply, map_add, map_smul]
  module

theorem projector_mem_jointSpace (σ τ : V →ₗ[ℚ] V)
    (hσ : σ.comp σ = LinearMap.id) (hτ : τ.comp τ = LinearMap.id)
    (hcomm : σ.comp τ = τ.comp σ) (χ : Bool × Bool) (v : V) :
    projector σ τ χ v ∈ jointSpace σ τ χ := by
  have hσσ (w : V) : σ (σ w) = w := LinearMap.congr_fun hσ w
  have hττ (w : V) : τ (τ w) = w := LinearMap.congr_fun hτ w
  have hτσ (w : V) : τ (σ w) = σ (τ w) := (LinearMap.congr_fun hcomm w).symm
  rw [mem_jointSpace, projector_apply]
  constructor
  · simp only [map_smul, map_add, hσσ]
    rcases χ with ⟨ε, δ⟩
    cases ε <;> cases δ <;> norm_num [characterSign] <;> module
  · simp only [map_smul, map_add, hττ, hτσ]
    rcases χ with ⟨ε, δ⟩
    cases ε <;> cases δ <;> norm_num [characterSign] <;> module

/-- A projector acts as the identity on its own character space and as zero
on any of the other three character spaces. -/
theorem projector_on_jointSpace (σ τ : V →ₗ[ℚ] V) (χ ψ : Bool × Bool)
    (v : V) (hv : v ∈ jointSpace σ τ ψ) :
    projector σ τ χ v = if χ = ψ then v else 0 := by
  obtain ⟨hσ, hτ⟩ := (mem_jointSpace σ τ ψ v).mp hv
  rw [projector_apply, hτ, map_smul, hσ]
  rcases χ with ⟨ε, δ⟩
  rcases ψ with ⟨ε', δ'⟩
  cases ε <;> cases δ <;> cases ε' <;> cases δ' <;>
    norm_num [characterSign] <;> module

theorem projector_idempotent (σ τ : V →ₗ[ℚ] V)
    (hσ : σ.comp σ = LinearMap.id) (hτ : τ.comp τ = LinearMap.id)
    (hcomm : σ.comp τ = τ.comp σ) (χ : Bool × Bool) :
    (projector σ τ χ).comp (projector σ τ χ) = projector σ τ χ := by
  ext v
  exact (projector_on_jointSpace σ τ χ χ _
    (projector_mem_jointSpace σ τ hσ hτ hcomm χ v)).trans (ite_eq_left rfl)

theorem projector_orthogonal (σ τ : V →ₗ[ℚ] V)
    (hσ : σ.comp σ = LinearMap.id) (hτ : τ.comp τ = LinearMap.id)
    (hcomm : σ.comp τ = τ.comp σ) (χ ψ : Bool × Bool) (hne : χ ≠ ψ) :
    (projector σ τ χ).comp (projector σ τ ψ) = 0 := by
  ext v
  exact (projector_on_jointSpace σ τ χ ψ _
    (projector_mem_jointSpace σ τ hσ hτ hcomm ψ v)).trans (ite_eq_right hne)

theorem sum_projectors (σ τ : V →ₗ[ℚ] V) (v : V) :
    ∑ χ : Bool × Bool, projector σ τ χ v = v := by
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, projector_apply, characterSign]
  norm_num
  module

/-- The canonical decomposition into the four simultaneous character spaces. -/
noncomputable def decompositionEquiv (σ τ : V →ₗ[ℚ] V)
    (hσ : σ.comp σ = LinearMap.id) (hτ : τ.comp τ = LinearMap.id)
    (hcomm : σ.comp τ = τ.comp σ) :
    V ≃ₗ[ℚ] (∀ χ : Bool × Bool, jointSpace σ τ χ) where
  toFun v χ := ⟨projector σ τ χ v, projector_mem_jointSpace σ τ hσ hτ hcomm χ v⟩
  invFun w := ∑ χ : Bool × Bool, (w χ : V)
  left_inv := sum_projectors σ τ
  right_inv w := by
    funext χ
    apply Subtype.ext
    change projector σ τ χ (∑ ψ : Bool × Bool, (w ψ : V)) = (w χ : V)
    rw [map_sum]
    calc
      ∑ ψ : Bool × Bool, projector σ τ χ (w ψ : V) =
          ∑ ψ : Bool × Bool, if χ = ψ then (w ψ : V) else 0 := by
        apply Finset.sum_congr rfl
        intro ψ _
        exact projector_on_jointSpace σ τ χ ψ _ (w ψ).property
      _ = (w χ : V) := by simp
  map_add' v w := by
    funext χ
    apply Subtype.ext
    exact (projector σ τ χ).map_add v w
  map_smul' a v := by
    funext χ
    apply Subtype.ext
    exact (projector σ τ χ).map_smul a v

theorem decompositionEquiv_apply (σ τ : V →ₗ[ℚ] V)
    (hσ : σ.comp σ = LinearMap.id) (hτ : τ.comp τ = LinearMap.id)
    (hcomm : σ.comp τ = τ.comp σ) (v : V) (χ : Bool × Bool) :
    ((decompositionEquiv σ τ hσ hτ hcomm v) χ : V) = projector σ τ χ v := rfl

theorem decompositionEquiv_symm_apply (σ τ : V →ₗ[ℚ] V)
    (hσ : σ.comp σ = LinearMap.id) (hτ : τ.comp τ = LinearMap.id)
    (hcomm : σ.comp τ = τ.comp σ) (w : ∀ χ : Bool × Bool, jointSpace σ τ χ) :
    (decompositionEquiv σ τ hσ hτ hcomm).symm w = ∑ χ : Bool × Bool, (w χ : V) := rfl

/-- The finite product decomposition is also the external direct sum. -/
noncomputable def directSumEquiv (σ τ : V →ₗ[ℚ] V)
    (hσ : σ.comp σ = LinearMap.id) (hτ : τ.comp τ = LinearMap.id)
    (hcomm : σ.comp τ = τ.comp σ) :
    V ≃ₗ[ℚ] ⨁ χ : Bool × Bool, jointSpace σ τ χ :=
  (decompositionEquiv σ τ hσ hτ hcomm).trans DFinsupp.linearEquivFunOnFintype.symm

/-- The dimension-independent cardinal rank decomposition. -/
theorem rank_decomposition (σ τ : V →ₗ[ℚ] V)
    (hσ : σ.comp σ = LinearMap.id) (hτ : τ.comp τ = LinearMap.id)
    (hcomm : σ.comp τ = τ.comp σ) :
    Module.rank ℚ V = Cardinal.sum (fun χ : Bool × Bool => Module.rank ℚ (jointSpace σ τ χ)) := by
  rw [(decompositionEquiv σ τ hσ hτ hcomm).rank_eq, rank_pi]

/-- For finite-dimensional V, the four eigenspace dimensions add to dim V. -/
theorem finrank_decomposition [FiniteDimensional ℚ V] (σ τ : V →ₗ[ℚ] V)
    (hσ : σ.comp σ = LinearMap.id) (hτ : τ.comp τ = LinearMap.id)
    (hcomm : σ.comp τ = τ.comp σ) :
    Module.finrank ℚ V = ∑ χ : Bool × Bool, Module.finrank ℚ (jointSpace σ τ χ) := by
  rw [(decompositionEquiv σ τ hσ hτ hcomm).finrank_eq, Module.finrank_pi_fintype]

theorem finrank_four_spaces [FiniteDimensional ℚ V] (σ τ : V →ₗ[ℚ] V)
    (hσ : σ.comp σ = LinearMap.id) (hτ : τ.comp τ = LinearMap.id)
    (hcomm : σ.comp τ = τ.comp σ) :
    Module.finrank ℚ V =
      Module.finrank ℚ (jointSpace σ τ (false, false)) +
      Module.finrank ℚ (jointSpace σ τ (true, false)) +
      Module.finrank ℚ (jointSpace σ τ (false, true)) +
      Module.finrank ℚ (jointSpace σ τ (true, true)) := by
  rw [finrank_decomposition σ τ hσ hτ hcomm]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  omega

end Z2Z4Rank6.Biquadratic
