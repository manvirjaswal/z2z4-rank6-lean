module

public import Z2Z4Rank6.BiquadraticDecomposition

@[expose] public section

/-!
# Eight character spaces of three commuting involutions

Generic rational linear algebra: the eight signed projectors give a
product and direct-sum decomposition of any rational vector space.
-/
namespace Z2Z4Rank6.ThreeCharacter
open scoped BigOperators DirectSum
open Biquadratic
variable {V : Type*} [AddCommGroup V] [Module ℚ V]

def jointSpace (σ τ υ : V →ₗ[ℚ] V) (χ : Bool × Bool × Bool) : Submodule ℚ V :=
  Module.End.eigenspace σ (characterSign χ.1) ⊓
    (Module.End.eigenspace τ (characterSign χ.2.1) ⊓
      Module.End.eigenspace υ (characterSign χ.2.2))

theorem mem_jointSpace (σ τ υ : V →ₗ[ℚ] V) (χ : Bool × Bool × Bool) (v : V) :
    v ∈ jointSpace σ τ υ χ ↔
      σ v = characterSign χ.1 • v ∧
      τ v = characterSign χ.2.1 • v ∧ υ v = characterSign χ.2.2 • v := by
  simp only [jointSpace, Submodule.mem_inf, Module.End.mem_eigenspace_iff]

def projector (σ τ υ : V →ₗ[ℚ] V) (χ : Bool × Bool × Bool) : V →ₗ[ℚ] V :=
  (1/8 : ℚ) • ((LinearMap.id + characterSign χ.1 • σ).comp
    ((LinearMap.id + characterSign χ.2.1 • τ).comp
      (LinearMap.id + characterSign χ.2.2 • υ)))

theorem projector_apply (σ τ υ : V →ₗ[ℚ] V) (χ : Bool × Bool × Bool) (v : V) :
    projector σ τ υ χ v = (1/8 : ℚ) •
      (v + characterSign χ.2.2 • υ v + characterSign χ.2.1 • τ v +
        (characterSign χ.2.1*characterSign χ.2.2) • τ (υ v) +
        characterSign χ.1 • σ v +
        (characterSign χ.1*characterSign χ.2.2) • σ (υ v) +
        (characterSign χ.1*characterSign χ.2.1) • σ (τ v) +
        (characterSign χ.1*characterSign χ.2.1*characterSign χ.2.2) • σ (τ (υ v))) := by
  simp only [projector, LinearMap.smul_apply, LinearMap.comp_apply,
    LinearMap.add_apply, LinearMap.id_apply, map_add, map_smul]
  module

theorem projector_mem_jointSpace (σ τ υ : V →ₗ[ℚ] V)
    (hσ : σ.comp σ = LinearMap.id) (hτ : τ.comp τ = LinearMap.id)
    (hυ : υ.comp υ = LinearMap.id)
    (hστ : σ.comp τ = τ.comp σ) (hσυ : σ.comp υ = υ.comp σ)
    (hτυ : τ.comp υ = υ.comp τ) (χ : Bool × Bool × Bool) (v : V) :
    projector σ τ υ χ v ∈ jointSpace σ τ υ χ := by
  have hσσ (w : V) : σ (σ w) = w := LinearMap.congr_fun hσ w
  have hττ (w : V) : τ (τ w) = w := LinearMap.congr_fun hτ w
  have hυυ (w : V) : υ (υ w) = w := LinearMap.congr_fun hυ w
  have hτσ (w : V) : τ (σ w) = σ (τ w) := (LinearMap.congr_fun hστ w).symm
  have hυσ (w : V) : υ (σ w) = σ (υ w) := (LinearMap.congr_fun hσυ w).symm
  have hυτ (w : V) : υ (τ w) = τ (υ w) := (LinearMap.congr_fun hτυ w).symm
  rw [mem_jointSpace, projector_apply]
  simp only [map_smul, map_add, hσσ, hττ, hυυ, hτσ, hυσ, hυτ]
  rcases χ with ⟨a,b,c⟩
  cases a <;> cases b <;> cases c <;>
    norm_num [characterSign] <;> constructor <;>
    first | module | (constructor <;> module)

theorem projector_on_jointSpace (σ τ υ : V →ₗ[ℚ] V)
    (χ ψ : Bool × Bool × Bool) (v : V) (hv : v ∈ jointSpace σ τ υ ψ) :
    projector σ τ υ χ v = if χ = ψ then v else 0 := by
  obtain ⟨hσ,hτ,hυ⟩ := (mem_jointSpace σ τ υ ψ v).mp hv
  rw [projector_apply]
  simp only [hσ, hτ, hυ, map_smul]
  rcases χ with ⟨a,b,c⟩
  rcases ψ with ⟨d,e,f⟩
  cases a <;> cases b <;> cases c <;>
    cases d <;> cases e <;> cases f <;>
    norm_num [characterSign] <;> module

theorem sum_projectors (σ τ υ : V →ₗ[ℚ] V) (v : V) :
    ∑ χ : Bool × Bool × Bool, projector σ τ υ χ v = v := by
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, projector_apply, characterSign]
  norm_num
  module

noncomputable def decompositionEquiv (σ τ υ : V →ₗ[ℚ] V)
    (hσ : σ.comp σ = LinearMap.id) (hτ : τ.comp τ = LinearMap.id)
    (hυ : υ.comp υ = LinearMap.id)
    (hστ : σ.comp τ = τ.comp σ) (hσυ : σ.comp υ = υ.comp σ)
    (hτυ : τ.comp υ = υ.comp τ) :
    V ≃ₗ[ℚ] ∀ χ : Bool × Bool × Bool, jointSpace σ τ υ χ where
  toFun v χ := ⟨projector σ τ υ χ v,
    projector_mem_jointSpace σ τ υ hσ hτ hυ hστ hσυ hτυ χ v⟩
  invFun w := ∑ χ : Bool × Bool × Bool, (w χ : V)
  left_inv := sum_projectors σ τ υ
  right_inv w := by
    funext χ
    apply Subtype.ext
    change projector σ τ υ χ (∑ ψ : Bool × Bool × Bool, (w ψ : V)) = (w χ : V)
    rw [map_sum]
    calc
      ∑ ψ : Bool × Bool × Bool, projector σ τ υ χ (w ψ : V) =
          ∑ ψ : Bool × Bool × Bool, if χ = ψ then (w ψ : V) else 0 := by
        apply Finset.sum_congr rfl
        intro ψ _
        exact projector_on_jointSpace σ τ υ χ ψ _ (w ψ).property
      _ = (w χ : V) := by simp
  map_add' v w := by
    funext χ
    apply Subtype.ext
    exact (projector σ τ υ χ).map_add v w
  map_smul' a v := by
    funext χ
    apply Subtype.ext
    exact (projector σ τ υ χ).map_smul a v

noncomputable def directSumEquiv (σ τ υ : V →ₗ[ℚ] V)
    (hσ : σ.comp σ = LinearMap.id) (hτ : τ.comp τ = LinearMap.id)
    (hυ : υ.comp υ = LinearMap.id)
    (hστ : σ.comp τ = τ.comp σ) (hσυ : σ.comp υ = υ.comp σ)
    (hτυ : τ.comp υ = υ.comp τ) :
    V ≃ₗ[ℚ] ⨁ χ : Bool × Bool × Bool, jointSpace σ τ υ χ :=
  (decompositionEquiv σ τ υ hσ hτ hυ hστ hσυ hτυ).trans
    DFinsupp.linearEquivFunOnFintype.symm

theorem rank_decomposition (σ τ υ : V →ₗ[ℚ] V)
    (hσ : σ.comp σ = LinearMap.id) (hτ : τ.comp τ = LinearMap.id)
    (hυ : υ.comp υ = LinearMap.id)
    (hστ : σ.comp τ = τ.comp σ) (hσυ : σ.comp υ = υ.comp σ)
    (hτυ : τ.comp υ = υ.comp τ) :
    Module.rank ℚ V = Cardinal.sum
      (fun χ : Bool × Bool × Bool => Module.rank ℚ (jointSpace σ τ υ χ)) := by
  rw [(decompositionEquiv σ τ υ hσ hτ hυ hστ hσυ hτυ).rank_eq, rank_pi]

end Z2Z4Rank6.ThreeCharacter
