module

public import Z2Z4Rank6.BiquadraticDecomposition

@[expose] public section

/-! # Two sign spaces of a rational linear involution

The linear algebra for the quadratic decomposition in Jaswal,
Proposition 7.2(b), DOI: 10.5281/zenodo.23437117.
-/

namespace Z2Z4Rank6.QuadraticLinear

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

def signSpace (σ : V →ₗ[ℚ] V) (ε : Bool) : Submodule ℚ V :=
  Biquadratic.jointSpace σ LinearMap.id (ε,false)

theorem mem_signSpace (σ : V →ₗ[ℚ] V) (ε : Bool) (v : V) :
    v ∈ signSpace σ ε ↔ σ v=(if ε then -v else v) := by
  rw [signSpace,Biquadratic.mem_jointSpace]
  cases ε <;> simp [Biquadratic.characterSign]

def positiveProjector (σ : V →ₗ[ℚ] V) : V →ₗ[ℚ] V := (1/2 : ℚ) • (LinearMap.id+σ)
def negativeProjector (σ : V →ₗ[ℚ] V) : V →ₗ[ℚ] V := (1/2 : ℚ) • (LinearMap.id-σ)

theorem positiveProjector_mem (σ : V →ₗ[ℚ] V) (hσ : σ.comp σ=LinearMap.id) (v : V) :
    positiveProjector σ v ∈ signSpace σ false := by
  have hh : σ (σ v)=v := congrArg (fun f : V →ₗ[ℚ] V => f v) hσ
  rw [mem_signSpace]
  change σ ((1/2 : ℚ) • (v+σ v))=(1/2 : ℚ) • (v+σ v)
  rw [map_smul,map_add,hh]
  module

theorem negativeProjector_mem (σ : V →ₗ[ℚ] V) (hσ : σ.comp σ=LinearMap.id) (v : V) :
    negativeProjector σ v ∈ signSpace σ true := by
  have hh : σ (σ v)=v := congrArg (fun f : V →ₗ[ℚ] V => f v) hσ
  rw [mem_signSpace]
  change σ ((1/2 : ℚ) • (v-σ v))= -((1/2 : ℚ) • (v-σ v))
  rw [map_smul,map_sub,hh]
  module

/-- The canonical two-character decomposition, with inverse given by addition
of the inclusions. -/
def decompositionEquiv (σ : V →ₗ[ℚ] V) (hσ : σ.comp σ=LinearMap.id) :
    V ≃ₗ[ℚ] signSpace σ false × signSpace σ true where
  toFun v := (⟨positiveProjector σ v,positiveProjector_mem σ hσ v⟩,
    ⟨negativeProjector σ v,negativeProjector_mem σ hσ v⟩)
  invFun z := z.1.val+z.2.val
  left_inv v := by
    change (1/2 : ℚ) • (v+σ v)+(1/2 : ℚ) • (v-σ v)=v
    module
  right_inv z := by
    have hp : σ z.1.val=z.1.val := (mem_signSpace σ false _).mp z.1.property
    have hn : σ z.2.val= -z.2.val := (mem_signSpace σ true _).mp z.2.property
    apply Prod.ext
    · apply Subtype.ext
      change (1/2 : ℚ) • (z.1.val+z.2.val+σ (z.1.val+z.2.val))=z.1.val
      rw [map_add,hp,hn]
      module
    · apply Subtype.ext
      change (1/2 : ℚ) • (z.1.val+z.2.val-σ (z.1.val+z.2.val))=z.2.val
      rw [map_add,hp,hn]
      module
  map_add' x y := by
    apply Prod.ext
    · exact Subtype.ext ((positiveProjector σ).map_add x y)
    · exact Subtype.ext ((negativeProjector σ).map_add x y)
  map_smul' q v := by
    apply Prod.ext
    · exact Subtype.ext ((positiveProjector σ).map_smul q v)
    · exact Subtype.ext ((negativeProjector σ).map_smul q v)

theorem rank_decomposition (σ : V →ₗ[ℚ] V) (hσ : σ.comp σ=LinearMap.id) :
    Module.rank ℚ V=Module.rank ℚ (signSpace σ false)+Module.rank ℚ (signSpace σ true) := by
  rw [(decompositionEquiv σ hσ).rank_eq,rank_prod']

theorem finrank_decomposition [FiniteDimensional ℚ V]
    (σ : V →ₗ[ℚ] V) (hσ : σ.comp σ=LinearMap.id) :
    Module.finrank ℚ V=Module.finrank ℚ (signSpace σ false)+
      Module.finrank ℚ (signSpace σ true) := by
  rw [(decompositionEquiv σ hσ).finrank_eq,Module.finrank_prod]

end Z2Z4Rank6.QuadraticLinear
