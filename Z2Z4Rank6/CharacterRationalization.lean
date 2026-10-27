module

public import Z2Z4Rank6.PointScaling
public import Z2Z4Rank6.BiquadraticDecomposition

@[expose] public section

/-!
# Rationalization of an integral character subgroup

For commuting involutions of an arbitrary abelian group, rationalizing its
simultaneous sign subgroup gives precisely the corresponding rational joint
eigenspace. The inverse is the integral four-term norm followed by division
by four.
-/

namespace Z2Z4Rank6.CharacterRationalization

open scoped TensorProduct

noncomputable section

variable {G : Type*} [AddCommGroup G]

/-- The signed identity map on an arbitrary abelian group. -/
def signed (b : Bool) : G →+ G := if b then -AddMonoidHom.id G else AddMonoidHom.id G

@[simp] theorem signed_apply (b : Bool) (P : G) : signed b P = if b then -P else P := by
  cases b <;> rfl

/-- The simultaneous sign subgroup, before killing any torsion. -/
def characterGroup (f g : G →+ G) (χ : Bool × Bool) : AddSubgroup G where
  carrier := {P | f P = (if χ.1 then -P else P) ∧ g P = (if χ.2 then -P else P)}
  zero_mem' := by simp
  add_mem' := by
    intro P Q hP hQ
    rcases hP with ⟨hPf,hPg⟩
    rcases hQ with ⟨hQf,hQg⟩
    constructor <;> simp only [map_add, hPf, hPg, hQf, hQg] <;>
      split <;> simp_all [add_comm]
  neg_mem' := by
    intro P hP
    rcases hP with ⟨hPf,hPg⟩
    constructor <;> simp only [map_neg,hPf,hPg] <;> split <;> simp_all

/-- The four-term integral norm for the chosen pair of signs. -/
def normMap (f g : G →+ G) (χ : Bool × Bool) : G →+ G :=
  (AddMonoidHom.id G + (signed χ.1).comp f).comp
    (AddMonoidHom.id G + (signed χ.2).comp g)

theorem normMap_mem (f g : G →+ G)
    (hf : ∀ P, f (f P)=P) (hg : ∀ P, g (g P)=P)
    (hc : ∀ P, f (g P)=g (f P)) (χ : Bool × Bool) (P : G) :
    normMap f g χ P ∈ characterGroup f g χ := by
  have hgf (P : G) : g (f P)=f (g P) := (hc P).symm
  change f (normMap f g χ P) = (if χ.1 then -(normMap f g χ P) else normMap f g χ P) ∧
    g (normMap f g χ P) = (if χ.2 then -(normMap f g χ P) else normMap f g χ P)
  rcases χ with ⟨a,b⟩
  cases a <;> cases b <;>
    dsimp [normMap,signed] <;>
    simp only [map_add,map_neg,hf,hg,hgf] <;> constructor <;> abel


/-- The norm, with its integral character-subgroup codomain. -/
def normToCharacter (f g : G →+ G)
    (hf : ∀ P, f (f P)=P) (hg : ∀ P, g (g P)=P)
    (hc : ∀ P, f (g P)=g (f P)) (χ : Bool × Bool) :
    G →+ characterGroup f g χ :=
  (normMap f g χ).codRestrict _ (normMap_mem f g hf hg hc χ)

abbrev rationalGroup (G : Type*) [AddCommGroup G] := ℚ ⊗[ℤ] G

/-- The rationalized inclusion of the character subgroup. -/
def inclusion (f g : G →+ G) (χ : Bool × Bool) :
    ℚ ⊗[ℤ] characterGroup f g χ →ₗ[ℚ] rationalGroup G :=
  PointScaling.rationalizeHom (characterGroup f g χ).subtype

theorem inclusion_injective (f g : G →+ G) (χ : Bool × Bool) :
    Function.Injective (inclusion f g χ) :=
  PointScaling.rationalizeHom_injective _ Subtype.val_injective

theorem inclusion_mem (f g : G →+ G) (χ : Bool × Bool)
    (z : ℚ ⊗[ℤ] characterGroup f g χ) :
    inclusion f g χ z ∈ Biquadratic.jointSpace
      (PointScaling.rationalizeHom f) (PointScaling.rationalizeHom g) χ := by
  induction z using TensorProduct.inductionOn with
  | tmul q P =>
    rw [Biquadratic.mem_jointSpace]
    change (q ⊗ₜ[ℤ] f P.val = Biquadratic.characterSign χ.1 • (q ⊗ₜ[ℤ] P.val)) ∧
      (q ⊗ₜ[ℤ] g P.val = Biquadratic.characterSign χ.2 • (q ⊗ₜ[ℤ] P.val))
    obtain ⟨hU,hV⟩ := P.property
    rw [hU,hV]
    rcases χ with ⟨a,b⟩
    cases a <;> cases b <;>
      simp [Biquadratic.characterSign, TensorProduct.tmul_neg]
  | add x y hx hy =>
    rw [map_add]
    exact Submodule.add_mem _ hx hy

/-- The rationalized inclusion with its exact joint-eigenspace codomain. -/
def toCharacterSpace (f g : G →+ G) (χ : Bool × Bool) :
    ℚ ⊗[ℤ] characterGroup f g χ →ₗ[ℚ]
      Biquadratic.jointSpace (PointScaling.rationalizeHom f)
        (PointScaling.rationalizeHom g) χ :=
  (inclusion f g χ).codRestrict _ (inclusion_mem f g χ)

/-- Divide the four-term integral norm by four. -/
def liftProjector (f g : G →+ G)
    (hf : ∀ P, f (f P)=P) (hg : ∀ P, g (g P)=P)
    (hc : ∀ P, f (g P)=g (f P)) (χ : Bool × Bool) :
    rationalGroup G →ₗ[ℚ] ℚ ⊗[ℤ] characterGroup f g χ :=
  (1/4 : ℚ) • PointScaling.rationalizeHom (normToCharacter f g hf hg hc χ)

theorem inclusion_liftProjector (f g : G →+ G)
    (hf : ∀ P, f (f P)=P) (hg : ∀ P, g (g P)=P)
    (hc : ∀ P, f (g P)=g (f P)) (χ : Bool × Bool) (z : rationalGroup G) :
    inclusion f g χ (liftProjector f g hf hg hc χ z) =
      Biquadratic.projector (PointScaling.rationalizeHom f)
        (PointScaling.rationalizeHom g) χ z := by
  induction z using TensorProduct.inductionOn with
  | tmul q P =>
    rw [Biquadratic.projector_apply]
    rcases χ with ⟨a,b⟩
    cases a <;> cases b <;>
      simp [inclusion, liftProjector, normToCharacter, normMap,
        Biquadratic.characterSign, TensorProduct.tmul_add, TensorProduct.tmul_neg] <;> module
  | add x y hx hy => simp only [map_add,hx,hy]

/-- Integral sign-subgroup rationalization is precisely the
joint sign-character space of the rationalized abelian group. -/
def equivCharacterSpace (f g : G →+ G)
    (hf : ∀ P, f (f P)=P) (hg : ∀ P, g (g P)=P)
    (hc : ∀ P, f (g P)=g (f P)) (χ : Bool × Bool) :
    (ℚ ⊗[ℤ] characterGroup f g χ) ≃ₗ[ℚ]
      Biquadratic.jointSpace (PointScaling.rationalizeHom f)
        (PointScaling.rationalizeHom g) χ :=
  LinearEquiv.ofBijective (toCharacterSpace f g χ) ⟨
    fun x y h => inclusion_injective f g χ (congrArg Subtype.val h),
    fun z => ⟨liftProjector f g hf hg hc χ z.val, by
      apply Subtype.ext
      exact (inclusion_liftProjector f g hf hg hc χ z.val).trans
        ((Biquadratic.projector_on_jointSpace _ _ χ χ z.val z.property).trans
          (ite_eq_left rfl))⟩⟩

end
end Z2Z4Rank6.CharacterRationalization
