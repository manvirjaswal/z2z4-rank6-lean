module

public import Z2Z4Rank6.CharacterRationalization
public import Z2Z4Rank6.ThreeCharacterDecomposition

@[expose] public section

/-!
# Rationalization of integral three-sign character subgroups

For three commuting involutions on any abelian group, rationalizing
the integral character subgroup gives its rational joint
eigenspace. The inverse is the integral eight-term norm divided by eight.
-/
namespace Z2Z4Rank6.ThreeCharacterRationalization
open scoped TensorProduct
open CharacterRationalization (signed)
noncomputable section
variable {G : Type*} [AddCommGroup G]

def characterGroup (f g h : G →+ G) (χ : Bool × Bool × Bool) : AddSubgroup G where
  carrier := {P | f P = (if χ.1 then -P else P) ∧
    g P = (if χ.2.1 then -P else P) ∧ h P = (if χ.2.2 then -P else P)}
  zero_mem' := by simp
  add_mem' := by
    intro P Q hP hQ
    rcases hP with ⟨hPf,hPg,hPh⟩
    rcases hQ with ⟨hQf,hQg,hQh⟩
    refine ⟨?_,?_,?_⟩ <;>
      simp only [map_add,hPf,hPg,hPh,hQf,hQg,hQh] <;>
      split <;> simp_all [add_comm]
  neg_mem' := by
    intro P hP
    rcases hP with ⟨hPf,hPg,hPh⟩
    refine ⟨?_,?_,?_⟩ <;>
      simp only [map_neg,hPf,hPg,hPh] <;> split <;> simp_all

def normMap (f g h : G →+ G) (χ : Bool × Bool × Bool) : G →+ G :=
  (AddMonoidHom.id G + (signed χ.1).comp f).comp
    ((AddMonoidHom.id G + (signed χ.2.1).comp g).comp
      (AddMonoidHom.id G + (signed χ.2.2).comp h))

theorem normMap_mem (f g h : G →+ G)
    (hf : ∀ P, f (f P)=P) (hg : ∀ P, g (g P)=P) (hh : ∀ P, h (h P)=P)
    (hfg : ∀ P, f (g P)=g (f P)) (hfh : ∀ P, f (h P)=h (f P))
    (hgh : ∀ P, g (h P)=h (g P)) (χ : Bool × Bool × Bool) (P : G) :
    normMap f g h χ P ∈ characterGroup f g h χ := by
  have hgf (P : G) : g (f P)=f (g P) := (hfg P).symm
  have hhf (P : G) : h (f P)=f (h P) := (hfh P).symm
  have hhg (P : G) : h (g P)=g (h P) := (hgh P).symm
  change f (normMap f g h χ P) = (if χ.1 then -(normMap f g h χ P) else normMap f g h χ P) ∧
    g (normMap f g h χ P) = (if χ.2.1 then -(normMap f g h χ P) else normMap f g h χ P) ∧
    h (normMap f g h χ P) = (if χ.2.2 then -(normMap f g h χ P) else normMap f g h χ P)
  rcases χ with ⟨a,b,c⟩
  cases a <;> cases b <;> cases c <;>
    dsimp [normMap,signed] <;>
    simp only [map_add,map_neg,hf,hg,hh,hgf,hhf,hhg] <;>
    refine ⟨?_,?_,?_⟩ <;> abel

def normToCharacter (f g h : G →+ G)
    (hf : ∀ P, f (f P)=P) (hg : ∀ P, g (g P)=P) (hh : ∀ P, h (h P)=P)
    (hfg : ∀ P, f (g P)=g (f P)) (hfh : ∀ P, f (h P)=h (f P))
    (hgh : ∀ P, g (h P)=h (g P)) (χ : Bool × Bool × Bool) :
    G →+ characterGroup f g h χ :=
  (normMap f g h χ).codRestrict _ (normMap_mem f g h hf hg hh hfg hfh hgh χ)

abbrev rationalGroup (G : Type*) [AddCommGroup G] := ℚ ⊗[ℤ] G

def inclusion (f g h : G →+ G) (χ : Bool × Bool × Bool) :
    ℚ ⊗[ℤ] characterGroup f g h χ →ₗ[ℚ] rationalGroup G :=
  PointScaling.rationalizeHom (characterGroup f g h χ).subtype

theorem inclusion_injective (f g h : G →+ G) (χ : Bool × Bool × Bool) :
    Function.Injective (inclusion f g h χ) :=
  PointScaling.rationalizeHom_injective _ Subtype.val_injective

theorem inclusion_mem (f g h : G →+ G) (χ : Bool × Bool × Bool)
    (z : ℚ ⊗[ℤ] characterGroup f g h χ) :
    inclusion f g h χ z ∈ ThreeCharacter.jointSpace
      (PointScaling.rationalizeHom f) (PointScaling.rationalizeHom g)
      (PointScaling.rationalizeHom h) χ := by
  induction z using TensorProduct.inductionOn with
  | tmul q P =>
    rw [ThreeCharacter.mem_jointSpace]
    change (q ⊗ₜ[ℤ] f P.val = Biquadratic.characterSign χ.1 • (q ⊗ₜ[ℤ] P.val)) ∧
      (q ⊗ₜ[ℤ] g P.val = Biquadratic.characterSign χ.2.1 • (q ⊗ₜ[ℤ] P.val)) ∧
      (q ⊗ₜ[ℤ] h P.val = Biquadratic.characterSign χ.2.2 • (q ⊗ₜ[ℤ] P.val))
    obtain ⟨h1,h2,h3⟩ := P.property
    rw [h1,h2,h3]
    rcases χ with ⟨a,b,c⟩
    cases a <;> cases b <;> cases c <;>
      simp [Biquadratic.characterSign,TensorProduct.tmul_neg]
  | add x y hx hy =>
    rw [map_add]
    exact Submodule.add_mem _ hx hy

def toCharacterSpace (f g h : G →+ G) (χ : Bool × Bool × Bool) :
    ℚ ⊗[ℤ] characterGroup f g h χ →ₗ[ℚ]
      ThreeCharacter.jointSpace (PointScaling.rationalizeHom f)
        (PointScaling.rationalizeHom g) (PointScaling.rationalizeHom h) χ :=
  (inclusion f g h χ).codRestrict _ (inclusion_mem f g h χ)

def liftProjector (f g h : G →+ G)
    (hf : ∀ P, f (f P)=P) (hg : ∀ P, g (g P)=P) (hh : ∀ P, h (h P)=P)
    (hfg : ∀ P, f (g P)=g (f P)) (hfh : ∀ P, f (h P)=h (f P))
    (hgh : ∀ P, g (h P)=h (g P)) (χ : Bool × Bool × Bool) :
    rationalGroup G →ₗ[ℚ] ℚ ⊗[ℤ] characterGroup f g h χ :=
  (1/8 : ℚ) • PointScaling.rationalizeHom (normToCharacter f g h hf hg hh hfg hfh hgh χ)

theorem inclusion_liftProjector (f g h : G →+ G)
    (hf : ∀ P, f (f P)=P) (hg : ∀ P, g (g P)=P) (hh : ∀ P, h (h P)=P)
    (hfg : ∀ P, f (g P)=g (f P)) (hfh : ∀ P, f (h P)=h (f P))
    (hgh : ∀ P, g (h P)=h (g P)) (χ : Bool × Bool × Bool) (z : rationalGroup G) :
    inclusion f g h χ (liftProjector f g h hf hg hh hfg hfh hgh χ z) =
      ThreeCharacter.projector (PointScaling.rationalizeHom f)
        (PointScaling.rationalizeHom g) (PointScaling.rationalizeHom h) χ z := by
  induction z using TensorProduct.inductionOn with
  | tmul q P =>
    rw [ThreeCharacter.projector_apply]
    rcases χ with ⟨a,b,c⟩
    cases a <;> cases b <;> cases c <;>
      simp [inclusion,liftProjector,normToCharacter,normMap,CharacterRationalization.signed,
        Biquadratic.characterSign,TensorProduct.tmul_add,TensorProduct.tmul_neg] <;> module
  | add x y hx hy => simp only [map_add,hx,hy]

def equivCharacterSpace (f g h : G →+ G)
    (hf : ∀ P, f (f P)=P) (hg : ∀ P, g (g P)=P) (hh : ∀ P, h (h P)=P)
    (hfg : ∀ P, f (g P)=g (f P)) (hfh : ∀ P, f (h P)=h (f P))
    (hgh : ∀ P, g (h P)=h (g P)) (χ : Bool × Bool × Bool) :
    (ℚ ⊗[ℤ] characterGroup f g h χ) ≃ₗ[ℚ]
      ThreeCharacter.jointSpace (PointScaling.rationalizeHom f)
        (PointScaling.rationalizeHom g) (PointScaling.rationalizeHom h) χ :=
  LinearEquiv.ofBijective (toCharacterSpace f g h χ) ⟨
    fun x y he => inclusion_injective f g h χ (congrArg Subtype.val he),
    fun z => ⟨liftProjector f g h hf hg hh hfg hfh hgh χ z.val, by
      apply Subtype.ext
      exact (inclusion_liftProjector f g h hf hg hh hfg hfh hgh χ z.val).trans
        ((ThreeCharacter.projector_on_jointSpace _ _ _ χ χ z.val z.property).trans
          (ite_eq_left rfl))⟩⟩

end
end Z2Z4Rank6.ThreeCharacterRationalization
