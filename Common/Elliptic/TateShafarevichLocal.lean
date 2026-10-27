import Common.Elliptic.TateShafarevich

/-!
# All local restrictions and the Shafarevich–Tate subgroup

The places are the real completion and every prime-adic completion of Q.
Each embedding of algebraic closures induces Mathlib's continuous
restriction on absolute Galois groups. The coefficient map uses that same
embedding on the coordinates of the geometric elliptic points.

Reference: Silverman, The Arithmetic of Elliptic Curves, second edition,
X.4, pp. 331–333. Quantifying closure embeddings is equivalent to fixing one,
by the independence explained in Remark 4.1.1, p. 332.
-/
namespace Common.Elliptic.TateShafarevich
noncomputable section
open WeierstrassCurve
open scoped Classical

inductive RationalPlace
  | real
  | finite (p : ℕ) (prime : p.Prime)

def RationalPlace.completion : RationalPlace → Type
  | .real=>ℝ
  | .finite p hp=>by
      letI : Fact p.Prime := ⟨hp⟩
      exact ℚ_[p]

instance completionField (v : RationalPlace) : Field v.completion := by
  cases v with
  | real => exact inferInstanceAs (Field ℝ)
  | finite p hp =>
      let : Fact p.Prime := ⟨hp⟩
      exact inferInstanceAs (Field ℚ_[p])

instance completionCharZero (v : RationalPlace) : CharZero v.completion := by
  cases v with
  | real => exact inferInstanceAs (CharZero ℝ)
  | finite p hp =>
      let : Fact p.Prime := ⟨hp⟩
      exact inferInstanceAs (CharZero ℚ_[p])

abbrev ClosureEmbedding (v : RationalPlace) :=
  AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure v.completion

/-- Closure embeddings exist at every completion. -/
def chosenClosureEmbedding (v : RationalPlace) : ClosureEmbedding v := IsAlgClosed.lift

def galoisRestriction (v : RationalPlace) (f : ClosureEmbedding v) :
    GaloisGroup v.completion →ₜ* GaloisGroup ℚ := by
  letI : Algebra (AlgebraicClosure ℚ) (AlgebraicClosure v.completion) := f.toAlgebra
  letI : IsScalarTower ℚ (AlgebraicClosure ℚ) (AlgebraicClosure v.completion) :=
    IsScalarTower.of_algebraMap_eq' (by ext q; exact (f.commutes q).symm)
  exact Field.absoluteGaloisGroup.mapOfAlgebra ℚ v.completion

variable (W : WeierstrassCurve ℚ)

def coefficientMap (v : RationalPlace) (f : ClosureEmbedding v) :
    GeometricPoints W ℚ →+ GeometricPoints W v.completion :=
  Affine.Point.map (W' := W.toAffine) f

theorem coefficientMap_action (v : RationalPlace) (f : ClosureEmbedding v)
    (σ : GaloisGroup v.completion) (P : GeometricPoints W ℚ) :
    coefficientMap W v f (action W ℚ (galoisRestriction v f σ) P)=
      action W v.completion σ (coefficientMap W v f P) := by
  let : Algebra (AlgebraicClosure ℚ) (AlgebraicClosure v.completion) := f.toAlgebra
  let : IsScalarTower ℚ (AlgebraicClosure ℚ) (AlgebraicClosure v.completion) :=
    IsScalarTower.of_algebraMap_eq' (by ext q; exact (f.commutes q).symm)
  change Affine.Point.map f
    (Affine.Point.map (((galoisRestriction v f σ).restrictScalars ℚ).toAlgHom) P)=
      Affine.Point.map ((σ.restrictScalars ℚ).toAlgHom) (Affine.Point.map f P)
  rw [Affine.Point.map_map,Affine.Point.map_map]
  have heq : f.comp (((galoisRestriction v f σ).restrictScalars ℚ).toAlgHom)=
      ((σ.restrictScalars ℚ).toAlgHom).comp f := by
    ext a
    exact (σ.restrictScalars ℚ).restrictNormal_commutes (AlgebraicClosure ℚ) a
  exact congrArg (fun j : AlgebraicClosure ℚ→ₐ[ℚ]AlgebraicClosure v.completion=>
    Affine.Point.map (W' := W.toAffine) j P) heq

def cocycleRestriction (v : RationalPlace) (f : ClosureEmbedding v) :
    cocycles W ℚ →+ cocycles W v.completion where
  toFun c := ⟨⟨fun σ=>coefficientMap W v f (c.val (galoisRestriction v f σ)),
    (continuous_of_discreteTopology : Continuous (coefficientMap W v f)).comp
      (c.val.continuous.comp (galoisRestriction v f).continuous)⟩,by
    intro σ τ
    change coefficientMap W v f (c.val (galoisRestriction v f (σ*τ)))=_
    rw [map_mul,c.property,map_add,coefficientMap_action]
    rfl⟩
  map_zero' := by
    ext σ
    change coefficientMap W v f 0=0
    exact map_zero _
  map_add' c d := by
    ext σ
    change coefficientMap W v f
      (c.val (galoisRestriction v f σ)+d.val (galoisRestriction v f σ))=
      coefficientMap W v f (c.val (galoisRestriction v f σ))+
        coefficientMap W v f (d.val (galoisRestriction v f σ))
    exact map_add _ _ _

theorem coboundary_restriction (v : RationalPlace) (f : ClosureEmbedding v) :
    coboundaries W ℚ≤(coboundaries W v.completion).comap (cocycleRestriction W v f) := by
  rintro c ⟨P,hP⟩
  refine ⟨coefficientMap W v f P,?_⟩
  intro σ
  change coefficientMap W v f (c.val (galoisRestriction v f σ))=_
  rw [hP,map_sub,coefficientMap_action]

/-- Restriction of continuous cohomology classes at a rational place. -/
def localRestriction (v : RationalPlace) (f : ClosureEmbedding v) :
    H1 W ℚ →+ H1 W v.completion :=
  QuotientAddGroup.map (coboundaries W ℚ) (coboundaries W v.completion)
    (cocycleRestriction W v f) (coboundary_restriction W v f)

/-- Sha: the intersection of all local restriction kernels. -/
def sha : AddSubgroup (H1 W ℚ) :=
  ⨅ v : RationalPlace,⨅ f : ClosureEmbedding v,(localRestriction W v f).ker

/-- Two-torsion in the Shafarevich–Tate subgroup. -/
def shaTwo : AddSubgroup (sha W) where
  carrier := {x | (2 : ℕ) • x=0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    change (2 : ℕ) • x=0 at hx
    change (2 : ℕ) • y=0 at hy
    change (2 : ℕ) • (x+y)=0
    simp only [two_nsmul] at hx hy ⊢
    calc
      (x+y)+(x+y)=(x+x)+(y+y) := by abel
      _=0 := by rw [hx,hy,zero_add]
  neg_mem' := by
    intro x hx
    change (2 : ℕ) • x=0 at hx
    change (2 : ℕ) • (-x)=0
    simp only [two_nsmul] at hx ⊢
    calc
      (-x)+(-x)=-(x+x) := by abel
      _=0 := by rw [hx,neg_zero]

theorem mem_sha_iff (x : H1 W ℚ) :
    x∈sha W ↔ ∀ (v : RationalPlace) (f : ClosureEmbedding v),
      localRestriction W v f x=0 := by simp [sha]

end
end Common.Elliptic.TateShafarevich
