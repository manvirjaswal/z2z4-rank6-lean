module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Set.Card
public import Mathlib.Tactic

@[expose] public section

/-!
# Finite decoding from an exact matrix kernel certificate

The identity I=N*P+L*M certifies that every vector in ker(M) is reconstructed
from its prescribed free coordinates by N. The set-theoretic consequences transfer covering
constraints to finite decoding sieves.
-/

namespace Z2Z4Rank6.FiniteKernelReconstruction

variable {R : Type*} [CommRing R]
variable {n r f : Type*} [Fintype n] [Fintype r] [Fintype f] [DecidableEq n]
variable (M : Matrix r n R) (N : Matrix n f R) (P : Matrix f n R) (L : Matrix n r R)
variable (hcert : (1 : Matrix n n R)=N*P+L*M)
include hcert

/-- An exact matrix identity reconstructs every kernel vector from
its specified free coordinates. -/
theorem kernel_reconstruction (b : n → R) (hb : M.mulVec b=0) :
    b=N.mulVec (P.mulVec b) := by
  calc
    b=(1 : Matrix n n R).mulVec b := (Matrix.one_mulVec b).symm
    _=(N*P+L*M).mulVec b := congrArg (fun A : Matrix n n R => A.mulVec b) hcert
    _=N.mulVec (P.mulVec b) := by
      rw [Matrix.add_mulVec,←Matrix.mulVec_mulVec,←Matrix.mulVec_mulVec,
        hb,Matrix.mulVec_zero,add_zero]

variable {A : Type*} (S : Set A) (encode : A → n → R) (decode : (n → R) → A)
variable (hdecode : ∀ a∈S, decode (encode a)=a)
variable (hkernel : ∀ a∈S, M.mulVec (encode a)=0)
include hdecode hkernel

/-- Every admissible object is decoded from finitely many free
coefficient coordinates once its encoding lies in the certified kernel. -/
theorem subset_decoded_range :
    S ⊆ Set.range (fun c : f → R => decode (N.mulVec c)) := by
  intro a ha
  refine ⟨P.mulVec (encode a),?_⟩
  calc
    decode (N.mulVec (P.mulVec (encode a)))=decode (encode a) :=
      congrArg decode (kernel_reconstruction M N P L hcert (encode a) (hkernel a ha)).symm
    _=a := hdecode a ha

/-- A proved test restricts the free-coordinate decoding pool. -/
theorem subset_decoded_sieve (test : A → Bool) (htest : ∀ a∈S, test a=true) :
    S ⊆ (fun c : f → R => decode (N.mulVec c)) ''
      {c : f → R | test (decode (N.mulVec c))=true} := by
  intro a ha
  obtain ⟨c,hc⟩ := subset_decoded_range M N P L hcert S encode decode hdecode hkernel ha
  refine ⟨c,?_,hc⟩
  change test (decode (N.mulVec c))=true
  change decode (N.mulVec c)=a at hc
  rw [hc]
  exact htest a ha

/-- Finite coefficient rings and finite free coordinates make the
admissible set finite. -/
theorem finite_of_certificate [Finite R] : S.Finite :=
  (Set.finite_range (fun c : f → R => decode (N.mulVec c))).subset
    (subset_decoded_range M N P L hcert S encode decode hdecode hkernel)

/-- A finite decoding sieve bounds the admissible cardinality. -/
theorem ncard_le_sieve [Finite R] (test : A → Bool) (htest : ∀ a∈S, test a=true) :
    S.ncard ≤ {c : f → R | test (decode (N.mulVec c))=true}.ncard := by
  let g : (f → R) → A := fun c => decode (N.mulVec c)
  let T : Set (f → R) := {c | test (g c)=true}
  have hT : T.Finite := Set.toFinite T
  calc
    S.ncard ≤ (g '' T).ncard := Set.ncard_le_ncard
      (subset_decoded_sieve M N P L hcert S encode decode hdecode hkernel test htest) (hT.image g)
    _ ≤ T.ncard := Set.ncard_image_le hT

/-- Without a further test, the cardinality is at most |R|^|f|. -/
theorem ncard_le_free_card [Finite R] : S.ncard ≤ Nat.card R ^ Fintype.card f := by
  let g : (f → R) → A := fun c => decode (N.mulVec c)
  have hfin : (Set.univ : Set (f → R)).Finite := Set.toFinite _
  calc
    S.ncard ≤ (Set.range g).ncard := Set.ncard_le_ncard
      (subset_decoded_range M N P L hcert S encode decode hdecode hkernel) (Set.finite_range g)
    _ ≤ (Set.univ : Set (f → R)).ncard := by
      rw [←Set.image_univ]
      exact Set.ncard_image_le hfin
    _=Nat.card R ^ Fintype.card f := by
      rw [Set.ncard_univ,Nat.card_fun,Nat.card_eq_fintype_card (α:=f)]

end Z2Z4Rank6.FiniteKernelReconstruction
