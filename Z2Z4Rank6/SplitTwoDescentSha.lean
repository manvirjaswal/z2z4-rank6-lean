import Common.Elliptic.TateShafarevichLocal
import Z2Z4Rank6.SplitDescentImage

/-!
# Split-cover class model and Sha[2]

Silverman, The Arithmetic of Elliptic Curves, second edition, Theorem X.4.2(a),
p. 333, gives the Selmer-to-Sha exact sequence. The coordinates and covering
equations are X.1.4, pp. 314–315; X.3.6, p. 325, identifies the torsor class with
its continuous Galois cocycle. The input below is this composite
specialization to split rational cubics. It retains the coordinate map and
the exact sequence, and refers to the independently defined Sha[2].

The source input uses unrestricted rational covering coefficients. Canonical
squarefree integral representatives and their coordinate-specific support
are proved below using square extraction and local solubility.
-/
namespace Common.Elliptic.TateShafarevich
noncomputable section
open WeierstrassCurve Z2Z4Rank6
open scoped Classical

abbrev SplitSquareClasses := RatSquareClassAdd×RatSquareClassAdd

def RationalCoverEverywhereLocallySoluble (q1 q2 q3 : ℚ) (r2 r3 : ℤ) : Prop :=
  SplitCoverSoluble (q1 : ℝ) (q2 : ℝ) (q3 : ℝ) (r2 : ℝ) (r3 : ℝ) ∧
    ∀ (p : ℕ) [Fact p.Prime],
      SplitCoverSoluble (q1 : ℚ_[p]) (q2 : ℚ_[p]) (q3 : ℚ_[p])
        (r2 : ℚ_[p]) (r3 : ℚ_[p])

/-- Everywhere-local homogeneous two-quadric classes, with arbitrary
nonzero rational coefficients and square product. -/
def rationalLocalClasses (r2 r3 : ℤ) : Set SplitSquareClasses :=
  {c | ∃ q1 q2 q3 : ℚ,q1≠0 ∧ q2≠0 ∧ q3≠0 ∧ IsSquare (q1*q2*q3) ∧
    RationalCoverEverywhereLocallySoluble q1 q2 q3 r2 r3 ∧
    c=(squareClass q1,squareClass q2)}

private theorem rescale_cover {K : Type} [Field K] [CharZero K]
    (q1 q2 q3 s1 s2 s3 : ℚ) (d1 d2 d3 r2 r3 : ℤ)
    (hs1 : s1≠0) (hs2 : s2≠0) (hs3 : s3≠0)
    (h1 : q1=(d1 : ℚ)*s1^2) (h2 : q2=(d2 : ℚ)*s2^2)
    (h3 : q3=(d3 : ℚ)*s3^2)
    (h : SplitCoverSoluble (q1 : K) (q2 : K) (q3 : K) (r2 : K) (r3 : K)) :
    SplitCoverSoluble (d1 : K) (d2 : K) (d3 : K) (r2 : K) (r3 : K) := by
  have hc1 : (q1 : K)=(d1 : K)*(s1 : K)^2 := by exact_mod_cast h1
  have hc2 : (q2 : K)=(d2 : K)*(s2 : K)^2 := by exact_mod_cast h2
  have hc3 : (q3 : K)=(d3 : K)*(s3 : K)^2 := by exact_mod_cast h3
  have hs1K : (s1 : K)≠0 := by exact_mod_cast hs1
  have hs2K : (s2 : K)≠0 := by exact_mod_cast hs2
  have hs3K : (s3 : K)≠0 := by exact_mod_cast hs3
  obtain ⟨z,⟨i,hi⟩,hz1,hz2⟩ := h
  let w : Fin 4→K := ![(s1 : K)*z 0,(s2 : K)*z 1,(s3 : K)*z 2,z 3]
  refine ⟨w,⟨i,?_⟩,?_,?_⟩
  · fin_cases i <;> simpa [w,mul_ne_zero_iff,hs1K,hs2K,hs3K] using hi
  · change (d2 : K)*((s2 : K)*z 1)^2-(d1 : K)*((s1 : K)*z 0)^2=
      (r2 : K)*(z 3)^2
    rw [hc1,hc2] at hz1
    linear_combination hz1
  · change (d3 : K)*((s3 : K)*z 2)^2-(d1 : K)*((s1 : K)*z 0)^2=
      (r3 : K)*(z 3)^2
    rw [hc1,hc3] at hz2
    linear_combination hz2

/-- Canonical support follows from everywhere-local solubility. -/
theorem rationalLocalClasses_subset_fullTwoSelmerClasses (r2 r3 : ℤ) :
    rationalLocalClasses r2 r3⊆fullTwoSelmerClasses r2 r3 := by
  rintro c ⟨q1,q2,q3,hq1,hq2,hq3,hsq,hloc,hc⟩
  obtain ⟨d1,s1,hd1,hs1,h1⟩ := rat_exists_squarefree_factor q1 hq1
  obtain ⟨d2,s2,hd2,hs2,h2⟩ := rat_exists_squarefree_factor q2 hq2
  obtain ⟨d3,s3,hd3,hs3,h3⟩ := rat_exists_squarefree_factor q3 hq3
  let d : ECFullTriple := (d1,d2,d3)
  have hdprod : IsSquare (d1*d2*d3) := by
    apply Rat.isSquare_intCast_iff.mp
    obtain ⟨n,hn⟩ := hsq
    refine ⟨n/(s1*s2*s3),?_⟩
    push_cast
    field_simp
    rw [h1,h2,h3] at hn
    linear_combination hn
  have hdloc : SplitCoverEverywhereLocallySoluble d r2 r3 := by
    constructor
    · exact rescale_cover q1 q2 q3 s1 s2 s3 d1 d2 d3 r2 r3
        hs1 hs2 hs3 h1 h2 h3 hloc.1
    · intro p hp
      exact rescale_cover q1 q2 q3 s1 s2 s3 d1 d2 d3 r2 r3
        hs1 hs2 hs3 h1 h2 h3 (hloc.2 p)
  obtain ⟨hdiv1,hdiv2,hdiv3⟩ := splitCover_support_all d r2 r3 hd1 hd2 hd3 hdprod hdloc
  refine ⟨d,⟨hd1,hd2,hd3,hdiv1,hdiv2,hdiv3,hdprod,hdloc⟩,?_⟩
  apply Prod.ext
  · exact (squareClass_eq_of_factor q1 d1 s1 hq1
      (by exact_mod_cast hd1.ne_zero) hs1 h1).symm.trans (congrArg Prod.fst hc).symm
  · exact (squareClass_eq_of_factor q2 d2 s2 hq2
      (by exact_mod_cast hd2.ne_zero) hs2 h2).symm.trans (congrArg Prod.snd hc).symm

theorem rationalLocalClasses_eq_fullTwoSelmerClasses (r2 r3 : ℤ) :
    rationalLocalClasses r2 r3=fullTwoSelmerClasses r2 r3 := by
  apply Set.Subset.antisymm (rationalLocalClasses_subset_fullTwoSelmerClasses r2 r3)
  rintro c ⟨d,hd,rfl⟩
  refine ⟨(d.1 : ℚ),(d.2.1 : ℚ),(d.2.2 : ℚ),?_,?_,?_,?_,?_,rfl⟩
  · exact_mod_cast hd.1.ne_zero
  · exact_mod_cast hd.2.1.ne_zero
  · exact_mod_cast hd.2.2.1.ne_zero
  · exact_mod_cast hd.2.2.2.2.2.2.1
  · simpa only [RationalCoverEverywhereLocallySoluble,
      SplitCoverEverywhereLocallySoluble,Rat.cast_intCast] using
      hd.2.2.2.2.2.2.2

/-- Silverman X.4.2(a), with X.1.4's split covering coordinates and
X.3.6's continuous Galois cohomology. This is a generic composite source
input over Q. -/
def SilvermanSplitTwoDescentExactSequence : Prop :=
  ∀ (W : WeierstrassCurve ℚ) (r2 r3 : ℤ),r2≠0 → r3≠0 → r2≠r3 →
    GoodCurve W → W=splitWeierstrass 0 (-(r2 : ℚ)) (-(r3 : ℚ)) →
    ∃ S : AddSubgroup SplitSquareClasses,
      (S : Set SplitSquareClasses)=rationalLocalClasses r2 r3 ∧
      ∃ κ : RationalPoints W→+S,
        (∀ P,(κ P).val=completeDescentCoordinates W 0 (-(r2 : ℚ)) (-(r3 : ℚ)) P) ∧
        (∀ P,κ P=0 ↔ ∃ Q : RationalPoints W,(2 : ℕ) • Q=P) ∧
        ∃ δ : S→+shaTwo W,Function.Surjective δ ∧ δ.ker=κ.range

/-- Exhausting the everywhere-local class set by rational
descent coordinates makes the cohomological Sha[2] trivial. -/
theorem shaTwo_subsingleton_of_fullClasses_eq_descent_image
    (hExact : SilvermanSplitTwoDescentExactSequence)
    (W : WeierstrassCurve ℚ) (r2 r3 : ℤ)
    (hr2 : r2≠0) (hr3 : r3≠0) (hr23 : r2≠r3)
    (hW : GoodCurve W) (hSplit : W=splitWeierstrass 0 (-(r2 : ℚ)) (-(r3 : ℚ)))
    (hClasses : fullTwoSelmerClasses r2 r3=
      Set.range (completeDescentCoordinates W 0 (-(r2 : ℚ)) (-(r3 : ℚ)))) :
    Subsingleton (shaTwo W) := by
  obtain ⟨S,hS,κ,hκ,_hker,δ,hδ,hδker⟩ := hExact W r2 r3 hr2 hr3 hr23 hW hSplit
  have zero_all (x : shaTwo W) : x=0 := by
    obtain ⟨s,rfl⟩ := hδ x
    have hs : s.val∈fullTwoSelmerClasses r2 r3 := by
      rw [←rationalLocalClasses_eq_fullTwoSelmerClasses,←hS]
      exact s.property
    rw [hClasses] at hs
    obtain ⟨P,hP⟩ := hs
    have hκP : κ P=s := Subtype.ext ((hκ P).trans hP)
    have hsKer : s∈δ.ker := by rw [hδker]; exact ⟨P,hκP⟩
    exact hsKer
  exact ⟨fun x y=>(zero_all x).trans (zero_all y).symm⟩

end
end Common.Elliptic.TateShafarevich
