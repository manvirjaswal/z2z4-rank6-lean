# Lean formalization: Infinitely many elliptic curves with torsion Z/2Z × Z/4Z and rank at least six

This package contains Lean 4 proofs for Manvir Jaswal, *Infinitely many elliptic curves with torsion Z/2Z × Z/4Z and rank at least six*, [DOI 10.5281/zenodo.23437117](https://doi.org/10.5281/zenodo.23437117) (all versions). Numbers refer to the printed paper.

All 19 numbered results are proved. Lemmas 2.1, 2.2 and 3.2, Proposition 4.2 and Remark 4.3 use Mathlib alone; the other fourteen assume published theorems of other authors, passed as explicit hypotheses and listed under "Hypotheses" below. Nothing from the paper itself is assumed: its ranks, points, independence statements, genera, conductors and local computations are all proved.

## What is proved

**Theorem 1.1.** Infinitely many elliptic curves over Q have torsion subgroup Z/2Z × Z/4Z and rank at least six, with infinitely many distinct j-invariants, hence infinitely many isomorphism classes. It assumes Mazur's torsion theorem, the integrality of odd-prime torsion, the reduction homomorphism at good primes, and the compact group structure of E(Q_p).

**Theorem 1.2.** The smooth projective model of C: u² = 5(3m² + 242), v² = 5(2m² + 243) has genus one and infinitely many rational points, and is isomorphic over Q to E_C: y² = x³ + x² − 137620x − 10504000, which has conductor 9240 and rank one; every rational point of the projective model lies in the affine chart. The six sections of X: y² = x(x + a²)(x + b²) are independent over Q(C), and the rank of X over Q(C) is exactly six. Away from the sixteen points (±1, ±35, ±35) and (±99, ±385, ±315), with independent signs, every fiber is elliptic with torsion containing Z/2Z × Z/4Z, and all but finitely many rational points of C give exact torsion Z/2Z × Z/4Z and rank at least six; as in the paper, the finite exceptional set is not determined.

**Theorem 8.1.** The second base curve G₂ is a smooth projective curve of genus one with infinitely many rational points; its Jacobian has conductor 182747931661680, torsion Z/2Z × Z/4Z and rank two. The six points of F(Q(G₂)) are independent. The sixteen rational points with W = 1 or W = λ² give singular fibers; every other fiber is elliptic with torsion containing Z/2Z × Z/4Z, all but finitely many have exact torsion and rank at least six, and infinitely many are pairwise non-isomorphic. At the point with s₁ = 23306521/20091929 the fiber is isomorphic over Q to E_{a,b} with (a, b) = (460019200, 11180308689), with exact torsion and six independent specialized points.

The other results include the exact generic ranks three (Proposition 2.3) and five (Proposition 7.2), the twist ranks and finite index of the six sections, the signed covers of genus 17 and 9 used with Faltings' theorem, the relatively minimal elliptic K3 surface of Lemma 3.1 with its nine singular fibers and Euler number 24, and the lift of n ↦ 9801/n to an automorphism of the whole surface. The numerical examples have the printed exact ranks and complete two-Selmer dimensions: rank nine in Proposition 7.1 (nine rational points and a two-descent bound); rank six and dimension eight at c₀ and at the G-fiber m = 291/53; rank seven and dimension nine for the second example; Ш[2] = 0 for the G-fiber and the second example. Section 7's further arguments (the family over G with exact torsion and rank at least five outside finitely many base points, with infinitely many j-invariants; the third twist q₃ = 4m² + 45, whose twists by q₃, q₃q₁, q₃q₂, q₃q₁₂ have generic ranks 1, 0, 0, 0 and, at the printed fibers, Selmer dimensions 3, 2, 2, 2, whose genus-one bases give rank five and whose genus-five base gives rank seven and finitely many rational points) and the descent dimensions of the original points with torsion (six at c₀, with a basis of dimension eight from two explicit halvings, as in the appendix; five for the six points of Theorem 8.1(d)) are also proved.

The main statements follow, copied from the Lean files. The definitions they use are explained under "Objects in the statements" and the hypotheses under "Hypotheses".

### Theorem 1.1

Module: `Z2Z4Rank6.Main`.

```lean
theorem theorem_1_1
    (hMazur : MazurTorsionTheorem)
    (hSilvermanVII34 : OddPrimeTorsionIntegrality)
    (hReduction : GoodReductionHomomorphisms)
    (hLocal : LocalEllipticTopology) : Theorem11
```

### Theorem 1.2(a)

Module: `Z2Z4Rank6.FirstBaseGeometry`.

```lean
theorem theorem_1_2_a
    (hCohom : AffineCoverStructureSheafCohomologyTheorem)
    (hGeo : SmoothProperGlobalConstantsGeometricIntegralityTheorem)
    (hIso : SmoothProperCurveFunctionFieldIsomorphismTheorem)
    (hMW : MordellWeilTheorem) (hDescent : CompleteTwoDescentTheorem)
    (hOdd : OddPrimeTorsionIntegrality)
    (hModels : EllipticMinimalModelsTheorem) (h21 : Theorem21Components)
    (hOddComponents : Theorems23And24SemistableComponents) :
    GeometricallyIntegral ProjectiveBaseScheme.structureMap ∧
      IsProper ProjectiveBaseScheme.structureMap ∧
      SmoothOfRelativeDimension 1 ProjectiveBaseScheme.structureMap ∧
      topologicalKrullDim ProjectiveBaseScheme.scheme = 1 ∧
      Function.Bijective (StructureSheafCohomology.qToGlobal
        ProjectiveBaseScheme.scheme ProjectiveBaseScheme.structureMap) ∧
      FiniteDimensional ℚ (StructureSheafCohomology.H1
        ProjectiveBaseScheme.scheme ProjectiveBaseScheme.structureMap) ∧
      Module.finrank ℚ (StructureSheafCohomology.H1
        ProjectiveBaseScheme.scheme ProjectiveBaseScheme.structureMap) = 1 ∧
      Infinite ProjectiveBaseSchemeRationalPoints.RationalPoint ∧
      Nonempty {e : ProjectiveBaseScheme.scheme ≅ ECProjectiveScheme.scheme //
        e.hom ≫ ECProjectiveScheme.structureMap = ProjectiveBaseScheme.structureMap} ∧
      PrintedModelConductorData.conductor hModels 0 = 9240 ∧
      Module.rank ℤ (RationalPoints EC) = 1 ∧
      Function.Bijective ProjectiveBaseSchemeRationalPoints.fromAffine
```

### Theorem 1.2(b)

Module: `Z2Z4Rank6.RankSixExact`.

```lean
theorem theorem_1_2_b (hMazur : MazurTorsionTheorem)
    (hReduction : GoodReductionHomomorphisms) (hFormal : FormalGoodReductionHomomorphisms)
    (hGT : GusicTadic.GusicTadicTheorem11) (hMW : MordellWeilTheorem)
    (hDescent : CompleteTwoDescentTheorem) : Theorem12b
```

### Theorem 1.2(c)

Module: `Z2Z4Rank6.FirstFamilyCofinite`.

```lean
theorem theorem12c
    (hSilverman : SilvermanRigidSpecializationTheorem.{0})
    (hMazur : MazurTorsionTheorem) (hReduction : GoodReductionHomomorphisms)
    (hFormal : FormalGoodReductionHomomorphisms)
    (hCohom : AffineCoverStructureSheafCohomologyTheorem)
    (hGeo : SmoothProperGlobalConstantsGeometricIntegralityTheorem)
    (hF : FaltingsProperCurveTheorem) : Theorem12c
```

### Theorem 8.1(a)

Module: `Z2Z4Rank6.SecondBaseJacobianArithmetic`.

```lean
theorem theorem_8_1_a
    (hGenus : QuadricIntersectionModel.CFSTheorem28ii)
    (hJacobian : QuadricIntersectionModel.CFSTheorem28iii)
    (hCubic : GenusOneModelTheorem.CFSTheorem28iiDegreeOne)
    (hGroup : WeierstrassScheme.MilneRegularGroupLaw) (hRigidity : MilneCorollary22)
    (hMW : MordellWeilTheorem) (hMazur : MazurTorsionTheorem)
    (hDescent : CompleteTwoDescentTheorem) (hTorsionIntegral : OddPrimeTorsionIntegrality)
    (hModels : EllipticMinimalModelsTheorem) (h21 : Theorem21Components)
    (hOdd : Theorems23And24SemistableComponents) :
    RationalCurveGenus.IsSmoothProperGenusOne
      SecondBaseProjectiveScheme.scheme SecondBaseProjectiveScheme.structureMap ∧
    Infinite SecondBaseProjectiveRationalPoints.RationalPoint ∧
    PrintedModelConductorData.conductor hModels 2=182747931661680 ∧
    ∃ P : Presentation (Over.mk SecondBaseProjectiveScheme.structureMap)
        (Over.mk (WeierstrassScheme.structureMap J2)),
      Module.rank ℤ P.abelian.Points=2 ∧
      Nonempty (AddCommGroup.torsion P.abelian.Points ≃+ (ZMod 2 × ZMod 4))
```

### Theorem 8.1(b)

Module: `Z2Z4Rank6.SecondFunctionFieldCharactersW4`.

```lean
theorem theorem_8_1_b_via_W4
    (hOdd : OddPrimeTorsionIntegrality) (hReduction : GoodReductionHomomorphisms)
    (hDescent : CompleteTwoDescentTheorem) (hFormal : FormalGoodReductionHomomorphisms) :
    LinearIndependent ℤ points ∧ 6≤Module.rank ℤ (SecondFamily.F W).toAffine.Point
```

### Theorem 8.1(c)

Module: `Z2Z4Rank6.SecondFamilyCofinite`.

```lean
theorem theorem_8_1_c
    (hSilverman : SilvermanRigidSpecializationTheorem.{0})
    (hMazur : MazurTorsionTheorem) (hReduction : GoodReductionHomomorphisms)
    (hFormal : FormalGoodReductionHomomorphisms)
    (hCohom : AffineCoverStructureSheafCohomologyTheorem)
    (hGeo : SmoothProperGlobalConstantsGeometricIntegralityTheorem)
    (hF : FaltingsProperCurveTheorem) (hOdd : OddPrimeTorsionIntegrality) :
    {P : G2Point ℚ | ¬GoodCurve (F P.W)}.ncard=16 ∧
    (∀ P : G2Point ℚ,P∉Set.range singularPoint → GoodCurve (F P.W) ∧ TorsionContains (F P.W)) ∧
    {P : G2Point ℚ | ¬DesiredCurve (F P.W)}.Finite ∧
    ((fun P : G2Point ℚ => jValue (F P.W)) '' {P | DesiredCurve (F P.W)}).Infinite
```

### Theorem 8.1(d)

Module: `Z2Z4Rank6.SecondExampleArithmetic`.

```lean
theorem theorem_8_1_d
    (hMazur : MazurTorsionTheorem) (hReduction : GoodReductionHomomorphisms)
    (hModels : EllipticMinimalModelsTheorem) (hTate : CremonaTateSteps4And19to21) :
    basePoint.s1=23306521/20091929 ∧
    Nonempty (Over.mk (WeierstrassScheme.structureMap SecondExampleRankSeven.curve) ≅
      Over.mk (WeierstrassScheme.structureMap (F baseW))) ∧
    TorsionExact (F baseW) ∧ LinearIndependent ℤ fiberPoints ∧
    SecondExampleConductor.conductor hModels=55712032256650048538220027355278990 ∧
    Squarefree (SecondExampleConductor.conductor hModels)
```

## Objects in the statements

A rank or genus in the statements is computed on the object below, not built into its definition.

| Lean definition | Meaning and place in the paper |
|---|---|
| `a`, `b` in `Z2Z4Rank6/Basic.lean` | Equation (1.1): a = 7(m − 99)(m + 1)(m − 11)(m + 9), b = −7(m + 99)(m − 1)(m + 11)(m − 9). |
| `E`, `X`, `EC` | Weierstrass equations: E_{a,b}: y² = x(x + a²)(x + b²); X is equation (1.2); EC is the cubic in Theorem 1.2(a). |
| `CPoint`; `ProjectiveBaseScheme.scheme` | Equation (1.3): the rational triples satisfying both equations; and the Proj of their homogeneous quotient ring. The rational points of the scheme are proved to correspond to these triples through the affine chart. |
| `RationalPoints W`; `GoodCurve W` | Mathlib's group of nonsingular points of W, with the point at infinity; W is elliptic when its discriminant is nonzero. |
| `TorsionExact W`; `TorsionContains W` | An additive isomorphism from the whole rational torsion subgroup onto Z/2Z × Z/4Z; an injective homomorphism of Z/2Z × Z/4Z into it. |
| `RankAtLeastSix W`; `DesiredCurve W` | Six rational points linearly independent over Z; ellipticity, exact torsion and that independence together. Exact ranks use Mathlib's `Module.rank`. |
| `jValue` | c₄³/Δ, proved equal to Mathlib's j-invariant on every elliptic equation. |
| `FunctionField.K`; `SecondFunctionField.K` | Iterated quadratic extensions with the displayed radical relations, of degree four over Q(m) and eight over Q(W). The first is proved isomorphic over Q to the function field of `ProjectiveBaseScheme.scheme`, matching m, u, v (`ProjectiveBaseSchemeFunctionField.functionFieldEquiv`). The second is proved isomorphic over Q to Mathlib's function field of J₂ (`SecondBaseMathlibFunctionFieldIso`); for the G₂ scheme what is proved is the correspondence of rational points (`SecondBaseProjectivePointEquiv`), not a comparison of function fields. |
| `FunctionField.points`; `SecondFunctionField.points` | The six points of Proposition 4.2 and Theorem 8.1(b), with their printed coordinates; linear independence is about these points. |
| `SecondFamily.F`, `U`, `V`, `lambda`, `beta`, `gamma` | Equation (8.1): F: y² = x(x² + Ux + V²), U = 2(1 + λ)²W + 2(W + λ)², V = −(W − 1)(W − λ²), λ = 361/1089, β = (161/1089)², γ = (361/161)². |
| `SecondBaseProjectiveScheme`; `SecondFamily.G2Point` | The Proj of the two quadrics, and the rational solutions of W = s₁², s₂² = 29(W − β), s₃² = −29β(W − γ). Their rational points are proved to correspond. |
| `Jacobian.Presentation`; `AbelianVariety.Points` | A Jacobian, characterized by the Albanese universal property of the basepoint-free difference map; and the group of rational sections of its abelian variety. Its identification with the printed Weierstrass group respects the group laws. |
| `StructureSheafCohomology.H1` | Ext¹ from the constant sheaf Q to the structure sheaf, in sheaves of Q-vector spaces. A genus is its dimension, on a curve proved proper, smooth and geometrically integral with Q → H⁰(O) bijective. |
| `TorsionCoverProjective`; `SecondTorsionCoverProjective` | The proper signed covers used in the Faltings arguments of Theorems 1.2(c) and 8.1(c), given by graded quotient rings and charts; their H¹ dimensions are 17 and 9. |
| `SurfaceRationalData.curve`; `SurfaceModel.RegularModel` | Equation (3.1) over Q(n); and a regular, proper, smooth, geometrically integral surface over a field k, flat over P¹_k, with an isomorphism of its generic fiber with the curve. Relative minimality quantifies over birational morphisms over P¹. |
| `NeronPolygon.IsTypeI`; `ComplexPointsTopology.euler`; `IsK3` | Fibers that are cycles of projective lines; the singular-homology Euler characteristic of the complex points; a smooth proper surface with trivial canonical sheaf and H¹(O) = 0. |
| `GeometricConductor` | Ogg's formula: at each prime, the valuation of the minimal discriminant plus one minus the number of geometric irreducible components of the special fiber of the minimal regular proper model (hypotheses 13–16). No Artin or Swan conductor is constructed. In `PrintedModelConductorData.conductor hModels i`, index 0 is E_C, 1 is J_G (Proposition 7.2(a)) and 2 is J_2 (Theorem 8.1(a)). |
| `fullTwoSelmerClasses` | The pairs in (Q*/Q*²)² whose intersection of two quadrics is soluble over R and every Q_p, with squarefree integral representatives and proved restrictions on their prime support. The stated Selmer dimensions refer to this set. |
| `TateShafarevich.H1`, `sha`, `shaTwo` | Continuous 1-cocycles of the absolute Galois group acting on the algebraic points, modulo coboundaries; the intersection of the kernels of restriction to R and every Q_p, over all embeddings of the algebraic closures; its 2-torsion. The comparison with 2-coverings is hypothesis 56. |

`Statements.lean` defines `Theorem11` and `Theorem12c`, and `FirstFunctionFieldStatements.lean` defines `Theorem12b`; Theorem 1.2(a) is stated in full above. `Audit.lean` prints the statements and their axioms, then the defining polynomials and the field degree.

## Numbered results

| Paper | Assertion | Lean declarations |
|---|---|---|
| 1.1 | Infinitely many elliptic curves over Q with exact torsion and rank at least six; infinitely many j-invariants. | `theorem_1_1` |
| 1.2 | First base genus, isomorphism, conductor and rank; exact generic rank six; cofinite specialization. | `FirstBaseGeometry.theorem_1_2_a`, `theorem_1_2_b`, `FirstFamilyCofinite.theorem12c` |
| 2.1 | The printed Dujella–Peral parameter and coefficient changes. | `dp_parameter_isomorphism` |
| 2.2 | The three rational sections and their square identities. | `p1_affine_equation`, `p2_affine_equation`, `p3_affine_equation`, `p1x_add_a_sq`, `p1x_add_b_sq`, `p2x_add_a_sq`, `p2x_add_b_sq`, `p3x_add_a_sq`, `p3x_add_b_sq` |
| 2.3 | Exact rank three over Q(m) and independence of the three points. | `RationalFunctionFamily.rank_eq_three`, `RationalFunctionFamily.points_linearIndependent` |
| 3.1 | Point of order four and its double, discriminant, singular fibers, the minimal K3 surface, and an automorphism of the surface lifting the base involution. | `surfaceS_sub_twoW`, `surfaceS_add_twoW`, `surfacePointFour_order`, `surfacePointFour_double`, `EllipticSurfaceK3.lemma_3_1_b`, `SurfaceInvolution.lemma_3_1_c`, `surfaceS_involution`, `surfaceW_involution`, `SurfaceInvolution.complete_k3_surface_automorphism` |
| 3.2 | Quadratic-section equations and the reciprocal identities. | `t4_equation`, `t5_equation`, `t6_equation`, `q2_involution`, `t4x_involution`, `t4y_involution` |
| 4.1 | The projective base, a rational point, its isomorphism with E_C, conductor 9240, rank and torsion. | `ProjectiveBaseSchemeGenus.lemma_4_1_a`, `FirstBaseJacobianArithmetic.lemma_4_1_b` |
| 4.2 | The six sections over the degree-four function field. | `FunctionField.points`, `six_affine_equations`, `p4x_formula`, `p5x_formula`, `p6x_formula` |
| 4.3 | The Klein-four field action, character decomposition and twist identifications. | `FunctionField.isGalois`, `FunctionField.galoisEquivKleinFour`, `FunctionField.rationalPoints_mem_characterSpace`, `FunctionField.pointGroup_rank_character_decomposition`, `FunctionField.TwistCharacters.fourTwistEquiv` |
| 5.1 | Independence of the six points by the printed reduction matrix. | `FunctionField.points_independent` |
| 5.2 | Three twist ranks one, total rank six, finite index of the six sections. | `proposition_5_2` |
| 6.1 | Exact torsion criterion for the split model. | `E_torsion_exact` |
| 6.2 | The congruence set is infinite, and the six sections stay independent on it. | `proposition_6_2_full` |
| 6.3 | Counts of representatives of the two families, with the printed logarithmic exponents. | `FirstCurveRepresentativeCounting.remark_6_3_first_family`, `SecondCurveRepresentativeCounting.remark_6_3_second_family` |
| 7.1 | Conic family, generic rank at least four and exact rank-nine numerical fiber. | `ConicFamilyRank.proposition_7_1` |
| 7.2 | The genus-one base G and the arithmetic of its Jacobian; twist rank two and generic rank five. | `GJacobianGeometry.proposition_7_2_a`, `GExactRank.rank_eq_five`, `GExactRank.printed_five_finite_index`, `proposition_7_2_b_full` |
| 8.1 | Second family: the base G₂ and its Jacobian, six sections, cofinite fibers and the numerical example. | `SecondBaseJacobianArithmetic.theorem_8_1_a`, `SecondFunctionField.theorem_8_1_b_via_W4`, `SecondFamilyCofinite.theorem_8_1_c`, `SecondExampleArithmetic.theorem_8_1_d`, `SecondTorsionCoverGenus.genus_nine` |
| 8.2 | An explicit infinite set of base points in a 3-adic neighborhood for the second family, proved without Faltings' theorem. | `remark_8_2`, `theorem_1_1_from_second_family` |

## Hypotheses

The theorems take the published results below as hypotheses. Each is a Lean proposition passed as an explicit argument (no axioms are added) and is generic, about no curve or surface of the paper; the structure `Common.Elliptic.SurfaceDescentSources.PublishedInputs` bundles hypotheses 34–49 for Lemma 3.1.

### Elliptic curves (1–12)

**1. `Z2Z4Rank6.MazurTorsionTheorem`.** For every elliptic Weierstrass equation W over Q, the torsion subgroup of W(Q) is isomorphic to Z/nZ with 1 ≤ n ≤ 10 or n = 12, or to Z/2Z × Z/2nZ with 1 ≤ n ≤ 4.

Source: [Barry Mazur, Modular curves and the Eisenstein ideal, Publ. Math. IHÉS 47 (1977), 33–186, Theorem (8) (also III, Theorem 5.1), 35](https://www.numdam.org/article/PMIHES_1977__47__33_0.pdf).

**2. `Z2Z4Rank6.OddPrimeTorsionIntegrality`.** Let W be an elliptic Weierstrass equation over Q with integral coefficients (not necessarily minimal), p an odd prime, and (x, y) an affine rational point of finite order. Then p does not divide the denominator of x.

Source: [Joseph H. Silverman, The Arithmetic of Elliptic Curves, second edition, GTM 106, Springer (2009), Theorem VII.3.4; Application VII.3.5, 193–194](https://doi.org/10.1007/978-0-387-09494-6).

Specialized from local fields to Q (along Q → Q_p, which preserves orders) and to odd p; parts (a) and (b) of the source cover orders that are not powers of p and powers of p. Only the denominator of x is used.

**3. `Z2Z4Rank6.GoodReductionHomomorphisms`.** For every prime p and elliptic Weierstrass equation W over Q whose coefficients are p-integral and whose reduction W̃ mod p is elliptic over F_p, there is a homomorphism W(Q) → W̃(F_p) sending each affine point with p-integral coordinates to the point given by their residues.

Source: [Joseph H. Silverman, The Arithmetic of Elliptic Curves, second edition, GTM 106, Springer (2009), Proposition VII.2.1, with good-reduction discussion, 187–191](https://doi.org/10.1007/978-0-387-09494-6); [Tom Fisher; lecture notes taken by Leonard Tomczak, Elliptic Curves, Cambridge Part III, Lent 2023, Proposition 9.5 and reduction definition, 27–28](https://math.berkeley.edu/~ltomczak/notes/Lent2023/EC_Notes.pdf).

Restricted from Q_p to Q; such a model is minimal at p, its discriminant being a p-adic unit. Only the homomorphism is used, not surjectivity or injectivity on prime-to-p torsion; its values at points with non-integral coordinates are not specified.

**4. `Z2Z4Rank6.FormalGoodReductionHomomorphisms`.** For every field F of characteristic 0 and Weierstrass equation W over F[[T]] such that W is elliptic over F((T)) and its reduction W₀ (constant terms) is elliptic over F, there is a homomorphism W(F((T))) → W₀(F) sending each affine point with coordinates in F[[T]] to the point given by their constant terms.

Source: [Joseph H. Silverman, The Arithmetic of Elliptic Curves, second edition, GTM 106, Springer (2009), Proposition VII.2.1; standing hypotheses of Chapter VII, 185, 187–191](https://doi.org/10.1007/978-0-387-09494-6).

The source applied to the complete discrete valuation ring F[[T]] with residue field F (perfect, as char F = 0); W is minimal since its discriminant is a unit. The premise that W is elliptic over F((T)) follows from the others. Surjectivity is not used.

**5. `Z2Z4Rank6.LocalEllipticTopology`.** For every prime p and elliptic Weierstrass equation W over Q_p, the group W(Q_p) has a compact topological group structure in which the inclusion of the affine solutions (x, y) ∈ Q_p², with the subspace topology, is an open embedding.

Source: [James S. Milne, Elliptic Curves, second edition (2021), II §4, proof of Theorem 4.1(a), 62–63](https://jmilne.org/math/Books/EC2.pdf); [Tom Fisher; lecture notes taken by Leonard Tomczak, Elliptic Curves, Cambridge Part III, Lent 2023, proof of Lemma 9.8, 29](https://math.berkeley.edu/~ltomczak/notes/Lent2023/EC_Notes.pdf).

Combined, not the statement of Milne's Theorem II.4.1(a) (which says that E(Q_p)/E₀(Q_p) is finite): compactness is in its proof, continuity of the group law in Fisher–Tomczak, and the open embedding is the affine chart Z ≠ 0 of the projective topology.

**6. `Z2Z4Rank6.MordellWeilTheorem`.** For every elliptic Weierstrass equation W over Q, the group W(Q) is finitely generated.

Source: [Joseph H. Silverman, The Arithmetic of Elliptic Curves, second edition, GTM 106, Springer (2009), Theorem VIII.4.1, 220](https://doi.org/10.1007/978-0-387-09494-6).

**7. `Z2Z4Rank6.MordellWeilLangNeronTheorem`.** For every field F containing Q and generated over Q by finitely many elements (as a field), and every elliptic Weierstrass equation W over F, the group W(F) is finitely generated.

Source: [Brian Conrad, Chow's K/k-image and K/k-trace, and the Lang–Néron theorem, Enseign. Math. (2) 52 (2006), 37–108, Corollary 7.2, deduced from Theorem 7.1 and number-field Mordell–Weil, p. 23 of the author's manuscript](https://math.stanford.edu/~conrad/papers/Kktrace.pdf).

Specialized to elliptic curves in characteristic 0; the source covers abelian varieties in any characteristic.

**8. `Z2Z4Rank6.CompleteTwoDescentTheorem`.** For every elliptic equation E: y² = (x − e₁)(x − e₂)(x − e₃) over Q there is a homomorphism κ: E(Q) → (Q*/Q*²)² with kernel 2E(Q), given by κ(x, y) = (x − e₁, x − e₂) for x ≠ e₁, e₂, κ(e₁, 0) = ((e₁ − e₃)/(e₁ − e₂), e₁ − e₂), κ(e₂, 0) = (e₂ − e₁, (e₂ − e₃)/(e₂ − e₁)) and κ(O) = (1, 1).

Source: [Joseph H. Silverman, The Arithmetic of Elliptic Curves, second edition, GTM 106, Springer (2009), Proposition X.1.4 (Complete 2-Descent), 315](https://doi.org/10.1007/978-0-387-09494-6).

The source's injection E(Q)/2E(Q) → Q(S, 2)², composed with the quotient map and the inclusion into (Q*/Q*²)². Its description of the image (local solubility, support in S) is not used.

**9. `Z2Z4Rank6.GusicTadic.GusicTadicTheorem11`.** Let e₁, e₂, e₃ ∈ Z[t] give an elliptic curve E: y² = (x − e₁)(x − e₂)(x − e₃) over Q(t) that is not isomorphic over Q(t) to a curve defined over Q, and let r ∈ Q. If for each i every nonconstant squarefree g ∈ Z[t] dividing (e_i − e_j)(e_i − e_k) has g(r) not a square in Q, then the specialization map E(Q(t)) → E_r(Q) is an injective homomorphism.

Source: [Ivica Gusić and Petra Tadić, Injectivity of the specialization homomorphism of elliptic curves, J. Number Theory 148 (2015), 137–152; arXiv:1409.7189v2, Theorem 1.1 and Introduction's nonconstant definition, 1–2](https://arxiv.org/pdf/1409.7189v2).

The specialization map is fixed explicitly: it evaluates the coordinates of a point, as reduced rational functions, at r when both are regular there, and sends the point to O otherwise. "Not isomorphic to a curve over Q" is the source's definition of nonconstant.

**10. `Z2Z4Rank6.SilvermanRigidSpecializationTheorem`.** Let K be a finite extension of Q(t) and W an elliptic Weierstrass equation over K whose j-invariant is transcendental over Q. Then specialization is injective at all but finitely many good normalized rational places of K. Such a place is a triple (c, ι, W′) with c ∈ Q, ι: K → Q((T)) a Q-embedding with ι(t) = c + T, and W′ an equation over Q[[T]] with image ι(W) whose reduction mod T is elliptic; specialization at it is base change along ι followed by reduction mod T, and injective means that this map, defined on all of W(K), is an injective homomorphism.

Source: [Joseph H. Silverman, The Arithmetic of Elliptic Curves, second edition, GTM 106, Springer (2009), Appendix C §20, Theorem 20.3; preceding specialization definition, 456–457](https://doi.org/10.1007/978-0-387-09494-6); [The Stacks Project Authors, The Stacks Project, Theorem 53.2.6 and Lemma 53.2.8, online tags 0BY1 / section 0BXX](https://stacks.math.columbia.edu/tag/0BXX); [The Stacks Project Authors, The Stacks Project, Lemma 10.160.10(2), online tag 0323](https://stacks.math.columbia.edu/tag/0323).

Not a verbatim theorem: the source is stated for rational points of a curve, and these places correspond to the rational points of the smooth projective model of K at which t − c is a uniformizer (the Stacks results); this correspondence is part of the hypothesis, not proved in Lean. Transcendental j is a special case of the source's hypothesis.

**11. `Z2Z4Rank6.FaltingsProperCurveTheorem`.** Let X be a scheme with a morphism s: X → Spec Q that is proper, smooth and geometrically integral, with dim X = 1, Q → H⁰(X, O_X) bijective, H¹(X, O_X) finite-dimensional and dim_Q H¹(X, O_X) ≥ 2. Then X has finitely many rational points (sections of s).

Source: [Gerd Faltings, Endlichkeitssätze für abelsche Varietäten über Zahlkörpern, Invent. Math. 73 (1983), 349–366, Satz 7 (Mordell-Vermutung), 365](https://doi.org/10.1007/BF01388432); [Michael Stoll, Rational points on curves (19 September 2015), §1.1, Theorem 1.1, 1](https://www.mathe2.uni-bayreuth.de/stoll/papers/Hay-on-Wye-2015.pdf); [The Stacks Project Authors, The Stacks Project, Theorem 53.2.6; Lemma 33.25.4; Definition 53.8.1, tags 0BY1, 056T, 0BY6](https://stacks.math.columbia.edu/tag/0BY1).

Specialized to Q and combined with Stacks: "proper" in place of "projective" (a proper smooth curve over a field is projective, 0BY1), and genus as dim H¹(O) (0BY6), with H¹ as in the table of objects.

**12. `Z2Z4Rank6.NeronRigidCountingTheorem`.** Let K be a finite extension of Q(t) that is isomorphic over Q to the function field of an elliptic curve E over Q of rank r > 0. For each H the normalized rational places of K (ι(t) = c + T, as in 10) with max(|num c|, den c) ≤ H form a finite set, and their number N(H) satisfies log N(H)/log log H → r/2 as H → ∞.

Source: [André Néron, Problèmes arithmétique et géométriques rattachés à la notion de rang d'une courbe algébrique dans un corps, Bull. Soc. Math. France 80 (1952), 101–166, Chapter III, Theorem 4, Lemma 20, Corollary 2, 151–153](https://www.numdam.org/article/BSMF_1952__80__101_0.pdf); [The Stacks Project Authors, The Stacks Project, Theorem 53.2.6 and Lemma 53.2.8, online tags 0BY1 / section 0BXX](https://stacks.math.columbia.edu/tag/0BXX); [The Stacks Project Authors, The Stacks Project, Lemma 10.160.10(2), online tag 0323](https://stacks.math.columbia.edu/tag/0323).

Not a verbatim theorem: Néron counts rational points of E; t is a nonconstant function on E, the places correspond to the rational points where t is finite and unramified (Stacks), and the finitely many excluded points do not change the exponent. Only the exponent is asserted, not an asymptotic constant.

### Minimal models and conductors (13–16)

**13. `Common.Elliptic.GeometricConductor.EllipticMinimalModelsTheorem`.** For every prime p and elliptic Weierstrass equation W over Q_p, the projective curve of W has a regular proper flat model over Z_p, with a given isomorphism of its generic fiber to the curve, that is minimal: every morphism from it to another regular proper model of the same curve is an isomorphism.

Source: [Brian Conrad, Minimal models for elliptic curves (21 November 2015), Definitions 3.1, 3.8; Theorem 3.10 and Remark 3.11, 6, 8](https://math.stanford.edu/~conrad/papers/minimalmodel.pdf). See also Q. Liu, Algebraic Geometry and Arithmetic Curves (2002), Theorem 9.3.21.

Existence only, for elliptic curves over Q_p; the source gives existence and uniqueness for curves of positive genus over any discrete valuation ring. Minimality is Conrad's Definition 3.8.

**14. `Common.Elliptic.MulhollandModelTheorems.Theorem21Components`.** Let y² = x³ + ax² + bx with a, b ∈ Z, nonzero discriminant and a odd, and let (v₂(b), a mod 4, m) be (2, 1, 1), (3, 3, 2) or (4, 3, 4). Then the special fiber of every minimal regular proper model over Z₂ has m + 5 geometric irreducible components.

Source: [John T. Mulholland, Elliptic curves with rational 2-torsion and related ternary Diophantine equations, UBC PhD thesis (2006), Theorem 2.1 and Table 2.1; Theorems 2.3–2.4 and Tables 2.3–2.4, 12–16, selected proofs 18–20](https://www.sfu.ca/~jtmulhol/papers/Mulholland-phd-thesis.pdf); John Tate, Algorithm for determining the type of a singular fiber in an elliptic pencil, Modular Functions of One Variable IV, LNM 476 (1975), 33–52, §0 summary; §7 algorithm, 34–35, 47.

These are rows of Mulholland's Table 2.1 (types I₁*, I₂*, I₄*); only their component counts 6, 7, 9 are used. Theorem 2.1's premise (not both v₂(a) ≥ 2 and v₂(b) ≥ 4) holds since a is odd. The count is geometric, as in Tate (p. 47).

**15. `Common.Elliptic.MulhollandModelTheorems.Theorems23And24SemistableComponents`.** For every odd prime p and coprime integers a, b with y² = x³ + ax² + bx of nonzero discriminant Δ, the special fiber of every minimal regular proper model over Z_p has 1 geometric irreducible component if p ∤ Δ and v_p(Δ) if p | Δ.

Source: [John T. Mulholland, Elliptic curves with rational 2-torsion and related ternary Diophantine equations, UBC PhD thesis (2006), Theorem 2.1 and Table 2.1; Theorems 2.3–2.4 and Tables 2.3–2.4, 12–16, selected proofs 18–20](https://www.sfu.ca/~jtmulhol/papers/Mulholland-phd-thesis.pdf); John Tate, Algorithm for determining the type of a singular fiber in an elliptic pencil, Modular Functions of One Variable IV, LNM 476 (1975), 33–52, §0 summary; §7 algorithm, 34–35, 47.

Coprimality is stronger than the source's premise (not both v_p(a) ≥ 2 and v_p(b) ≥ 4); under it the tables give only types I₀ and I_n, and only their component counts are used. p = 3 is Theorem 2.3, p ≥ 5 Theorem 2.4.

**16. `Common.Elliptic.GeometricConductor.CremonaTateSteps4And19to21`.** Let W be an integral Weierstrass equation with nonzero discriminant Δ, minimal at the prime p, with p ∤ Δ or p ∤ c₄. Then the special fiber of every minimal regular proper model over Z_p has 1 geometric irreducible component if p ∤ Δ and v_p(Δ) if p | Δ.

Source: [John E. Cremona, Algorithms for Modular Elliptic Curves, second edition (1997), Chapter 3, §3.2; Tate algorithm Steps 4 and 19–21, 65–67](https://johncremona.github.io/book/fulltext/chapter3.pdf); John Tate, Algorithm for determining the type of a singular fiber in an elliptic pencil, Modular Functions of One Variable IV, LNM 476 (1975), 33–52, §0 summary; §7 algorithm, 34–35, 47.

Numbered steps of Tate's algorithm, not a numbered theorem: Step 4 (good reduction) and Steps 19–21 (multiplicative reduction, including p = 2, 3 when c₄ is a unit), with n_p = ord_p(Δ) stated on p. 65; Tate counts geometric components (p. 47).

### Curves, genus and Jacobians (17–26)

In 20–22, a curve of genus one over Q means: proper, smooth of relative dimension 1 and geometrically integral over Q, of dimension 1, with Q → H⁰(O) bijective and H¹(O) of dimension 1 (`RationalCurveGenus.IsSmoothProperGenusOne`); H¹ is as in the table of objects.

**17. `Z2Z4Rank6.AffineCoverStructureSheafCohomologyTheorem`.** Let X be a scheme over Q covered by two affine opens U and V with U ∩ V affine. Then the cokernel of O(U) × O(V) → O(U ∩ V), (f, g) ↦ f − g (restricted to U ∩ V), is isomorphic as a Q-vector space to H¹(X, O_X).

Source: [The Stacks Project Authors, The Stacks Project, Lemma 30.2.6](https://stacks.math.columbia.edu/tag/01XD); [The Stacks Project Authors, The Stacks Project, Lemma 20.8.2](https://stacks.math.columbia.edu/tag/01EB); [The Stacks Project Authors, The Stacks Project, Lemma 30.2.2](https://stacks.math.columbia.edu/tag/01XB); [The Stacks Project Authors, The Stacks Project, Lemma 20.5.1](https://stacks.math.columbia.edu/tag/0B3A); [The Stacks Project Authors, The Stacks Project, Lemma 21.12.4](https://stacks.math.columbia.edu/tag/03FD).

Combined: Mayer–Vietoris with vanishing of cohomology on affines, and the identification of H¹ (Ext¹, as in the table of objects) with sheaf cohomology; these standard translations, including Q-linearity, are part of the hypothesis.

**18. `Z2Z4Rank6.SmoothProperGlobalConstantsGeometricIntegralityTheorem`.** A scheme X, proper and smooth over Q with Q → Γ(X, O_X) bijective, is geometrically integral over Q.

Source: [The Stacks Project Authors, The Stacks Project, Lemma 33.25.4](https://stacks.math.columbia.edu/tag/056T); [The Stacks Project Authors, The Stacks Project, Lemma 33.10.7](https://stacks.math.columbia.edu/tag/0FD3).

Combined: smooth implies geometrically normal (056T), and a proper geometrically normal scheme with Γ(X, O_X) = Q is geometrically integral (0FD3).

**19. `Z2Z4Rank6.SmoothProperCurveFunctionFieldIsomorphismTheorem`.** Two integral schemes of dimension 1, proper and smooth over Q, whose function fields are isomorphic, are isomorphic over Q.

Source: [The Stacks Project Authors, The Stacks Project, Theorem 53.2.6, categories (1), (6)](https://stacks.math.columbia.edu/tag/0BY1); [The Stacks Project Authors, The Stacks Project, Lemma 33.25.4](https://stacks.math.columbia.edu/tag/056T).

A consequence of the equivalence between normal proper curves and their function fields (0BY1), smooth implying normal (056T). The premise is a ring isomorphism of function fields; it is automatically Q-linear (proved in Lean).

**20. `GenusOneModelTheorem.CFSTheorem28iiDegreeOne`.** For every Weierstrass equation W over Q, its projective cubic is a curve of genus one (as above) if and only if Δ(W) ≠ 0.

Source: [J. E. Cremona, T. A. Fisher, M. Stoll, Minimisation and reduction of 2-, 3- and 4-coverings of elliptic curves, Algebra & Number Theory 4 (2010), 763–820, Theorem 2.8(ii), p. 6; Definitions 2.1/2.2/2.4, pp. 4–6](https://arxiv.org/pdf/0908.1741v1).

Specialized to Q and to Weierstrass cubics (models of degree 1 in the source).

**21. `GenusOneModelTheorem.CFSTheorem28iiDegreeTwo`.** For every binary quartic g(x, z) over Q, the curve y² = g(x, z) in weighted projective space with weights (1, 1, 2) is a curve of genus one if and only if the discriminant of g is nonzero.

Source: [J. E. Cremona, T. A. Fisher, M. Stoll, Minimisation and reduction of 2-, 3- and 4-coverings of elliptic curves, Algebra & Number Theory 4 (2010), 763–820, Theorem 2.8(ii), p. 6; Definitions 2.1/2.2/2.4, pp. 4–6](https://arxiv.org/pdf/0908.1741v1).

Specialized to Q and to y² = g (the source allows y² + h(x, z)y = g(x, z)).

**22. `QuadricIntersectionModel.CFSTheorem28ii`.** For every pair of quadrics over Q in four variables, their intersection in P³ is a curve of genus one if and only if its discriminant (from the invariants of det(xA + zB), with A and B the matrices of second partial derivatives of the quadrics) is nonzero.

Source: [J. E. Cremona, T. A. Fisher, M. Stoll, Minimisation and reduction of 2-, 3- and 4-coverings of elliptic curves, Algebra & Number Theory 4 (2010), 763–820, Theorem 2.8(ii), p. 6; Definitions 2.1/2.2/2.4, pp. 4–6](https://arxiv.org/pdf/0908.1741v1).

**23. `BinaryQuarticModel.CFSBinaryQuarticJacobianTheorem`.** For every binary quartic g over Q with nonzero discriminant, the projective cubic y² = x³ − 27c₄x − 54c₆, with c₄ = 16I(g) and c₆ = 32J(g) as in CFS Definition 2.2, is the Jacobian of y² = g(x, z) in the sense of `Jacobian.IsJacobian` (table of objects).

Source: [J. E. Cremona, T. A. Fisher, M. Stoll, Minimisation and reduction of 2-, 3- and 4-coverings of elliptic curves, Algebra & Number Theory 4 (2010), 763–820, Theorem 2.8(iii), p. 6; Definitions 2.2/2.4, pp. 4–6](https://arxiv.org/pdf/0908.1741v1); [J. S. Milne, Jacobian Varieties, Arithmetic Geometry (1986), Ch. VII, 167–212; corrected reprint 12 June 2021, Proposition 6.4/Remark 6.5, author pp. 20–21](https://www.jmilne.org/math/xnotes/JVs.pdf).

Combined: CFS give the equation of the Jacobian, and Milne's Albanese property (Proposition 6.4, Remark 6.5) characterizes the Jacobian. The clause of CFS 2.8(iii) on generators of the ring of invariants is not used.

**24. `QuadricIntersectionModel.CFSTheorem28iii`.** For every pair of quadrics over Q whose intersection in P³ has nonzero discriminant, the projective cubic y² = x³ − 27c₄x − 54c₆, with c₄, c₆ the invariants of CFS Definition 2.4, is the Jacobian of the intersection, in the same sense.

Source: [J. E. Cremona, T. A. Fisher, M. Stoll, Minimisation and reduction of 2-, 3- and 4-coverings of elliptic curves, Algebra & Number Theory 4 (2010), 763–820, Theorem 2.8(iii), p. 6; Definitions 2.2/2.4, pp. 4–6](https://arxiv.org/pdf/0908.1741v1); [J. S. Milne, Jacobian Varieties, Arithmetic Geometry (1986), Ch. VII, 167–212; corrected reprint 12 June 2021, Proposition 6.4/Remark 6.5, author pp. 20–21](https://www.jmilne.org/math/xnotes/JVs.pdf).

As for 23.

**25. `WeierstrassScheme.MilneRegularGroupLaw`.** For every elliptic Weierstrass equation W over Q, the projective cubic of W is, as a scheme over Q, isomorphic to a commutative group scheme over Q whose group law on rational points is the usual addition of W(Q).

Source: [J. S. Milne, Elliptic Curves, second edition, World Scientific (2021), Proposition I.4.10/Remark I.4.11(b, c), pp. 32–33; II.2 pp. 49–53](https://www.jmilne.org/math/Books/EC2.pdf).

Combined: Milne shows that the chord-and-tangent law is given by regular maps; its form as a group object in schemes over Q is the standard consequence.

**26. `AlgebraicGeometry.Jacobian.MilneCorollary22`.** Every morphism over Q between abelian varieties over Q is a homomorphism of group schemes followed by a translation by a rational point.

Source: [J. S. Milne, Abelian Varieties, Arithmetic Geometry (1986), Ch. V, 103–150; corrected reprint 2 January 2022, Corollary 2.2, author p. 3](https://www.jmilne.org/math/xnotes/AVs.pdf).

### Elliptic surfaces (27–55)

A model of an elliptic curve W over k(t) over P¹_k is a `SurfaceModel.RegularModel` (table of objects); projective over k means a closed immersion over k into some Pⁿ_k. Hypotheses 34–54 are used to pass between the surface over Q and its base change to C.

**27. `Common.Elliptic.EllipticSurfaceSections.LeterrierRemark139Models`.** For a perfect field k, every elliptic Weierstrass curve W over k(t) has a relatively minimal model over P¹_k that is projective over k and whose projection onto P¹_k is surjective.

Source: [Gauthier Leterrier, Some Mordell-Weil lattices and applications to sphere packings, EPFL thesis 10417 (2024), Remark 1.3.9, first bullet and following flatness paragraph, printed p. 36/PDF p. 50](https://infoscience.epfl.ch/record/307330/files/EPFL_TH10417.pdf). See also Q. Liu, Algebraic Geometry and Arithmetic Curves (2002), Theorem 9.3.21.

Specialized to the base curve P¹; existence only (uniqueness is hypothesis 55).

**28. `Common.Elliptic.EllipticSurfaceSections.LeterrierRemark139Sections`.** For a perfect field k, an elliptic W over k(t), and a relatively minimal model of W over P¹_k that is projective over k with surjective projection, restriction to the generic fiber is a bijection from the sections of the model over P¹_k to the k(t)-rational points of the projective cubic of W.

Source: [Gauthier Leterrier, Some Mordell-Weil lattices and applications to sphere packings, EPFL thesis 10417 (2024), Remark 1.3.9, second bullet, printed p. 36/PDF p. 50](https://infoscience.epfl.ch/record/307330/files/EPFL_TH10417.pdf).

**29. `Common.Elliptic.ComplexEllipticSurfaceTheorems.MirandaTableIV31`.** Let W have coefficients in C[t] and be elliptic over C(t), and let M be a relatively minimal model of it over P¹_C with a section. At t ∈ C with Δ(t) ≠ 0 the fiber of M is a smooth plane cubic. At t with Δ ≠ 0, c₄(t) ≠ 0 and Δ of order n > 0 at t, the fiber is of type I_n (`NeronPolygon.IsTypeI`); this also holds at t = ∞, read on the equation in the coordinate s = 1/t (with a_i multiplied by s^{id}).

Source: [Rick Miranda, The Basic Theory of Elliptic Surfaces, ETS Editrice, Pisa (1989), Table IV.3.1 printed p. 41/PDF p. 45; minimal-form discussion III.3 printed p. 31](https://www.math.colostate.edu/~miranda/BTES-Miranda.pdf).

Two rows (good and multiplicative) of Miranda's table, which is stated for y² = x³ + A(t)x + B(t); over C its conditions translate into those on c₄ and Δ.

**30. `Common.Elliptic.ComplexEllipticSurfaceTheorems.SchuttShiodaSection67FiberEuler`.** For a relatively minimal model with a section over P¹_C of an elliptic curve over C(t), every fiber of type I_n (at a finite point or at ∞) has finite-dimensional rational singular homology, zero above degree 2, and Euler number equal to its number of irreducible components, n.

Source: [Matthias Schütt, Tetsuji Shioda, Elliptic Surfaces, Advanced Studies in Pure Mathematics 60 (2010), 51–160; arXiv:0907.0298v3, Section 6.7, unnumbered fiber-Euler display, arXiv p. 27](https://arxiv.org/pdf/0907.0298v3).

**31. `Common.Elliptic.SurfaceEulerCharacteristic.SchuttShiodaTheorem610`.** Let M be a relatively minimal model with a section over P¹_C, projective over C, of an elliptic curve over C(t), with at least one fiber of type I_n for some n > 0. For every finite set S of points of P¹_C outside which all fibers are smooth cubics, the rational singular homology of M(C) is finite-dimensional and zero above degree 4, and e(M) = Σ_{t∈S} e(F_t).

Source: [Matthias Schütt, Tetsuji Shioda, Elliptic Surfaces, Advanced Studies in Pure Mathematics 60 (2010), 51–160; arXiv:0907.0298v3, Theorem 6.10 and surrounding singular-fiber premise, arXiv p. 27](https://arxiv.org/pdf/0907.0298v3).

A fiber of type I_n is a stronger premise than the source's singular fiber; in characteristic 0 the source's wild terms vanish.

**32. `Common.Elliptic.SurfaceFundamentalLineBundle.MirandaIII44`.** Let M be a relatively minimal model over P¹_C, projective over C, of an elliptic curve over C(t), and s a section. If the rational homology of M(C) is finite-dimensional and zero above degree 4, then e(M) = 12 deg L, where L is the conormal sheaf of s and deg L = χ(L) − χ(O).

Source: [Rick Miranda, The Basic Theory of Elliptic Surfaces, ETS Editrice, Pisa (1989), formula III.4.4 printed p. 34/PDF p. 38; Definition II.4.1 and II.3.6 printed p. 23/PDF p. 27](https://www.math.colostate.edu/~miranda/BTES-Miranda.pdf).

Miranda's fundamental line bundle (the dual of the normal bundle of the section) is the conormal sheaf of s.

**33. `Common.Elliptic.SurfaceFundamentalLineBundle.MirandaLemmaIII46a`.** Let M be a relatively minimal model over P¹_C, projective over C, of an elliptic curve over C(t), with a section whose conormal sheaf has degree 2. Then M is a K3 surface (`IsK3`, table of objects).

Source: [Rick Miranda, The Basic Theory of Elliptic Surfaces, ETS Editrice, Pisa (1989), Lemma III.4.6(a), degree 2 clause, printed p. 35/PDF p. 39](https://www.math.colostate.edu/~miranda/BTES-Miranda.pdf); [Matthias Schütt, Tetsuji Shioda, Elliptic Surfaces, Advanced Studies in Pure Mathematics 60 (2010), 51–160; arXiv:0907.0298v3, Definition 12.1, arXiv p. 59](https://arxiv.org/pdf/0907.0298v3).

Only the K3 case of the lemma.

**34. `Common.AlgebraicGeometry.ClosedSubschemeDescent.EGAIV2Proposition4813`.** For a field extension K/k and a k-scheme X that is quasi-compact and locally of finite type, every closed subscheme of X_K is the base change of a closed subscheme of X_L for some finitely generated intermediate field k ⊆ L ⊆ K.

Source: [A. Grothendieck, with J. Dieudonné, Éléments de géométrie algébrique IV, seconde partie, Publications Mathématiques IHÉS 24 (1965), 5–231, Proposition 4.8.13, closed-subscheme case using Corollary 4.8.11, printed p. 83/PDF p. 80](https://www.numdam.org/item/10.1007/BF02684322.pdf).

The source also gives a smallest such field; only existence is used.

**35. `Common.AlgebraicGeometry.NegativeCurveDescent.EGAIV2Corollary414`.** For a field extension K/k and a k-scheme X locally of finite type, dim X_K = dim X.

Source: [A. Grothendieck, with J. Dieudonné, Éléments de géométrie algébrique IV, seconde partie, Publications Mathématiques IHÉS 24 (1965), 5–231, Corollary 4.1.4, printed p. 54/PDF p. 51](https://www.numdam.org/item/10.1007/BF02684322.pdf).

The same proposition is also stated, with identical content, as `Common.Elliptic.SurfaceBaseChange.EGAIV2Corollary414` and used in the proofs.

**36. `Common.AlgebraicGeometry.ClosedSubschemeDescent.EllenbergLemma41`.** Let K/k be an extension of algebraically closed fields of finite transcendence degree and X a smooth projective integral surface over k. Every integral closed curve D on X_K with D² < 0 is the base change of an integral closed curve on X.

Source: [Jordan S. Ellenberg, Endomorphism algebras of Jacobians, Advances in Mathematics 162 (2001), 243–271, Lemma 4.1 author p. 14, proof p. 15](https://people.math.wisc.edu/~ellenberg/EndJacAjour.pdf).

D² < 0 is written as: the conormal sheaf of D and O_D have finite-dimensional H⁰ and H¹, and the conormal sheaf has positive degree (equal to −D², an integral curve on a smooth surface being a Cartier divisor).

**37. `Common.AlgebraicGeometry.ConormalCohomologyComparison.Stacks01R1ConormalQuasicoherent`.** For every closed immersion i: C → X of schemes, the conormal sheaf of i is quasi-coherent.

Source: [The Stacks Project Authors, The Stacks Project, Definition 29.32.1, construction and Lemma 29.32.2](https://stacks.math.columbia.edu/tag/01R1).

The conormal sheaf is defined as i*(ker(O_X → i_*O_C)); Stacks Lemma 29.32.2 identifies it with I/I².

**38. `Common.AlgebraicGeometry.ConormalCohomologyComparison.Stacks0473Conormal`.** For a cartesian square of schemes in which C → X and D → Y are closed immersions and Y → X is flat, the conormal sheaf of D → Y is isomorphic to the pullback of that of C → X.

Source: [The Stacks Project Authors, The Stacks Project, Lemma 29.32.4](https://stacks.math.columbia.edu/tag/0473).

Only the flat case (an isomorphism); the source also gives a surjection in general.

**39. `Common.AlgebraicGeometry.ConormalCohomologyComparison.Stacks02KHModules`.** For a field extension K/k, a quasi-compact quasi-separated k-scheme X and a quasi-coherent O_X-module F, K ⊗_k Hⁱ(X, F) ≅ Hⁱ(X_K, F_K) as K-vector spaces, for all i.

Source: [The Stacks Project Authors, The Stacks Project, Lemma 30.5.2(2)](https://stacks.math.columbia.edu/tag/02KH); [The Stacks Project Authors, The Stacks Project, Lemma 21.12.4](https://stacks.math.columbia.edu/tag/03FD); [The Stacks Project Authors, The Stacks Project, Section 20.44](https://stacks.math.columbia.edu/tag/0B6A).

Hⁱ is Ext from the constant sheaf k in sheaves of k-vector spaces; its identification with sheaf cohomology in all degrees (Section 20.44) is part of the hypothesis.

**40. `Common.AlgebraicGeometry.K3BaseChange.Stacks02KHCartesianStructureSheaf`.** For a field extension K/k and a proper k-scheme X, K ⊗_k Hⁱ(X, O_X) ≅ Hⁱ(X_K, O) for all i.

Source: [The Stacks Project Authors, The Stacks Project, Lemma 30.5.2(2)](https://stacks.math.columbia.edu/tag/02KH); [The Stacks Project Authors, The Stacks Project, Lemma 21.12.4](https://stacks.math.columbia.edu/tag/03FD); [The Stacks Project Authors, The Stacks Project, Section 20.44](https://stacks.math.columbia.edu/tag/0B6A).

The case F = O_X of the source, under the stronger premise "proper"; cohomology as in 39.

**41. `Common.Elliptic.SurfaceBaseChange.Stacks056SSmoothRegular`.** A scheme smooth over a field is regular.

Source: [The Stacks Project Authors, The Stacks Project, Lemma 33.25.3](https://stacks.math.columbia.edu/tag/056S).

**42. `Common.Elliptic.SurfaceDescentSources.EGAIIProposition555iii`.** For a field extension K/k, the base change to K of a projective k-scheme is projective over K.

Source: [A. Grothendieck, with J. Dieudonné, Éléments de géométrie algébrique II, Publications Mathématiques IHÉS 8 (1961), 5–222, Proposition 5.5.5(iii), printed p. 105/PDF p. 102](https://www.numdam.org/item/PMIHES_1961__8__5_0.pdf).

**43. `Common.Elliptic.SurfaceDescentSources.OverkampSmeetsProposition26`.** Let k have characteristic 0 and K be an algebraic closure of k. If a relatively minimal model of an elliptic W over k(t), projective over k and with a section, has base change to K that is regular of dimension 2, then that base change is relatively minimal.

Source: [Otto Overkamp, Arne Smeets, On logarithmic reduction of cohomologically tame elliptic surfaces, arXiv:2212.01070v1 (2022), Propositions 2.5 and 2.6, p. 6; Definition 1.1, pp. 1–2; Definition 2.2, p. 4](https://arxiv.org/pdf/2212.01070v1).

Only the algebraic-closure case (Proposition 2.5; 2.6 adds the separable closure), in characteristic 0 where the source needs characteristic ≠ 2, 3.

**44. `Common.AlgebraicGeometry.CurveLineBundle.EGAIV2Proposition252iv`.** Let p: Y → X be flat, surjective and quasi-compact, and F a quasi-coherent O_X-module. If p*F is invertible, so is F.

Source: [A. Grothendieck, with J. Dieudonné, Éléments de géométrie algébrique IV, seconde partie, Publications Mathématiques IHÉS 24 (1965), 5–231, Proposition 2.5.2(iv), n=1 backward implication, printed p. 22/PDF p. 19](https://www.numdam.org/item/10.1007/BF02684322.pdf).

The case n = 1 of the source; invertible means locally isomorphic to O_X on an open cover.

**45. `Common.AlgebraicGeometry.CurveLineBundle.Stacks0C6U`.** Let C be a proper integral scheme of dimension 1 over a field k with H¹(C, O_C) = 0, and L an invertible O_C-module, with H⁰ and H¹ of L and of O_C finite-dimensional. If deg L = χ(L) − χ(O_C) = 1, then C ≅ P¹_k over k.

Source: [The Stacks Project Authors, The Stacks Project, Proposition 53.10.4, (7)⇒(1)](https://stacks.math.columbia.edu/tag/0C6U); [The Stacks Project Authors, The Stacks Project, Section 53.5, equation 53.5.0.1; Definition 33.44.1](https://stacks.math.columbia.edu/tag/0B5B).

Implication (7) ⇒ (1); the source's H⁰(C, O_C) = k is not assumed, since the source derives it.

**46. `Common.AlgebraicGeometry.CurveLineBundle.Stacks3081`.** If a k-scheme C is isomorphic over k to P¹_k, then H¹(C, O_C) = 0.

Source: [The Stacks Project Authors, The Stacks Project, Lemma 30.8.1, n=1, d=0, q=1](https://stacks.math.columbia.edu/tag/01XS).

**47. `Common.Elliptic.SurfaceModel.LiedtkeTheorem6Vertical`.** Let k be algebraically closed, W elliptic over k(t), M a model of W over P¹_k that is projective over k, and E a vertical curve on M (an integral closed curve of dimension 1 lying over one k-point of P¹_k). Then E is exceptional (some morphism of models M → N that is not an isomorphism maps E to a point and is an isomorphism away from it) if and only if E ≅ P¹_k, its conormal sheaf and O_E have finite-dimensional H⁰ and H¹, and the conormal sheaf has degree 1.

Source: [Christian Liedtke, Semi-stable reduction for curves, Mordell seminar notes, Theorem 6 with Definition 4/Proposition 5, p. 2; Definition 2, p. 1](https://math.stanford.edu/~conrad/mordellsem/Notes/L12.pdf). See also Q. Liu, Algebraic Geometry and Arithmetic Curves (2002), Theorem 9.3.8 (Castelnuovo's criterion).

Castelnuovo's criterion for vertical curves over an algebraically closed field: the source's E² = −[k′ : κ(s)] becomes −1, written as degree 1 of the conormal sheaf.

**48. `Common.Elliptic.SurfaceModel.LiedtkeProposition5Vertical`.** For k algebraically closed, every exceptional vertical curve on a model of an elliptic W over k(t) that is projective over k has invertible conormal sheaf.

Source: [Christian Liedtke, Semi-stable reduction for curves, Mordell seminar notes, Proposition 5/Definition 4, p. 2; Definition 2, p. 1](https://math.stanford.edu/~conrad/mordellsem/Notes/L12.pdf).

Only the invertibility in the source's formula O_E(−1) for the normal sheaf.

**49. `Common.Elliptic.SurfaceModel.LiedtkeCorollary15Vertical`.** For k algebraically closed, a model of an elliptic W over k(t) that is projective over k and has no exceptional vertical curves is relatively minimal.

Source: [Christian Liedtke, Semi-stable reduction for curves, Mordell seminar notes, Definition 8, p. 3; Theorem 14/Corollary 15, p. 4; Definition 2, p. 1](https://math.stanford.edu/~conrad/mordellsem/Notes/L12.pdf). See also Q. Liu, Algebraic Geometry and Arithmetic Curves (2002), Theorem 9.3.21.

Combined: having no exceptional vertical curves is the source's definition of relative minimality (Definition 8), and Corollary 15 gives minimality in the sense used here.

**50. `Common.AlgebraicGeometry.CanonicalCotangentConstruction.StacksLemma29335`.** For a separated scheme X over a field k, with Ω_{X/k} defined as the conormal sheaf of the diagonal, there are isomorphisms Ω_{O(U)/k} ≅ Γ(U, Ω_{X/k}) for all affine opens U, compatible with restriction and with the universal derivations.

Source: [The Stacks Project Authors, The Stacks Project, Lemma 29.33.5, Remark 29.33.6, Lemma 29.33.7](https://stacks.math.columbia.edu/tag/01UM).

Combined: Ω as the conormal sheaf of the diagonal (29.33.7) and its affine description (29.33.5).

**51. `Common.AlgebraicGeometry.CanonicalCotangentConstruction.StacksLemma2672`.** For every scheme X, quasi-coherent O_X-module F and d ≥ 0, the sheafified exterior power ∧ᵈF is quasi-coherent, with Γ(U, ∧ᵈF) ≅ ∧ᵈ_{O(U)} F(U) on every affine open U, compatibly with restriction of wedges.

Source: [The Stacks Project Authors, The Stacks Project, Lemma 26.7.2(2), with Lemma 26.7.1](https://stacks.math.columbia.edu/tag/01I6).

The source's affine statement, assembled over all affine opens.

**52. `Common.AlgebraicGeometry.CanonicalBundleDescent.Stacks0FL5`.** For a field extension K/k, a k-scheme X and every d, the pullback of Ωᵈ_{X/k} to X_K is isomorphic to Ωᵈ_{X_K/K}, where Ωᵈ means any O-module with compatible isomorphisms Γ(U, Ωᵈ) ≅ ∧ᵈ Ω_{O(U)/k} on affine opens U.

Source: [The Stacks Project Authors, The Stacks Project, Lemma 50.2.1](https://stacks.math.columbia.edu/tag/0FL5).

The source needs neither smoothness nor flatness.

**53. `Common.AlgebraicGeometry.CanonicalBundleDescent.Stacks02O3Global`.** For a proper scheme X over a field k, Γ(X, O_X) is finite-dimensional over k.

Source: [The Stacks Project Authors, The Stacks Project, Lemma 30.19.2, F=O_X, i=0](https://stacks.math.columbia.edu/tag/02O3).

**54. `Common.AlgebraicGeometry.CanonicalBundleDescent.Stacks0CC5`.** For a field extension K/k and a quasi-compact quasi-separated k-scheme X with Γ(X, O_X) finite-dimensional over k, an invertible O_X-module whose pullback to X_K is trivial is trivial.

Source: [The Stacks Project Authors, The Stacks Project, Lemma 33.30.3](https://stacks.math.columbia.edu/tag/0CC5).

The injectivity of Pic(X) → Pic(X_K); finite-dimensional Γ(X, O_X) is a stronger premise than the source's.

**55. `Common.AlgebraicGeometry.SurfaceModelAutomorphism.LeterrierRemark139Uniqueness`.** For a perfect field k and an elliptic W over k(t), any two relatively minimal models of W over P¹_k that are projective over k and have surjective projections are isomorphic over P¹_k.

Source: [Gauthier Leterrier, Some Mordell-Weil lattices and applications to sphere packings, EPFL thesis 10417 (2024), Remark 1.3.9 (Elliptic surfaces), first bullet, uniqueness-of-pairs clause, printed p. 36; PDF p. 50](https://infoscience.epfl.ch/record/307330/files/EPFL_TH10417.pdf). See also Q. Liu, Algebraic Geometry and Arithmetic Curves (2002), Theorem 9.3.21.

Specialized from a base curve to P¹. Only the existence of an isomorphism over P¹_k is assumed, not its uniqueness or its compatibility with the generic fibers. The source asks for geometrically irreducible models; these are geometrically integral, a stronger condition.

### Tate–Shafarevich groups (56)

**56. `Common.Elliptic.TateShafarevich.SilvermanSplitTwoDescentExactSequence`.** Let E be an elliptic Weierstrass equation over Q equal to y² = x(x + r₂)(x + r₃), with r₂, r₃ distinct nonzero integers. The square-class pairs whose 2-covering of E is soluble over R and every Q_p form a subgroup S; the map κ of hypothesis 8 (with e₁ = 0) takes values in S and has kernel 2E(Q); and there is a surjective homomorphism S → Ш(E/Q)[2] (table of objects) whose kernel is the image of κ.

Source: [Joseph H. Silverman, The Arithmetic of Elliptic Curves, second edition, GTM 106, Springer 2009, Theorem X.1.1 and its proof, 311–314](https://doi.org/10.1007/978-0-387-09494-6); [Joseph H. Silverman, The Arithmetic of Elliptic Curves, second edition, GTM 106, Springer 2009, Proposition X.1.4 (Complete 2-Descent), 315](https://doi.org/10.1007/978-0-387-09494-6); [Joseph H. Silverman, The Arithmetic of Elliptic Curves, second edition, GTM 106, Springer 2009, Theorem X.3.6, 325–327](https://doi.org/10.1007/978-0-387-09494-6); [Joseph H. Silverman, The Arithmetic of Elliptic Curves, second edition, GTM 106, Springer 2009, X.4 setup, definitions and Remark 4.1.1, 331–332](https://doi.org/10.1007/978-0-387-09494-6); [Joseph H. Silverman, The Arithmetic of Elliptic Curves, second edition, GTM 106, Springer 2009, Theorem X.4.2(a), 333](https://doi.org/10.1007/978-0-387-09494-6); [Joseph H. Silverman, The Arithmetic of Elliptic Curves, second edition, GTM 106, Springer 2009, Appendix B.1/B.2, Example 2.1.2 and Proposition 2.5(c), 416, 418–420](https://doi.org/10.1007/978-0-387-09494-6); [Joseph H. Silverman, The Arithmetic of Elliptic Curves, second edition, GTM 106, Springer 2009, Example X.4.5.1, 334–335](https://doi.org/10.1007/978-0-387-09494-6).

Combined from Silverman: the exact sequence X.4.2(a) for [2] over Q, with the square-class coordinates of X.1.4, the identification X.3.6 and continuous cohomology (Appendix B); Example X.4.5.1 writes out these coverings. Specialized to split curves with integral roots. Cocycles use left actions, the inverse of Silverman's right-action convention.

## Relation to the printed proofs

The proofs follow the paper: Theorem 1.1 by its congruence construction and six-row reduction matrix; the generic rank six by the four quadratic characters, the three rank-one twists, injective specialization and complete two-descent; the second family's six points with the extra twist at W = 4 and its character actions; both cofinite torsion statements by the signed covers and Faltings' theorem. They differ as follows.

- The genera of the first base and of the signed covers are computed from affine charts and structure-sheaf cohomology, not from the paper's pencil or branch count; the curves and genera are the same.
- Specialization is a map on Weierstrass points defined through normalized Laurent places, with poles and good reduction built into the definition; hypotheses 10 and 12 are stated for these places.
- Two-descent upper bounds use explicit square-class coordinates, local obstructions, matrices and reconstruction data; every identity and bound is proved in Lean, with no appeal to outside software.
- The finite-field independence proofs use the point groups themselves; group orders, prime-primary projections, the finite-group decompositions and all matrix entries are proved in Lean.
- Jacobian ranks and torsion are carried over to sections of the abelian variety by the regular group law and the rigidity theorem (hypotheses 25 and 26).
- Lemma 4.1(b) and Theorem 1.2(a): the isomorphism of the projective base with E_C comes from explicit maps and an isomorphism of function fields (hypothesis 19), not from Cremona–Fisher–Stoll Theorem 2.8(iii); that route is also proved, as `FirstBaseJacobianCFS.ec_isJacobian`. For Theorem 8.1(a) the genus and the Jacobian come from Theorem 2.8 for the pair of quadrics (hypotheses 22 and 24).
- The paper gives conductor 9240 with its LMFDB label, states 683760 and 182747931661680, and prints the squarefree conductor of the curve in Theorem 8.1(d); here all four are computed by Ogg's formula, from the minimal models of hypothesis 13 and the component counts of hypotheses 14–16.
- Lemma 3.1(a) is stated for every n at which Y is elliptic; the generic fiber is elliptic by `SurfaceRationalData.curveElliptic`.
- Lemma 3.1(b) follows the printed proof on the complex minimal model, where Miranda's results apply; the rational model, its minimality over C and the descent of the K3 property to Q use hypotheses 27–28 and 34–54.
- Remark 8.2 uses an explicit infinite subset of the printed 3-adic neighborhood that also satisfies the six independence congruences; its infinitude is proved by a recurrence, and the independence by reduction as in Section 6, instead of by Silverman's specialization theorem (hypothesis 10).

The historical survey, the heuristic rank predictions and the search averages are context, not results, and are not formalized.

## Building and checking

You need about 10 GB of RAM and 16 GB of free disk space. Install [elan](https://lean-lang.org/install/); it fetches the Lean version named in `lean-toolchain` (v4.34.0). Then, in this folder:

```sh
lake exe cache get
LEAN_NUM_THREADS=4 lake build
```

The first command downloads Mathlib, pinned in `lake-manifest.json`, with its prebuilt files, about 8 GB on disk. The second compiles this project with four parallel jobs: about 20 to 30 minutes. If memory runs short, use `LEAN_NUM_THREADS=2`.

```sh
lake env lean Audit.lean
```

prints the main statements and the axioms each depends on.

To replay every module through Lean's separate kernel checker after building (about 2 to 3 hours):

```sh
(find Common Z2Z4Rank6 -name '*.lean' -print | while IFS= read -r f; do
  m=${f%.lean}
  m=$(printf '%s' "$m" | tr / .)
  lake env leanchecker "$m" || exit 1
done)
```

The only axioms used are `propext`, `Classical.choice` and `Quot.sound`.

## Layout

| Paper | Main module groups |
|---|---|
| Main theorem; Section 6 | `Main`, `Congruence*`, `Local*`, `Reduction*`, `First*Counting` |
| Sections 2–5 | `FamilyIdentities`, `Sections`, `FunctionField*`, `Twist*`, `Rank*`, `FirstBase*`, `ProjectiveBase*` |
| Elliptic surface in Section 3 | `Surface*`, `EllipticSurface*` |
| Section 7 | `Conic*`, `G*` |
| Section 8 | `Second*` |
| Complete two-descent | `ECFull*`, `*Selmer*`, `*Rank*`, and the class-space and parity helpers |
| Used throughout: schemes, cohomology, curves, Jacobians, models, conductors, surfaces | `Common/AlgebraicGeometry`, `Common/Elliptic` |

`Z2Z4Rank6.lean` imports the result modules, and through them every file in `Common/` and `Z2Z4Rank6/`. `Audit.lean` is the only file with diagnostic commands.

## License

Copyright 2026 Manvir Jaswal. Released under the Apache License 2.0; see [LICENSE](LICENSE). Reused Mathlib construction patterns retain their source credits.
