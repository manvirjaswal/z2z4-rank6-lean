# Lean formalization: infinitely many elliptic curves with torsion Z/2Z × Z/4Z and rank at least six

A Lean 4 formalization, with Mathlib, of

> Manvir Jaswal, *Infinitely many elliptic curves with torsion Z/2Z × Z/4Z and rank at least six*, preprint, Zenodo,
> 2026. <https://doi.org/10.5281/zenodo.23437117>

**Main result.** Infinitely many elliptic curves over ℚ have torsion subgroup Z/2Z × Z/4Z and rank at least six, with
infinitely many distinct j-invariants, assuming four published theorems of other authors stated
[below](#the-hypotheses).

**Verification.** Comparator checks Theorem 1.1 with Lean's kernel and the independent kernels NanoDa and con-ron. The
other 18 numbered results of the paper are proved in the same library. The proofs use only Lean's standard axioms
(`propext`, `Classical.choice`, `Quot.sound`), with no `sorry` and no `native_decide`; every computation is checked by
the Lean kernel.

The archived release of this formalization, on Lean v4.34.0, is <https://doi.org/10.5281/zenodo.23682552>. This
repository moves it to Lean v4.35.0-rc2 and the module system, in the layout of the
[Palomar](https://palomar-registry.org/) registry; the statements and their hypotheses are unchanged.

## What it proves

- `Z2Z4Rank6.theorem_1_1` (Theorem 1.1): infinitely many elliptic curves over ℚ have torsion subgroup Z/2Z × Z/4Z
  and rank at least six, with infinitely many distinct j-invariants, hence infinitely many isomorphism classes.

[`Challenge.lean`](Challenge.lean) states this theorem with the definitions it uses, and imports only Mathlib.
[`Solution.lean`](Solution.lean) imports the proof from the library (`Z2Z4Rank6/` and `Common/`).

Among the other numbered results, Theorem 1.2 is about the family y² = x(x + a²)(x + b²), with a and b quartic
polynomials in a parameter m, over a curve C of genus one: the smooth projective model of C is isomorphic over ℚ to an
elliptic curve of conductor 9240 and rank one, the family has rank exactly six over ℚ(C), and at all but finitely many
rational points of C its fibers have torsion exactly Z/2Z × Z/4Z and rank at least six. Theorem 8.1 gives a second
such family, over a curve of genus one whose Jacobian has rank two. [`Audit.lean`](Audit.lean) names Lean
declarations for every numbered result.

## The hypotheses

The theorems take published theorems of other authors as hypotheses. Each is a Lean proposition passed as an
explicit argument (no axiom is added) and stated in general form, about no curve or surface of the paper. Theorem 1.1
takes four:

- `MazurTorsionTheorem`: the torsion subgroup of an elliptic curve over ℚ is one of Mazur's fifteen groups (Mazur,
  Publ. Math. IHÉS 47 (1977), Theorem (8)).
- `OddPrimeTorsionIntegrality`: on an elliptic curve given by a Weierstrass equation with integer coefficients, an
  affine point of finite order has x-coordinate integral at every odd prime (Silverman, *The Arithmetic of Elliptic
  Curves*, 2nd ed., Theorem VII.3.4).
- `GoodReductionHomomorphisms`: reduction modulo a prime of good reduction is a group homomorphism (Silverman,
  Proposition VII.2.1).
- `LocalEllipticTopology`: the points of an elliptic curve over ℚ_p form a compact topological group in which the
  inclusion of the affine solutions is an open embedding (Milne, *Elliptic Curves*, 2nd ed., II §4, proof of
  Theorem 4.1(a)).

The other results use further ones, 56 in all, among them the Mordell–Weil theorem, Faltings' theorem, and results on
minimal models, Jacobians and elliptic surfaces. The README of the archived release states each of them and gives
its source. Nothing from the paper itself is assumed; Lemmas 2.1, 2.2 and 3.2, Proposition 4.2 and Remark 4.3 use
Mathlib alone.

## Build

You need about 10 GB of RAM and 16 GB of free disk space. Install [elan](https://lean-lang.org/install/); it fetches
the Lean version named in `lean-toolchain`. Then, in this folder:

```bash
lake exe cache get   # Mathlib's prebuilt files, about 8 GB on disk
lake build           # this project
```

With four parallel jobs (`LEAN_NUM_THREADS=4 lake build`) the build takes about 20 to 30 minutes. If it runs short of
memory, limit it to two parallel jobs: `LEAN_NUM_THREADS=2 lake build`.

`lake env lean Audit.lean` prints the statements of the numbered results and the axioms their proofs use.

## Run Comparator

On Linux, with [bubblewrap](https://github.com/containers/bubblewrap) installed:

```bash
./scripts/verify-comparator.sh
```

This runs the `lake comparator` of the project's toolchain on [`comparator.json`](comparator.json), as Palomar does.
It checks that `Z2Z4Rank6.theorem_1_1` in `Solution` has exactly the type stated in `Challenge`, that the definitions
this type uses are the same, that the proof uses only the permitted axioms, and that Lean's kernel and the
independent kernels NanoDa and con-ron accept it.

Without bubblewrap, for example on macOS, the script cannot run. The same comparison runs without the sandbox, with
NanoDa and Lean's kernel, as `PATH="$(lean --print-prefix)/bin:$PATH" lake comparator --inadvisably-no-sandbox`.

`scripts/`, `Gemfile` and `Gemfile.lock` come from Palomar's
[template](https://github.com/PalomarRegistry/PalomarTemplate); the CI workflow uses them to check the Lean
sources, [`formalization.yaml`](formalization.yaml) and the licence.

## About

Copyright 2026 Manvir Jaswal. Released under the Apache License 2.0; see [`LICENSE`](LICENSE).
