# Improved Sidorenko bound in Lean

Formalization of *Improved Sidorenko bound for hypergraph Turán densities* by
Shuyan Chen, Xinmin Hou and Xizhi Liu. The formalization author and responsible
maintainer is Xizhi Liu. The repository uses Apache-2.0; mathematical sources
and dependencies retain their own licenses.

The full project compiled on macOS and Linux with Lean 4.35.0-rc2 on
2026-10-12. The default-sandbox Comparator accepted all three statements;
Lean, NanoDa and con-ron accepted the solution. An audit of 28 declarations
found only the three standard Lean axioms. Current evidence is recorded in
`verification/RESULTS.json` and its accompanying logs. Historical logs under
`verification/legacy-v4.19.0/` concern the previous archive only.

## Submitted mathematical statements

`Challenge.lean` is the independent, Mathlib-only statement module. It defines
finite simple uniform hypergraphs, globally injective embeddings, the exact
paper constant, the extremal number and the classical Turán density. Comparator
compares these three statements with their proved counterparts in `Solution.lean`:

- `ImprovedSidorenko.Registry.embedding`: the finite embedding assertion in the
  manuscript, with a host-size threshold uniform over every host.
- `ImprovedSidorenko.Registry.limit_exists`: the normalized extremal numbers
  converge to the formally defined Turán density.
- `ImprovedSidorenko.Registry.main_theorem`: Theorem 1.1 for that density, with
  the exact real-power constant and no convergence assumption.

The three `sorry` declarations in Challenge are deliberate statement holes.
The proof development and Solution must contain none. Challenge imports no
project proof module, and Solution does not import Challenge.

## Proof development

The proof constructs a legal partial embedding using two potentials, applies
a proved finite Lovász Local Lemma with the actual coordinate-independence
conditions, and excludes all vertex collisions. The constant and the
ordered-tuple/binomial normalization are exact.

`ImprovedSidorenko/Extremal.lean` defines the maximum over actual F-free hosts,
proves attainment when F has at least one edge, and proves convergence by
vertex deletion and double counting. `ImprovedSidorenko/TuranDensity.lean`
applies the embedding bound to the extremal hosts and proves the final theorem.
The infimum used to define the density is proved to be its ordinary limit.

The introductory lower bounds, the optimal-exponent discussion and an
executable embedding-search algorithm are outside the formalization.

## Build and verify

The project pins Lean 4.35.0-rc2 and mathlib commit
`065356127b1dc0016f66b7283ce0ce2c4055aa55`.

```bash
lake exe cache get
bash verify.sh
```

On Linux, with `bubblewrap` installed, also run:

```bash
bash verify.sh --comparator
```

The Comparator script fetches the canonical cache for the project's Mathlib
imports, uses the toolchain's bundled independent kernels and
allows only `propext`, `Quot.sound` and `Classical.choice`. The checked-in CI
runs the same source, metadata, Lean, axiom and Comparator checks on Linux.
Generated `.lake/` state is excluded from the repository.

## Palomar submission

Submissions go to https://submit.palomar-registry.org/ and identify a public
GitHub repository and its full 40-character commit SHA. Use the repository root,
`comparator.json` and `formalization.yaml`. The repository has not been submitted
or registered by this local preparation. Follow the current requirements at
https://palomar-registry.org/how-to-submit before publishing the final commit.

See `README_zh.md` for the Chinese guide. The manuscript snapshot is in `paper/`.
Submission validators and the CI/Comparator scripts are adapted from
PalomarTemplate commit `2891de4c48955af824969a263d31b25e7a9a1406`.
