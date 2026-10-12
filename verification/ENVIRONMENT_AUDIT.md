# Verification environment

Verified on 2026-10-12 with the official Lean 4.35.0-rc2 toolchain, Lean commit
`11acb17ec6b07a8f9e9173e6845197929540936b`, and canonical mathlib commit
`065356127b1dc0016f66b7283ce0ce2c4055aa55`. All nine dependency revisions are
pinned in `lake-manifest.json`.

## Toolchain provenance

Both toolchain archives came from the official
[Lean release](https://github.com/leanprover/lean4/releases/tag/v4.35.0-rc2).
Their SHA-256 hashes were checked against the published release assets:

- `lean-4.35.0-rc2-darwin_aarch64.tar.zst`:
  `e721cf30671d3830fa6120c7b1a4e6b22624650ce1d618c0ca28a4889f5ef324`.
- `lean-4.35.0-rc2-linux_aarch64.tar.zst`:
  `b702aca1e0bceb4d902ae1d269f514dc571195d9f6912590f7a81c983bf45324`.

The toolchains and checker binaries were unmodified. Mathlib build artifacts
were obtained through its canonical public cache for the pinned revision.
No compatibility host, patched kernel or project-provided checker was used.
The earlier Lean 4.19 compatibility-host source is retained only under
`legacy-v4.19.0/environment/`.

## Checks performed

The full source compiled on macOS arm64 and Ubuntu 24.04 aarch64. The Linux
environment was a disposable Colima virtual machine with bubblewrap installed.
The VM alone enabled unprivileged user namespaces for Comparator; no host
security setting was changed. The VM was removed after saving the evidence.

The default-sandbox `lake comparator` rebuilt and exported Challenge and
Solution. It accepted all three named theorems, including their definitions
and permitted-axiom requirements. Lean's default kernel, NanoDa and con-ron
accepted the solution; con-ron reported 18,131 accepted declarations.
The sandbox was not disabled, and pre-exported inputs were not substituted.

The separate axiom audit covered 28 declarations and found only `propext`,
`Classical.choice` and `Quot.sound`. The source scans passed module-header,
line-limit, metadata and proof-placeholder checks. The proof development
contains no `sorry`, custom axiom, `native_decide` or unsafe declaration.
Challenge has exactly three deliberate statement holes, as allowed by Palomar.

Build logs retain nonfatal Mathlib style warnings and the expected Challenge
hole warnings. These are distinct from missing proofs in Solution.

## Evidence and reproduction

`RESULTS.json` records the outcomes. `build-macos.log`, `build-linux.log`,
`axioms.log`, `comparator-linux.log`, `source-check.log` and the two environment
logs contain the actual output. `source-sha256.txt` records the mathematical
sources and build/statement configuration checked here.

To repeat the checks with the pinned toolchain, run `lake exe cache get` and
`bash verify.sh`. On Linux with bubblewrap available, run
`bash verify.sh --comparator`. `scripts/verify-comparator.sh` supplies only the
toolchain's bundled NanoDa and con-ron commands in a temporary checker config;
the submitted `comparator.json` contains no external-checker field.

This is local mechanical verification and an AI-assisted statement audit.
The checked-in GitHub workflow has not been run remotely. No independent human
review, Palomar editorial review or registration is claimed.
