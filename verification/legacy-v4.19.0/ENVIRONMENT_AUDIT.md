# Lean environment used for this session

## Versions

- Official Lean 4.19.0 Linux distribution, downloaded directly from the Lean release on GitHub.
- Lean commit, reported by the unmodified library: `6caaee842e9495688c1567e78c0e68dbb96942aa`.
- mathlib4 tag `v4.19.0`, commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`.
- Mathlib dependency versions are pinned by the upstream `lake-manifest.json`.

## Host compatibility

The standard Lean command-line driver cannot discover its installation in this host.
Its implementation requests `/proc/<pid>/exe`, for which the host reports `Permission denied`.
The standard CLI calls this before processing arguments, including `--version`.
The official Lean 4.24 and current master sources retain this discovery mechanism.
No access controls or system calls were changed or intercepted.

The session instead uses `embed_lean.c`, a small C host for the **unmodified official
`libleanshared.so`**. It explicitly supplies the installation directory to
`Lean.initSearchPath`, then invokes the library's original `lean_run_frontend` with
trust level 0. It uses the original `lean_write_module` and `lean_ir_emit_c` entry
points to write outputs. This host does not introduce, replace, or modify proof
checking, elaboration, tactics, or the kernel.

Lake remains the official binary. Its documented `LEAN_SYSROOT` and `LAKE_HOME`
configuration variables are set to explicit paths. The local cache downloader's
`Cache.IO` source was adjusted only to read these explicit source paths instead
of calling automatic executable discovery. `Cache.Requests` was adjusted to pass
curl's `--parallel-immediate --parallel-max 100` options. These are the only
tracked modifications in the mathlib checkout, and neither is mathematical
source or imported by the proof modules. No mathematical source in Mathlib was
changed. `TAR_OPTIONS=--no-same-owner` is used because the host cannot assign the
UIDs/GIDs from downloaded archives.

## Sanity checks

- The original library reports version `4.19.0` and its full commit above.
- `example : 1 + 1 = 2 := by rfl` is accepted.
- `#print axioms Nat.add_comm` reports no axioms.
- The deliberately invalid `example : (1 : Nat) = 2 := by rfl` is rejected with
  Lean's expected elaboration error, and the host returns exit code 1.
- An `.olean` and a C file were produced for the accepted source using the
  official library's output functions.
- The targeted Mathlib import closure (2781 modules) was successfully downloaded
  and unpacked from the official cache.
- `ImprovedSidorenko/LegalChoices.lean` and `ImprovedSidorenko/Main.lean` both
  compiled with exit code 0 and no warnings.
- `#print axioms ImprovedSidorenko.main_embedding` and
  `#print axioms ImprovedSidorenko.main_density` both reported exactly
  `[propext, Classical.choice, Quot.sound]`. The polynomial embedding theorem
  has the same dependencies. No `sorryAx` or extra axioms occur in these results.

## Commands

```sh
source /workspace/scratch/47e4ed7445e7/.tooling/env.sh
lake env lean path/to/File.lean
lake build
```

`verification/Environment.lean` independently queries `Lean.versionString` and
`Lean.githash` inside Lean; the result is recorded in `environment.log`. The
command-line compatibility host's printed version is not the sole version check.

The SHA-256 of the official shared library loaded during this session is:

```text
2ab605c74c78f9ba4431a7b5305a4b28a9071d8a826f223eb14fe5530f78e14d  libleanshared.so
```

The normal `lean-toolchain` and Lake dependency files in the delivered project
are sufficient for a standard Lean/Elan installation outside this host; the
explicit-root C host is an environmental accommodation for this session only.
