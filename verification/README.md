# Verification record

These files record checks performed on 2026-09-17 with the pinned dependency
graph in `lake-manifest.json`.

- `build.txt`: project build result.
- `leanchecker.txt`: independent kernel replay result from Lean's bundled
  `leanchecker`.
- `axioms.txt`: Lean's dependency report for all three public theorems.
- `toolchain.txt`: exact Lean, Lake and Mathlib revisions.
- `SHA256SUMS`: hashes of the proof source and dependency lockfile.

This is authoring-session evidence, not an official or independent prize
review. The repository workflow repeats the build, kernel replay, axiom audit
and placeholder scan on GitHub-hosted runners.
