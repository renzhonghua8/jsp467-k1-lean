# JSP-000467 / Erdős 577 — verified base case

This repository formalizes the exact `k = 1` case of the Erdős–Faudree
quadrilateral conjecture in Lean 4:

> Every simple graph on four vertices with minimum degree at least two
> contains a four-cycle.

The original theorem says that a graph on `4k` vertices with minimum degree
at least `2k` contains `k` pairwise vertex-disjoint four-cycles. Hong Wang
proved the full mathematical theorem in 2010. This repository intentionally
claims only the first parameter case; it does **not** claim a formalization of
Wang's full theorem.

The formal result is exposed in three equivalent reviewer-friendly forms:

- `erdos_577_k_one`: four pairwise distinct vertices with the four cycle edges;
- `erdos_577_k_one_cycle`: a closed `SimpleGraph.Walk` that is a cycle of length four;
- `erdos_577_k_one_contains_cycleGraph`: Mathlib's canonical containment statement
  `cycleGraph 4 ⊑ G`.

## Proof idea

Label the four vertices `0, 1, 2, 3`. If a vertex is not adjacent to one of
the other three, its two-or-more neighbors must be exactly the remaining two.
The proof first splits on edge `01`, then on the candidate opposite edge `23`;
only the `02` and `13` diagonals require further splits. In every missing-edge
branch, the observation above forces the two cycle edges needed to close an
explicit four-cycle. The proof reasons from neighbor-set cardinality; it does
not enumerate all graphs or use a native computation oracle.

## Reproduce

The Lean toolchain and direct Mathlib revision are pinned by `lean-toolchain`
and `lakefile.toml`; every transitive dependency is locked to an exact commit
by the committed `lake-manifest.json`.

```sh
lake build
lake env leanchecker Jsp467
lake env lean Jsp467/Audit.lean
```

The source contains no proof placeholders and declares no custom axioms. The
GitHub Actions workflow rebuilds the project from a clean checkout and rejects
placeholder tokens.

## Files

- `Jsp467/Erdos577.lean` — definitions and proof.
- `Jsp467/Audit.lean` — Lean axiom report for the main theorem.
- `STATEMENT.md` — correspondence between the formal statement and the source.
- `REFERENCES.md` — primary and catalog references.
- `verification/` — recorded local build, kernel replay, toolchain and axiom
  outputs; GitHub Actions separately repeats the checks from a clean runner.

## Scope and prize submission

The work is a scoped candidate contribution toward
[JSP-000467](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0401-0500.md#JSP-000467).
Because it proves only `k = 1`, it should be assessed as a special-case
formalization rather than as a full closure of the catalog problem.
At publication time the official catalog says `Eligible to claim: No`.
Whether this candidate is accepted, how it is classified, and whether any
award or payment applies are decisions reserved to the Prize committees.

Mathematical credit for the full theorem belongs to Hong Wang. This Lean
formalization was developed for the submitting GitHub account with OpenAI
Codex assistance; no mathematical priority is claimed.

## License

The original files in this repository are released under the MIT License.
Mathlib is a separate dependency under its own license.
