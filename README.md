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

## Reproduce

The toolchain and Mathlib revision are pinned by `lean-toolchain` and
`lakefile.toml`.

```sh
lake update
lake build
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

## Scope and prize submission

The work is a scoped open contribution toward
[JSP-000467](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0401-0500.md#JSP-000467).
Because it proves only `k = 1`, it should be assessed as a special-case
formalization rather than as a full closure of the catalog problem.

## License

The original files in this repository are released under the MIT License.
Mathlib is a separate dependency under its own license.

