# Statement correspondence

## Source theorem

Erdős problem 577 asks for the following result:

> If `G` is a graph with `4k` vertices and minimum degree at least `2k`, then
> `G` contains `k` vertex-disjoint four-cycles.

## Formalized scope

`Erdos577.erdos_577_k_one` specializes the source theorem to `k = 1` and uses
the fixed four-element vertex type `Fin 4`.

- `SimpleGraph (Fin 4)` models a finite undirected graph without loops.
- `∀ v, 2 ≤ (G.neighborSet v).ncard` is the minimum-degree hypothesis,
  expressed as the cardinality of each finite neighbor set.
- `ContainsC4 G` provides four pairwise distinct vertices and all four cyclic
  adjacency relations, so it is a nondegenerate four-cycle.

No converse or claim for `k > 1` is made.
