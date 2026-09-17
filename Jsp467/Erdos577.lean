import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Tactic

/-!
# Erdős problem 577: the case `k = 1`

Hong Wang proved that every graph on `4 * k` vertices whose minimum degree is
at least `2 * k` contains `k` vertex-disjoint four-cycles.  This file proves
the exact first case: every simple graph on four vertices with minimum degree
at least two contains a four-cycle.
-/

open SimpleGraph

namespace Erdos577

/-- Four pairwise distinct vertices occurring cyclically in `G`. -/
def ContainsC4 (G : SimpleGraph (Fin 4)) : Prop :=
  ∃ a b c d : Fin 4,
    a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a

private lemma adj_pair_of_neighborFinset_subset (G : SimpleGraph (Fin 4))
    {v x y : Fin 4} (hxy : x ≠ y) (hdegree : 2 ≤ G.degree v)
    (hsubset : G.neighborFinset v ⊆ {x, y}) : G.Adj v x ∧ G.Adj v y := by
  have hcard : #({x, y} : Finset (Fin 4)) ≤ #(G.neighborFinset v) := by
    simpa [hxy, SimpleGraph.degree] using hdegree
  have heq : G.neighborFinset v = {x, y} :=
    Finset.eq_of_subset_of_card_le hsubset hcard
  constructor
  · rw [← G.mem_neighborFinset v]
    rw [heq]
    simp
  · rw [← G.mem_neighborFinset v]
    rw [heq]
    simp

/-- The `k = 1` case of Erdős problem 577. -/
theorem erdos_577_k_one (G : SimpleGraph (Fin 4))
    (hdegree : ∀ v, 2 ≤ G.degree v) : ContainsC4 G := by
  classical
  by_cases h01 : G.Adj 0 1
  · by_cases h02 : G.Adj 0 2
    · by_cases h13 : G.Adj 1 3
      · by_cases h23 : G.Adj 2 3
        · refine ⟨0, 1, 3, 2, by decide, by decide, by decide,
            by decide, by decide, by decide, h01, h13, ?_, ?_⟩
          · exact G.symm h23
          · exact G.symm h02
        · have h2 : G.Adj 2 0 ∧ G.Adj 2 1 :=
            adj_pair_of_neighborFinset_subset G (by decide) (hdegree 2) (by
              intro z hz
              have hadj : G.Adj 2 z := (G.mem_neighborFinset 2 z).mp hz
              fin_cases z <;> simp_all [G.adj_comm])
          have h3 : G.Adj 3 0 ∧ G.Adj 3 1 :=
            adj_pair_of_neighborFinset_subset G (by decide) (hdegree 3) (by
              intro z hz
              have hadj : G.Adj 3 z := (G.mem_neighborFinset 3 z).mp hz
              fin_cases z <;> simp_all [G.adj_comm])
          exact ⟨0, 2, 1, 3, by decide, by decide, by decide,
            by decide, by decide, by decide, h02, h2.2, h13, h3.1⟩
      · have h1 : G.Adj 1 0 ∧ G.Adj 1 2 :=
          adj_pair_of_neighborFinset_subset G (by decide) (hdegree 1) (by
            intro z hz
            have hadj : G.Adj 1 z := (G.mem_neighborFinset 1 z).mp hz
            fin_cases z <;> simp_all [G.adj_comm])
        have h3 : G.Adj 3 0 ∧ G.Adj 3 2 :=
          adj_pair_of_neighborFinset_subset G (by decide) (hdegree 3) (by
            intro z hz
            have hadj : G.Adj 3 z := (G.mem_neighborFinset 3 z).mp hz
            fin_cases z <;> simp_all [G.adj_comm])
        exact ⟨0, 1, 2, 3, by decide, by decide, by decide,
          by decide, by decide, by decide, h01, h1.2, G.symm h3.2, h3.1⟩
    · have h0 : G.Adj 0 1 ∧ G.Adj 0 3 :=
        adj_pair_of_neighborFinset_subset G (by decide) (hdegree 0) (by
          intro z hz
          have hadj : G.Adj 0 z := (G.mem_neighborFinset 0 z).mp hz
          fin_cases z <;> simp_all [G.adj_comm])
      have h2 : G.Adj 2 1 ∧ G.Adj 2 3 :=
        adj_pair_of_neighborFinset_subset G (by decide) (hdegree 2) (by
          intro z hz
          have hadj : G.Adj 2 z := (G.mem_neighborFinset 2 z).mp hz
          fin_cases z <;> simp_all [G.adj_comm])
      exact ⟨0, 1, 2, 3, by decide, by decide, by decide,
        by decide, by decide, by decide, h01, G.symm h2.1, h2.2, G.symm h0.2⟩
  · have h0 : G.Adj 0 2 ∧ G.Adj 0 3 :=
      adj_pair_of_neighborFinset_subset G (by decide) (hdegree 0) (by
        intro z hz
        have hadj : G.Adj 0 z := (G.mem_neighborFinset 0 z).mp hz
        fin_cases z <;> simp_all [G.adj_comm])
    have h1 : G.Adj 1 2 ∧ G.Adj 1 3 :=
      adj_pair_of_neighborFinset_subset G (by decide) (hdegree 1) (by
        intro z hz
        have hadj : G.Adj 1 z := (G.mem_neighborFinset 1 z).mp hz
        fin_cases z <;> simp_all [G.adj_comm])
    exact ⟨0, 2, 1, 3, by decide, by decide, by decide,
      by decide, by decide, by decide, h0.1, G.symm h1.1, h1.2, G.symm h0.2⟩

end Erdos577
