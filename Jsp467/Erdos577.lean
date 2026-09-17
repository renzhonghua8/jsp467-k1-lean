import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Combinatorics.SimpleGraph.Finite

/-!
# Erdős problem 577: the case `k = 1`

Hong Wang proved that every graph on `4 * k` vertices whose minimum degree is
at least `2 * k` contains `k` vertex-disjoint four-cycles. This file proves
the exact first case: every simple graph on four vertices with minimum degree
at least two contains a four-cycle.

References:
* [The Justin Sun Prize, JSP-000467](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0401-0500.md#JSP-000467)
* [Erdős problem 577](https://www.erdosproblems.com/577)
* H. Wang, *Proof of the Erdős-Faudree conjecture on quadrilaterals*,
  Graphs and Combinatorics (2010), 833–877.
-/

open SimpleGraph

namespace Erdos577

/-- Four pairwise distinct vertices occurring cyclically in `G`. -/
def ContainsC4 {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ a b c d : V,
    a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a

/-- On four named vertices, if one is not adjacent to another and has degree
at least two, it is adjacent to both remaining vertices. -/
private lemma adj_both_of_not_adj
    (G : SimpleGraph (Fin 4)) (hdegree : ∀ v, 2 ≤ (G.neighborSet v).ncard)
    (v w x y : Fin 4) (hxy : x ≠ y)
    (hall : ∀ z, z = v ∨ z = w ∨ z = x ∨ z = y)
    (hvw : ¬ G.Adj v w) : G.Adj v x ∧ G.Adj v y := by
  have hsubset : G.neighborSet v ⊆ {x, y} := by
    intro z hz
    have hvz : G.Adj v z := (G.mem_neighborSet v z).mp hz
    rcases hall z with rfl | rfl | rfl | rfl
    · exact (G.irrefl hvz).elim
    · exact (hvw hvz).elim
    · simp
    · simp
  have hcard : ({x, y} : Set (Fin 4)).ncard ≤ (G.neighborSet v).ncard := by
    simpa [Set.ncard_pair hxy] using hdegree v
  have heq : G.neighborSet v = {x, y} :=
    Set.eq_of_subset_of_ncard_le hsubset hcard
  constructor <;> rw [← G.mem_neighborSet, heq] <;> simp

/-- The `k = 1` case of Erdős problem 577, as an explicit four-cycle. -/
theorem erdos_577_k_one (G : SimpleGraph (Fin 4))
    (hdegree : ∀ v, 2 ≤ (G.neighborSet v).ncard) : ContainsC4 G := by
  have hall01 (z : Fin 4) : z = 0 ∨ z = 1 ∨ z = 2 ∨ z = 3 := by omega
  have hall10 (z : Fin 4) : z = 1 ∨ z = 0 ∨ z = 2 ∨ z = 3 := by omega
  have hall23 (z : Fin 4) : z = 2 ∨ z = 3 ∨ z = 0 ∨ z = 1 := by omega
  have hall32 (z : Fin 4) : z = 3 ∨ z = 2 ∨ z = 0 ∨ z = 1 := by omega
  have hall02 (z : Fin 4) : z = 0 ∨ z = 2 ∨ z = 1 ∨ z = 3 := by omega
  have hall20 (z : Fin 4) : z = 2 ∨ z = 0 ∨ z = 1 ∨ z = 3 := by omega
  have hall13 (z : Fin 4) : z = 1 ∨ z = 3 ∨ z = 0 ∨ z = 2 := by omega
  have hall31 (z : Fin 4) : z = 3 ∨ z = 1 ∨ z = 0 ∨ z = 2 := by omega
  by_cases h01 : G.Adj 0 1
  · by_cases h23 : G.Adj 2 3
    · by_cases h02 : G.Adj 0 2
      · by_cases h13 : G.Adj 1 3
        · refine ⟨0, 2, 3, 1, by omega, by omega, by omega, by omega, by omega,
            by omega, h02, h23, h13.symm, h01.symm⟩
        · have h12 := (adj_both_of_not_adj G hdegree 1 3 0 2 (by omega) hall13 h13).2
          have h30 := (adj_both_of_not_adj G hdegree 3 1 0 2 (by omega) hall31
            (fun h31 ↦ h13 h31.symm)).1
          refine ⟨0, 1, 2, 3, by omega, by omega, by omega, by omega, by omega,
            by omega, h01, h12, h23, h30⟩
      · have h03 := (adj_both_of_not_adj G hdegree 0 2 1 3 (by omega) hall02 h02).2
        have h21 := (adj_both_of_not_adj G hdegree 2 0 1 3 (by omega) hall20
          (fun h20 ↦ h02 h20.symm)).1
        refine ⟨0, 3, 2, 1, by omega, by omega, by omega, by omega, by omega,
          by omega, h03, h23.symm, h21, h01.symm⟩
    · have h20 := (adj_both_of_not_adj G hdegree 2 3 0 1 (by omega) hall23 h23).1
      have h21 := (adj_both_of_not_adj G hdegree 2 3 0 1 (by omega) hall23 h23).2
      have h31 := (adj_both_of_not_adj G hdegree 3 2 0 1 (by omega) hall32
        (fun h32 ↦ h23 h32.symm)).2
      refine ⟨0, 2, 1, 3, by omega, by omega, by omega, by omega, by omega,
        by omega, h20.symm, h21, h31.symm, ?_⟩
      exact (adj_both_of_not_adj G hdegree 3 2 0 1 (by omega) hall32
        (fun h32 ↦ h23 h32.symm)).1
  · have h02 := (adj_both_of_not_adj G hdegree 0 1 2 3 (by omega) hall01 h01).1
    have h21 := (adj_both_of_not_adj G hdegree 1 0 2 3 (by omega) hall10
      (fun h10 ↦ h01 h10.symm)).1
    have h13 := (adj_both_of_not_adj G hdegree 1 0 2 3 (by omega) hall10
      (fun h10 ↦ h01 h10.symm)).2
    have h30 := (adj_both_of_not_adj G hdegree 0 1 2 3 (by omega) hall01 h01).2
    refine ⟨0, 2, 1, 3, by omega, by omega, by omega, by omega, by omega,
      by omega, h02, h21.symm, h13, h30.symm⟩

/-- Walk/cycle API form of the same result. -/
theorem erdos_577_k_one_cycle (G : SimpleGraph (Fin 4))
    (hdegree : ∀ v, 2 ≤ (G.neighborSet v).ncard) :
    ∃ (v : Fin 4) (p : G.Walk v v), p.IsCycle ∧ p.length = 4 := by
  rcases erdos_577_k_one G hdegree with
    ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, eab, ebc, ecd, eda⟩
  let p : G.Walk a a :=
    .cons eab (.cons ebc (.cons ecd (.cons eda .nil)))
  refine ⟨a, p, ?_, by simp [p]⟩
  rw [SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length]
  constructor
  · rw [SimpleGraph.Walk.isPath_def]
    simp [p, hab.symm, hac.symm, had.symm, hbc, hbd, hcd]
  · simp [p]

/-- Canonical containment form: `G` contains a copy of `C₄`. -/
theorem erdos_577_k_one_contains_cycleGraph (G : SimpleGraph (Fin 4))
    (hdegree : ∀ v, 2 ≤ (G.neighborSet v).ncard) : cycleGraph 4 ⊑ G := by
  rw [cycleGraph_isContained_iff (by omega)]
  exact erdos_577_k_one_cycle G hdegree

end Erdos577
