import Mathlib
import YoungDiagram.Mutations

open Finsupp

def Gene.lifting (g : Gene) (k : ℕ) : Gene :=
  ⟨g.rank + k, g.type, Nat.le_add_right_of_le g.rank_pos⟩

namespace Chromosome

noncomputable def lifting (c : Chromosome)
    (k : ℕ) : Chromosome :=
  c.sum (fun g count ↦ single (g.lifting k) count)

abbrev below (c : Chromosome) (k : ℕ) : Chromosome := c.filter (·.rank ≤ k)

abbrev above (c : Chromosome) (k : ℕ) : Chromosome := c.filter (k < ·.rank)

lemma rankDecomposition (c : Chromosome) (k : ℕ) :
    c = c.below k + c.above k := by
  simp [below, above]
  conv =>
    enter [2, 2, 1, a]
    rw [lt_iff_not_ge]
  rw [filter_pos_add_filter_neg]

lemma prime_elim (c : Chromosome) (k : ℕ) :
    prime^[k] c = prime^[k] (c.above k) := by
  nth_rw 1 [rankDecomposition c k]
  simp only [iterate_map_add, add_eq_right]
  induction c using Finsupp.induction with
  | zero =>
    simp [below, filter_zero]
  | single_add g n f hg hn hf =>
    simp [below]
    by_cases hg_rank : g.rank ≤ k
    · rw [filter_single_of_pos, ← mul_one n, ← smul_single', iterate_map_nsmul]
      · refine ⟨?_, hf⟩
        rw [IsAddTorsionFree.nsmul_eq_zero_iff, ← Gene.ofRank_eq_gene,
          prime_ofRank_it, Nat.sub_eq_zero_of_le hg_rank, Gene.ofRank_zero]
        exact Or.inl rfl
      exact hg_rank
    rw [filter_single_of_neg, iterate_map_zero]
    · exact ⟨rfl, hf⟩
    exact hg_rank

end Chromosome

#check IsMutation
