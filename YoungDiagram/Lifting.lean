import Mathlib
import YoungDiagram.Mutations

open Finsupp

noncomputable def liftGene (g : Gene) : Chromosome :=
  Gene.ofRank (g.rank + 1) g.type

namespace Chromosome

noncomputable def lift : Chromosome →+ Chromosome where
  toFun c := c.sum (fun g count ↦ count • liftGene g)
  map_zero' := sum_zero_index
  map_add' _ _ := sum_add_index' (fun _ ↦ zero_nsmul _)
    fun _ _ _ ↦ add_nsmul ..

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
  | zero => simp [below, filter_zero]
  | single_add g n f hg hn hf =>
    simp [below]
    by_cases hg_rank : g.rank ≤ k
    · rw [filter_single_of_pos, ← Gene.ofRank_eq_gene', iterate_map_nsmul]
      · refine ⟨?_, hf⟩
        rw [IsAddTorsionFree.nsmul_eq_zero_iff, prime_ofRank_it,
          Nat.sub_eq_zero_of_le hg_rank, Gene.ofRank_zero]
        exact Or.inl rfl
      exact hg_rank
    rw [filter_single_of_neg, iterate_map_zero]
    · exact ⟨rfl, hf⟩
    exact hg_rank

lemma prime_lift_eq_id : prime ∘ lift = id := by
  funext x
  induction x using Finsupp.induction with
  | zero => simp only [Function.comp_apply, map_zero, id_eq]
  | single_add a m f ha hm hf =>
    rw [Function.comp_apply, id_eq] at hf
    rw [Function.comp_apply, map_add, map_add, hf, id_eq, add_left_inj]
    simp [prime, lift, liftGene, primeGene]
    split_ifs with h
    · rw [← Gene.ofRank_eq_gene', h, Gene.ofRank_zero, smul_zero]
    · rfl

end Chromosome


#exit
namespace Lifting

open Chromosome

@[simp] lemma lifting_single {g : Gene} {k : ℕ} :
    lifting k (single g 1) = single (g.lifting k) 1 := by
  simp [lifting]

@[simp] lemma lifting_zero {X : Chromosome} : X.lifting 0 = X := by
  simp [lifting]

lemma lifting_it (X : Chromosome) (k n : ℕ) :
    X.lifting (k + n) = (X.lifting k).lifting n := by
  induction X using Finsupp.induction with
  | zero => simp
  | single_add a m f ha hm hf =>
    simp [hf]
    rw [← mul_one m, ← smul_single', map_nsmul, map_nsmul, map_nsmul,
      nsmul_right_inj hm, lifting_single, lifting_single, lifting_single,
      ← Gene.lifting_it]

lemma prime_lifting {k n : ℕ} (X : Chromosome) (h : ) : prime^[k] (X.lifting n) =

lemma IsMutation_lifting (X Y : Chromosome) (k : ℕ) (h : IsMutation X Y) :
    IsMutation (X.lifting k) (Y.lifting k) := by
  induction k with
  | zero => rwa [lifting_zero, lifting_zero]
  | succ n hn =>
    rw [lifting_it, lifting_it]
    set A := X.lifting n
    set B := Y.lifting n
    refine ⟨?_, ?_, ?_⟩
    · simp
    sorry

variable {X U : Chromosome} {k : ℕ} (h : IsMutation (prime^[k] X) U)

local notation "Z" => X.below k + U.lifting k

lemma Z_isMutation : IsMutation X Z := by
  nth_rw 1 [rankDecomposition X k, add_comm (X.below k),
    add_comm (X.below k), IsMutation_iff_add]


theorem lifting_property {X U : Chromosome} {k : ℕ} (h : IsMutation (prime^[k] X) U) :
  ∃ Z : Chromosome, IsMutation X Z ∧ prime^[k] Z = U ∧
    ∀ i ≤ k, (prime^[i] X).signature = (prime^[i] Z).signature := sorry

end Lifting
