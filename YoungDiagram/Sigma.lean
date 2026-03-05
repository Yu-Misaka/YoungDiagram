import YoungDiagram.Chromosome
import YoungDiagram.Variety
import YoungDiagram.Mutations
import Mathlib.Tactic

namespace Sigma
open Chromosome

noncomputable def sigma_k (c : Chromosome) (k : ℕ) : ℚ × ℚ :=
  signature (prime^[k] c)

lemma prime_prime : (X : Chromosome) → (k : ℕ) → prime^[k + 1] X = prime^[k] (prime X) := by
  intro X k
  induction k with
  | zero => rfl
  | succ n ih => simp

lemma prime_prime_other : (k : ℕ) → (X : Chromosome) → prime^[k + 1] X = prime (prime^[k] X) := by
  intro k
  induction k with
  | zero =>
    intro X
    rfl
  | succ n ih =>
    intro X
    simp only [Function.iterate_succ, Function.comp_apply]
    rw [← ih (prime X)]
    simp

lemma sigma_nonneg_1 : (X : Chromosome) → (k : ℕ) → (sigma_k X k).1 ≥ 0 := by
  intro X k
  rw [sigma_k]
  have h : (signature (prime^[k] X)) ≥ 0 :=
    signature_nonneg (prime^[k] X)
  exact h.left

lemma sigma_nonneg_2 : (X : Chromosome) → (k : ℕ) → (sigma_k X k).2 ≥ 0 := by
  intro X k
  rw [sigma_k]
  have h : (signature (prime^[k] X)) ≥ 0 :=
    signature_nonneg (prime^[k] X)
  exact h.right

lemma sig_prime_le_sig_1 : (X : Chromosome) → (signature (prime X)).1 ≤ (signature X).1 := by
  sorry

lemma sig_prime_le_sig_2 : (X : Chromosome) → (signature (prime X)).2 ≤ (signature X).2 := by
  sorry

lemma sig_prime_le_sig : (X : Chromosome) → (signature (prime X)) ≤ (signature X) := by
  intro X
  exact ⟨sig_prime_le_sig_1 X, sig_prime_le_sig_2 X⟩

-- If a_k of a chromosome X is 0, then a_k+1 is also 0
lemma if_0_then_next_is_zero_1 : (X : Chromosome) → (k : ℕ) → (sigma_k X k).1 = 0 →
  (sigma_k X (k+1)).1 = 0 := by
    intro X k h
    rw [sigma_k] at h
    rw [sigma_k]
    have hle : (signature (prime^[k] (prime X))).1 ≤ (signature (prime^[k] X)).1 := by
      rw [← prime_prime X k]
      rw [prime_prime_other k X]
      apply sig_prime_le_sig_1 (prime^[k] X)
    have hle1 : (signature (prime^[k] (prime X))).1 ≤ 0 := by
      simpa [h] using hle
    have hle2 : (signature (prime^[k] (prime X))).1 ≥ 0 :=
      sigma_nonneg_1 X (k + 1)
    exact le_antisymm hle1 hle2

-- If b_k of a chromosome X is 0, then b_k+1 is also 0
lemma if_0_then_next_is_zero_2 : (X : Chromosome) → (k : ℕ) → (sigma_k X k).2 = 0 →
  (sigma_k X (k+1)).2 = 0 := by
    intro X k h
    rw [sigma_k] at h
    rw [sigma_k]
    have hle : (signature (prime^[k] (prime X))).2 ≤ (signature (prime^[k] X)).2 := by
      rw [← prime_prime X k]
      rw [prime_prime_other k X]
      apply sig_prime_le_sig_2 (prime^[k] X)
    have hle1 : (signature (prime^[k] (prime X))).2 ≤ 0 := by
      simpa [h] using hle
    have hle2 : (signature (prime^[k] (prime X))).2 ≥ 0 :=
      sigma_nonneg_2 X (k + 1)
    exact le_antisymm hle1 hle2

-- signature (prime^[rank]) of chromosome = 0
-- Maybe move this to chromosome?
lemma sig_rank_0_eq_0_gene : (g : Gene) → (h : g.rank = 0) → g.signature = (0, 0) := by
  intro g h
  have h' : False := by
    have := g.rank_pos
    simp [h] at this
  cases h'

lemma sig_rank_0_eq_0 : (X : Chromosome) → (h : maxRank X = 0) → signature X = 0 := by
  intro X h
  rw [maxRank] at h
  rw [signature]
  simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  have h1 : ∀ g ∈ X.support, g.rank = 0 := by
    intro g h''
    have := Finset.le_sup (s := X.support) (f := fun g => g.rank) h''
    simpa [h] using this
  have h2 : ∀ g ∈ X.support, g.signature = 0 := by
    intro g h''
    have := h1 g h''
    apply sig_rank_0_eq_0_gene g this
  rw [Finsupp.sum]
  refine Finset.sum_eq_zero ?_
  intro g h''
  have := h2 g h''
  rw [this]
  simp

lemma gene_rank_leq_chrom_maxRank : (X : Chromosome) → (g : Gene) → (h : X g ≠ 0) →
  g.rank ≤ maxRank X := by
  intro X g h
  simp only [maxRank]
  apply Finset.le_sup
  simp [h]

lemma gene_leq_max_rank : (X : Chromosome) → ∀ g ∈ X.support, g.rank ≤ maxRank X := by
  intro X g h
  simp [maxRank]
  apply Finset.le_sup
  simp [h]

lemma exist_gene_with_maxRank : (X : Chromosome) → (h : maxRank X = n + 1) →
  ∃ g ∈ X.support, g.rank = n + 1:= by
  intro X h
  have h' : maxRank X > 0 := by
    simp [h]
  have h'' : X.support.Nonempty := by
    rw [maxRank] at h
    classical
    by_contra h_empty
    have h_empty' : X.support = ∅ := by
      simpa [Finset.not_nonempty_empty] using h_empty
    have : X.support.sup (fun g => g.rank) = 0 := by
      simp [h_empty']
    have : n + 1 = 0 := by
      rw [h] at this
      exact this
    exact Nat.succ_ne_zero n this
  obtain ⟨g, hg_mem, hg_max⟩ :=
    Finset.exists_max_image X.support (fun g => g.rank) h''
  use g
  constructor
  · exact hg_mem
  · have : g.rank = X.maxRank := by
      rw [maxRank] at h
      have hyp : g.rank ≤ X.support.sup (fun g => g.rank) :=
        Finset.le_sup hg_mem
      have hyp2 : X.support.sup (fun g => g.rank) ≤ g.rank :=
        Finset.sup_le hg_max
      have : g.rank = X.support.sup (fun g => g.rank) :=
        le_antisymm hyp hyp2
      rw [this]
      rw [maxRank]
    simpa [h] using this

lemma rank_of_geneOfRank {typ : GeneType} : (Gene.ofRank n typ).rank = n := by
  rw [Gene.ofRank]
  induction n with
  | zero => simp
  | succ n ih =>
    simp [rank]

lemma prime_gene_rank : (n : ℕ) → (g : Gene) → (h : g.rank = n + 1) → (primeGene g).rank ≤ n := by
  intro n g h
  induction n with
  | zero =>
    simp at h
    simp [primeGene, h]
  | succ k ih =>
    simp [primeGene, h]
    rw [rank_of_geneOfRank]

lemma max_rank_prime_minus1 : (X : Chromosome) → (h : maxRank X = n + 1) →
  maxRank (prime X) = n := by
  intro X h
  simp [prime]
  have gene_n_1 : ∃ g ∈ X.support, g.rank = n + 1 := by
    apply exist_gene_with_maxRank X h
  obtain ⟨g, hg_mem, hg_rank⟩ := gene_n_1
  have h_1 :(Finsupp.sum X fun g m ↦ m • primeGene g).maxRank ≤ n := by
    apply Finset.sup_le
    intro g' hg'
    have hg'_ne : (prime X) g' ≠ 0 := Finsupp.mem_support_iff.mp hg'
    sorry
  have h_2 :(Finsupp.sum X fun g m ↦ m • primeGene g).maxRank ≥ n := by
    have : (primeGene g).rank = n := by
      sorry
    sorry
  exact le_antisymm h_1 h_2

lemma sig_prime_rank_eq_0 : ∀ k : ℕ, ∀ X : Chromosome, (h : maxRank X = k) →
  signature (prime^[k] X) = (0,0) := by
  intro k
  induction k with
  | zero =>
    intro X h
    simp only [Function.iterate_zero, id_eq]
    apply sig_rank_0_eq_0 X h
  | succ n ih =>
    intro X h
    simp only [Function.iterate_succ, Function.comp_apply]
    apply ih (prime X)
    apply max_rank_prime_minus1 X h

-- Eventaully a_k, b_k becomes 0
lemma cond15_2_0case : (X : Chromosome) →
  ∃ k : ℕ, (sigma_k X k) = 0 := by
  intro X
  let k := maxRank X
  have h : k = maxRank X := by rfl
  have h' : signature (prime^[k] X) = (0, 0) := by
    apply sig_prime_rank_eq_0
    exact h
  refine ⟨ k, ?_ ⟩
  rw [sigma_k]
  exact h'

lemma cond15_2_and_3 : ∀ k : ℕ, ∀ X : Chromosome, (sigma_k X k) ≥ (sigma_k X (k + 1)) := by
  intro k
  induction k with
  | zero =>
    intro X
    rw [sigma_k]
    rw [sigma_k]
    simp only [Function.iterate_zero, id_eq, zero_add, Function.iterate_one, ge_iff_le]
    apply sig_prime_le_sig X
  | succ n ih =>
    intro X
    rw [sigma_k]
    rw [sigma_k]
    simp only [Function.iterate_succ, Function.comp_apply, ge_iff_le]
    apply ih

lemma signature_of_zero : (X : Chromosome) → (X = 0) → signature X = (0, 0) := by
  intro X h
  subst h
  change signature 0 = (0 : ℚ × ℚ)
  simp

lemma sig_of_prime_lt_sig : (X : Chromosome) → signature X ≥ signature (prime X) := by
  intro X
  sorry

lemma sig_of_prime_k_lt_sig : (k : ℕ) → (X: Chromosome)
  → signature X ≥ signature (prime^[k] X) := by
  intro k
  induction k with
  | zero =>
    intro X
    simp
  | succ n ih =>
    intro X
    simp [Function.iterate_succ_apply]
    exact ge_trans (sig_of_prime_lt_sig X) (ih (prime X))

-- 1 is a_i > b_{i+1}
lemma cond15_4_and_5_1 : ∀ k : ℕ, ∀ X : Chromosome,
  (sigma_k X k).1 ≥ (sigma_k X (k + 1)).2 := by
  intro k
  induction k with
  | zero =>
    intro X
    rw [sigma_k]
    rw [sigma_k]
    rw [prime]
    simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, Function.iterate_zero, id_eq, zero_add,
      Function.iterate_one, ge_iff_le]
    rw [signature]
    simp [primeGene, Gene.signature]
    sorry
  | succ n ih => sorry

-- 2 is b_{i} > a_{i+1}
lemma cond15_4_and_5_2 : (X : Chromosome) →
  ∀ k : ℕ, (sigma_k X k).2 ≥ (sigma_k X (k + 1)).1 := by sorry

lemma cond15_6_and_7_1 : ∀ k : ℕ, ∀ X : Chromosome,
  (sigma_k X k).1 - (sigma_k X (k+1)).1 ≥ (sigma_k X (k+1)).2 - (sigma_k X (k+2)).2 := by
  intro k
  induction k with
  | zero =>
    intro X
    sorry

  | succ n ih => sorry


lemma cond15_6_and_7_2 : (X : Chromosome) →
  ∀ k : ℕ, (sigma_k X k).2 - (sigma_k X (k+1)).2 ≥ (sigma_k X (k+1)).1 - (sigma_k X (k+2)).1 :=
  by sorry

lemma cond15_8 : (X Y : Chromosome) → (h : X < Y) →
  ∀ k : ℕ, sigma_k X k ≤ sigma_k Y k := by
  intro X Y h k
  have h' : X ≤ Y := by exact le_of_lt h
  simp only [sigma_k, ge_iff_le]
  exact le_iff_dominates.mp h' k

end Sigma

open Variety Mutation

lemma rank_0 : (X : Chromosome) → (h : X.rank = 0) → X = 0 := by
  intro X h
  simp [Chromosome.rank, Finsupp.sum] at h
  have h' : ∀ a ∈ X.support, 1 ≤ a.rank := by
    intro a h''
    exact a.rank_pos
  apply Finsupp.ext
  intro a
  simp
  simp_all

lemma theorem_6 : (n : ℕ) → (X Y : Chromosome) → (hX : X.rank = n) → (hY : Y.rank = n) →
  (h : X < Y) → ∃ Z ∈ Pi, (IsMutation X Z) ∧ (Z ≤ Y) := by
  intro n X Y hX hY hlt
  induction n generalizing X Y with
  | zero =>
    have x_0 := rank_0 X hX
    have y_0 := rank_0 Y hY
    rw [x_0, y_0] at hlt
    exact False.elim <| (Std.not_gt_of_lt hlt) hlt
  | succ n ih =>
    sorry
