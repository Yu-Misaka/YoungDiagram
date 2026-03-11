import YoungDiagram.Chromosome
import YoungDiagram.Variety
import YoungDiagram.Mutations
import Mathlib.Tactic

open Chromosome

lemma prime_a_b : (X : Chromosome) → (a b : ℕ) → prime^[a] (prime^[b] X) = prime^[a + b] X := by
  intro X a b
  simp [Function.iterate_add]

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

lemma sig_prime_le_sig_1 : (X : Chromosome) → (signature (prime X)).1 ≤ (signature X).1 := by
  intro X
  simp [signature, prime]
  sorry

lemma sig_prime_le_sig_2 : (X : Chromosome) → (signature (prime X)).2 ≤ (signature X).2 := by
  sorry

lemma sig_prime_le_sig : (X : Chromosome) → (signature (prime X)) ≤ (signature X) := by
  intro X
  exact ⟨sig_prime_le_sig_1 X, sig_prime_le_sig_2 X⟩

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
  simp only [maxRank]
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
    simp [rank_of_geneOfRank]

lemma max_rank_prime_minus1 : (X : Chromosome) → (h : maxRank X = n + 1) →
  maxRank (prime X) = n := by
  intro X h
  simp only [prime]
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
    simp only [Function.iterate_succ_apply]
    exact ge_trans (sig_of_prime_lt_sig X) (ih (prime X))

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
