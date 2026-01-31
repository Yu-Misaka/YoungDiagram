import YoungDiagram.Chromosome

namespace Chromosome

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
    simp
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
  have h' : g.rank/2 = 0 := by simp [h]
  sorry

lemma sig_rank_0_eq_0 : (X : Chromosome) → (h : max_rank X = 0) → signature X = 0 := by
  intro X h
  rw [max_rank] at h
  rw [signature]
  simp
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

lemma max_rank_prime_minus1 : (X : Chromosome) → (h : max_rank X = n + 1) →
  max_rank (prime X) = n := by
  intro X h
  rw [max_rank]
  rw [max_rank] at h
  rw [prime]
  simp
  rw [Finsupp.sum]
  sorry

lemma sig_prime_rank_eq_0 : ∀ k : ℕ, ∀ X : Chromosome, (h : max_rank X = k) →
  signature (prime^[k] X) = (0,0) := by
  intro k
  induction k with
  | zero =>
    intro X h
    simp
    apply sig_rank_0_eq_0 X h
  | succ n ih =>
    intro X h
    simp
    apply ih (prime X)
    apply max_rank_prime_minus1 X h

-- Eventaully a_k, b_k becomes 0
lemma cond15_2_0case : (X : Chromosome) →
  ∃ k : ℕ, (sigma_k X k) = 0 := by
  intro X
  let k := max_rank X
  have h : k = max_rank X := by rfl
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
    simp
    apply sig_prime_le_sig X
  | succ n ih =>
    intro X
    rw [sigma_k]
    rw [sigma_k]
    simp
    apply ih

-- 1 is a > b
lemma cond15_4_and_5_1 : (X : Chromosome) →
  ∀ k : ℕ, (sigma_k X k).1 ≥ (sigma_k X k + 1).2 := by sorry

-- 2 is b > a
lemma cond15_4_and_5_2 : (X : Chromosome) →
  ∀ k : ℕ, (sigma_k X k).2 ≥ (sigma_k X k + 1).1 := by sorry

lemma cond15_6_and_7_1 : (X : Chromosome) →
  ∀ k : ℕ, (sigma_k X k).1 - (sigma_k X (k+1)).1 ≥ (sigma_k X (k+1)).2 - (sigma_k X (k+2)).2 :=
  by sorry

lemma cond15_6_and_7_2 : (X : Chromosome) →
  ∀ k : ℕ, (sigma_k X k).2 - (sigma_k X (k+1)).2 ≥ (sigma_k X (k+1)).1 - (sigma_k X (k+2)).1 :=
  by sorry

-- lemma existence_of_mut_0 : (X Y : Chromosome) → (h : X < Y)

lemma cond15_8 : (X Y : Chromosome) → (h : X ≤ Y) →
  ∀ k : ℕ, sigma_k X k ≤ sigma_k Y k := by
  intro X Y h k
  sorry
