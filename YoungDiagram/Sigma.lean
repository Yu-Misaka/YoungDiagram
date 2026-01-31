import YoungDiagram.Chromosome

namespace Chromosome

noncomputable def sigma_k (c : Chromosome) (k : ℕ) : ℚ × ℚ :=
  signature (prime^[k] c)

lemma sig_prime_le_sig_1 : (X : Chromosome) → (signature (prime X)).1 ≤ (signature X).1 := by
  intro X
  sorry

lemma sig_prime_le_sig_2 : (X : Chromosome) → (signature (prime X)).2 ≤ (signature X).2 := by
  intro X
  sorry

-- if sigma k is 0, then sigma k + 1 is 0
lemma if_0_then_next_is_zero_1 : (X : Chromosome) → (k : ℕ) → (sigma_k X k).1 = 0 →
  (sigma_k X (k+1)).1 = 0 := by
    intro X k h
    rw [sigma_k] at h
    rw [sigma_k]
    have hle : (signature (prime^[k + 1] X)).1 ≤ (signature (prime^[k] X)).1 := by
      apply sig_prime_le_sig_1
    sorry


lemma if_0_then_next_is_zero_2 : (X : Chromosome) → (k : ℕ) → (sigma_k X k).2 = 0 →
  (sigma_k X (k+1)).2 = 0 := by
    intro X k h
    sorry

lemma cond15_2_0_case : (X : Chromosome) →
  ∃ k : ℕ, sigma_k X k = 0 := by sorry

lemma cond15_2_and_3 : (X : Chromosome) →
  ∀ k : ℕ, (sigma_k X k) ≥ (sigma_k X k + 1) := by sorry

lemma cond15_4_and_5_1 : (X : Chromosome) →
  ∀ k : ℕ, (sigma_k X k).1 ≥ (sigma_k X k + 1).2 := by sorry

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
