import YoungDiagram.Chromosome
import YoungDiagram.Variety
import YoungDiagram.Mutations
import YoungDiagram.SigmaAux
import Mathlib.Tactic

namespace Sigma
open Chromosome

noncomputable def sigma_k (c : Chromosome) (k : ℕ) : ℚ × ℚ :=
  signature (prime^[k] c)

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

open Variety Mutation

-- Im actually not sure how to prove this case,
-- if n = 1, we don't have any mutations?
lemma t6_rank_1 : (X Y : Pi) → (hX : rank X = 1) → (hY : rank Y = 1) →
  (h : X < Y) → (IsMutation X Y) ∧ (Y ≤ Y) := by
  intro X Y hX hY hlt
  constructor
  · sorry
  · rfl

lemma theorem_6 : (n : ℕ) → (X Y : Pi) → (hX : rank X = n) → (hY : rank Y = n) →
  (h : X < Y) → ∃ Z ∈ Pi, (IsMutation X Z) ∧ (Z ≤ Y) := by
  intro n
  refine Nat.strong_induction_on n ?_
  intro k ih
  cases k with
  | zero =>
    intro X Y hX hY hlt
    have x_0 := rank_0 X hX
    have x0 : X = 0 := by simpa using x_0
    have y_0 := rank_0 Y hY
    have y0 : Y = 0 := by simpa using y_0
    rw [x0, y0] at hlt
    exact False.elim <| (Std.not_gt_of_lt hlt) hlt
  | succ k =>
    cases k with
    | zero => --n = 1
      intro X Y hX hY hlt
      use Y
      constructor
      · exact Y.property
      · exact t6_rank_1 X Y hX hY hlt
    | succ k => sorry

lemma step15_8 : (X Y : Pi) → (h : X < Y) →
  ∀ k : ℕ, sigma_k X k ≤ sigma_k Y k := by
  intro X Y h k
  have h' : X ≤ Y := by exact le_of_lt h
  simp only [sigma_k, ge_iff_le]
  exact le_iff_dominates.mp h' k

lemma sig_sum_eq_rank : (n : ℕ) → (X : Pi) → (hX : rank X = n) →
  (signature X).1 + (signature X).2 = n := by
  intro n
  induction n with
  | zero => sorry
  | succ k ih => sorry

lemma sigma_0_sum_eq_rank : (n : ℕ) → (X : Pi) → (hX : rank X = n) →
  (sigma_k X 0).1 + (sigma_k X 0).2 = n := by
  intro n X hX
  simp [sigma_k, sig_sum_eq_rank]
  simp_all

lemma step15_8_ext : (n : ℕ) → (X Y : Pi) → (hX : rank X = n) → (hY : rank Y = n) → (h : X < Y) →
  (sigma_k X 0) = (sigma_k Y 0) := by
  intro n X Y hX hY hlt
  have h15_8 := step15_8 X Y hlt 0
  have sig_sum_X := sigma_0_sum_eq_rank n X hX
  simp [sigma_k] at sig_sum_X
  have sig_sum_Y := sigma_0_sum_eq_rank n Y hY
  simp [sigma_k] at sig_sum_Y
  have sig_sum_X_eq_Y : (signature X).1 + (signature X).2 = (signature Y).1 + (signature Y).2 := by
    simp_all
  have sig_1 : (signature X).1 ≤ (signature Y).1 := by exact h15_8.1
  have sig_2 : (signature X).2 ≤ (signature Y).2 := by exact h15_8.2
  have eq_1 : (signature X).1 = (signature Y).1 := by linarith
  have eq_2 : (signature X).2 = (signature Y).2 := by linarith
  ext
  · exact eq_1
  · exact eq_2

--this is to prove for the case where X and Y are not disjoint in the case of theorem 6
lemma step15_8_cont : (n : ℕ) → (X Y X₁ Y₁ : Pi) → (hX : rank X = n) → (hY : rank Y = n) → (X < Y) →
  (g : Gene) → (X₁.val + (Finsupp.single g 1) = X.val) ∧
  (Y₁.val + (Finsupp.single g 1) = Y.val) → X₁ < Y₁ := by
  intro n X Y X₁ Y₁ hX hY hlt g rel
  have r1 := rel.left
  have r2 := rel.right
  have hlt' : X₁.val + (Finsupp.single g 1) < Y₁.val + (Finsupp.single g 1) := by
    simp [r1, r2, hlt]
  --have almost : (X₁ : Chromosome) < (Y₁ : Chromosome) := by
    --exact (add_lt_add_iff_right (Finsupp.single g 1)).1 hlt'
  --I don't know why this is complaining
  sorry

--Now when X Y are disjoint, no common gene between the two
lemma disjoint_1 : (k : ℕ) → (X Y : Pi) → (X < Y) →
  Chromosome.prime^[k] X ≤ Chromosome.prime^[k] Y := by
  intro k X Y hlt
  simp only [le_iff_dominates]
  simp only [LT.lt] at hlt
  simp only [Dominates] at hlt
  simp only [prime_a_b]
  intro k'
  exact hlt.1 (k' + k)

--X and Y disjoint -> X' Y' disjoint
lemma disjoint_2_1 : (X Y : Pi) → (X < Y) → (∀ g ∈ X.val.support, g ∉ Y.val.support) →
  ∀ g ∈ (prime X).support, g ∉ (prime Y).support := by
  intro X Y hlt h
  simp_all
  sorry

-- Not really needed, just want to show disjoint is symmetric
lemma disjoint_2_2 : (X Y : Pi) → (X < Y) → (∀ g ∈ Y.val.support, g ∉ X.val.support) →
  ∀ g ∈ X.val.support, g ∉ Y.val.support := by
  intro X Y hlt h
  by_contra
  simp_all only [Finsupp.mem_support_iff, ne_eq, Decidable.not_not, not_forall]
  rcases this with ⟨x, hxX, hxY⟩
  have hX0 : X.val x = 0 := h x hxY
  exact hxX hX0

lemma disjoint_2_3 : (k : ℕ) → (X Y : Pi) → (X < Y) → (∀ g ∈ X.val.support, g ∉ Y.val.support) →
  ∀ g ∈ (Chromosome.prime^[k] X).support, g ∉ (Chromosome.prime^[k] Y).support := by
  intro k X Y hlt hdis
  induction k with
  | zero => exact hdis
  | succ i ih =>
    rw [prime_prime_other i X]
    rw [prime_prime_other i Y]
    sorry
    --exact disjoint_2_1 n (Chromosome.prime^[i] X) (Chromosome.prime^[i] Y) + induction hypothesis
    -- prime (Pi) doesn't play well

lemma step15_9 : (n : ℕ) → (X Y : Pi) → (hX : rank X = n) → (hY : rank Y = n) → (hlt : X < Y) →
  (∀ g ∈ X.val.support, g ∉ Y.val.support) → (k : ℕ) → (k ≥ 1) → (h : sigma_k X k = sigma_k Y k) →
  (h' : sigma_k X k ≠ (0, 0)) →
  (∃ U ∈ Pi, (IsMutation (Chromosome.prime^[k] X) U) ∧ (U ≤ Chromosome.prime^[k] Y)) →
  ∃ Z ∈ Pi, (IsMutation X Z) ∧ (Chromosome.prime^[k] Z = U) ∧ (Z ≤ Y) := by
  intro n X Y hX hY hlt hdis k k_1 sig_k_eq sig_k_not_0 ih
  --apply lifting lemma on ih.
  sorry
--with this we can assume sigma_k X k < sigma_k Y k (element-wise)

end Sigma
