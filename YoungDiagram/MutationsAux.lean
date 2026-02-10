import YoungDiagram.Chromosome
import Mathlib.Tactic

open Chromosome

section type1_isMutation

lemma mutation_type1_ne {ε : GeneType}
  {m n : ℕ} (h_le : m ≤ n) (hm : 1 ≤ m) :
    (Gene.ofRank m ε + Gene.ofRank n (- ε)) ≠
    (Gene.ofRank (m - 1) (- ε) + Gene.ofRank (n + 1) ε) := by
  have h_n : n ≠ 0 := by omega
  have h_m : m ≠ 0 := by omega
  simp [h_n, h_m, Gene.ofRank_def]
  split_ifs with h
  · by_contra!
    replace this := (Finsupp.ext_iff.1 this) ⟨m, ε, hm⟩
    simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same, zero_add] at this
    convert_to 1 + _ = 0 at this
    · refine Finsupp.single_eq_of_ne ?_
      simp only [ne_eq, Gene.mk.injEq, and_true]
      omega
    omega
  · by_contra!
    replace this := (Finsupp.ext_iff.1 this) ⟨m, ε, hm⟩
    simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same] at this
    convert_to 1 + _ = 0 at this
    · rw [Nat.add_eq_zero_iff]
      split_ands <;> refine Finsupp.single_eq_of_ne ?_
      · simp only [ne_eq, Gene.mk.injEq, not_and]
        omega
      · simp only [ne_eq, Gene.mk.injEq, and_true]
        omega
    omega

lemma mutation_type1_signature_eq {ε : GeneType} (hε : ε ≠ .NonPolarized)
  {m n : ℕ} (h_le : m ≤ n) (hm : 1 ≤ m) :
    (Gene.ofRank m ε + Gene.ofRank n (- ε)).signature =
    (Gene.ofRank (m - 1) (- ε) + Gene.ofRank (n + 1) ε).signature := by
  cases ε
  · tauto
  · rw [map_add, map_add, signature_ofRank_positive_eq hm,
      signature_ofRank_positive_eq (Nat.le_add_right_of_le <| hm.trans h_le),
      Nat.add_sub_cancel]
    ac_rfl
  · rw [map_add, map_add, signature_ofRank_negative_eq hm,
      signature_ofRank_negative_eq (Nat.le_add_right_of_le <| hm.trans h_le),
      Nat.add_sub_cancel]
    ac_rfl

lemma mutation_type1_le_positive {m n : ℕ} (h_le : m ≤ n) :
    (Gene.ofRank m .Positive + Gene.ofRank n (- .Positive)) ≤
    (Gene.ofRank (m - 1) (- .Positive) + Gene.ofRank (n + 1) .Positive) := by
  rw [le_iff_dominates]
  intro k
  simp only [GeneType.neg_pos_eq_neg, iterate_map_add, map_add]
  repeat rw [prime_iterate_ofRank]
  by_cases hk1 : k < m
  · rw [signature_ofRank_positive_eq (by omega), signature_ofRank_positive_eq (by omega)]
    convert_to _ ≤
      (Gene.ofRank (m - k - 1) .Negative).signature +
      ((Gene.ofRank (n - k) .Negative).signature + (1, 0))
    · congr 3
      · omega
      · congr 1; omega
    group; exact le_refl _
  by_cases hk2 : k < n
  · rw [Nat.sub_right_comm, Nat.sub_eq_zero_of_le <| Nat.le_of_not_lt hk1,
      Nat.zero_sub, signature_ofRank_zero, signature_ofRank_zero, zero_add,
      zero_add, signature_ofRank_positive_eq (by omega)]
    convert_to _ ≤ (Gene.ofRank (n - k) .Negative).signature + (1, 0)
    · congr 3; omega
    simp; exact posPart_eq_self.mp rfl
  · rw [Nat.sub_right_comm, Nat.sub_eq_zero_of_le <| Nat.le_of_not_lt hk1,
      Nat.zero_sub, signature_ofRank_zero, signature_ofRank_zero, zero_add,
      zero_add, Nat.sub_eq_zero_of_le <| Nat.le_of_not_lt hk2,
      signature_ofRank_zero]
    exact signature_nonneg _

lemma mutation_type1_le_negative {m n : ℕ} (h_le : m ≤ n) :
    (Gene.ofRank m .Negative + Gene.ofRank n (- .Negative)) ≤
    (Gene.ofRank (m - 1) (- .Negative) + Gene.ofRank (n + 1) .Negative) := by
  rw [le_iff_dominates]
  intro k
  simp only [GeneType.neg_neg_eq_pos, iterate_map_add, map_add]
  repeat rw [prime_iterate_ofRank]
  by_cases hk1 : k < m
  · rw [signature_ofRank_negative_eq (by omega), signature_ofRank_negative_eq (by omega)]
    convert_to _ ≤
      (Gene.ofRank (m - k - 1) .Positive).signature +
      ((Gene.ofRank (n - k) .Positive).signature + (0, 1))
    · congr 3
      · omega
      · congr 1; omega
    group; exact le_refl _
  by_cases hk2 : k < n
  · rw [Nat.sub_right_comm, Nat.sub_eq_zero_of_le <| Nat.le_of_not_lt hk1,
      Nat.zero_sub, signature_ofRank_zero, signature_ofRank_zero, zero_add,
      zero_add, signature_ofRank_negative_eq (by omega)]
    convert_to _ ≤ (Gene.ofRank (n - k) .Positive).signature + (0, 1)
    · congr 3; omega
    simp; exact posPart_eq_self.mp rfl
  · rw [Nat.sub_right_comm, Nat.sub_eq_zero_of_le <| Nat.le_of_not_lt hk1,
      Nat.zero_sub, signature_ofRank_zero, signature_ofRank_zero, zero_add,
      zero_add, Nat.sub_eq_zero_of_le <| Nat.le_of_not_lt hk2,
      signature_ofRank_zero]
    exact signature_nonneg _

lemma mutation_type1_le {ε : GeneType} (hε : ε ≠ .NonPolarized)
  {m n : ℕ} (h_le : m ≤ n) :
    (Gene.ofRank m ε + Gene.ofRank n (- ε)) ≤
    (Gene.ofRank (m - 1) (- ε) + Gene.ofRank (n + 1) ε) :=
  match ε with
  | .NonPolarized => by absurd hε; decide
  | .Positive => mutation_type1_le_positive h_le
  | .Negative => mutation_type1_le_negative h_le

end type1_isMutation

section type2_isMutation

lemma mutation_type2_ne {ε : GeneType}
  {m n : ℕ} (h_le : m ≤ n) (hm : 1 < m) :
    (Gene.ofRank m ε + Gene.ofRank n (- ε)) ≠
    (Gene.ofRank (m - 2) ε + Gene.ofRank (n + 2) ε) :=
  sorry

lemma mutation_type2_signature_eq {ε : GeneType} (hε : ε ≠ .NonPolarized)
  {m n : ℕ} (h_le : m ≤ n) (hm : 1 < m) :
    (Gene.ofRank m ε + Gene.ofRank n (- ε)).signature =
    (Gene.ofRank (m - 2) ε + Gene.ofRank (n + 2) ε).signature := by
  sorry

lemma mutation_type2_le_positive {m n : ℕ} (h_le : m ≤ n) (hm : 1 < m) :
    (Gene.ofRank m .Positive + Gene.ofRank n (- .Positive)) ≤
    (Gene.ofRank (m - 2) .Positive + Gene.ofRank (n + 2) .Positive) := by
  sorry

lemma mutation_type2_le_negative {m n : ℕ} (h_le : m ≤ n) (hm : 1 < m) :
    (Gene.ofRank m .Negative + Gene.ofRank n (- .Negative)) ≤
    (Gene.ofRank (m - 2) .Negative + Gene.ofRank (n + 2) .Negative) := by
  sorry

lemma mutation_type2_le {ε : GeneType} (hε : ε ≠ .NonPolarized)
  {m n : ℕ} (h_le : m ≤ n) (hm : 1 < m) :
    (Gene.ofRank m ε + Gene.ofRank n (- ε)) ≤
    (Gene.ofRank (m - 2) ε + Gene.ofRank (n + 2) ε) :=
  match ε with
  | .NonPolarized => by absurd hε; decide
  | .Positive => mutation_type2_le_positive h_le hm
  | .Negative => mutation_type2_le_negative h_le hm

end type2_isMutation

section type3_isMutation

lemma mutation_type3_ne {ε : GeneType}
  {m n : ℕ} (h_le : m ≤ n) (hm : 1 ≤ m) :
    (Gene.ofRankAlt m ε + Gene.ofRankAlt n (- ε)) ≠
    (Gene.ofRankAlt (m - 1) ε + Gene.ofRankAlt (n + 1) (- ε)) := by
  sorry

lemma mutation_type3_signature_eq {ε : GeneType} (hε : ε ≠ .NonPolarized)
  {m n : ℕ} (h_le : m ≤ n) (hm : 1 ≤ m) :
    (Gene.ofRankAlt m ε + Gene.ofRankAlt n (- ε)).signature =
    (Gene.ofRankAlt (m - 1) ε + Gene.ofRankAlt (n + 1) (- ε)).signature := by
  sorry

lemma mutation_type3_le {ε : GeneType} (hε : ε ≠ .NonPolarized)
  {m n : ℕ} (h_le : m ≤ n) (hm : 1 ≤ m) :
    (Gene.ofRankAlt m ε + Gene.ofRankAlt n (- ε)) ≤
    (Gene.ofRankAlt (m - 1) ε + Gene.ofRankAlt (n + 1) (- ε)) := by
  sorry

end type3_isMutation
