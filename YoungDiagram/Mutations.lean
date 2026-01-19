import YoungDiagram.Chromosome
import Mathlib.Tactic

open Chromosome

structure IsMutation (X Y : Chromosome) : Prop where
  le : X ≤ Y
  ne : X ≠ Y
  sign_eq : signature X = signature Y

lemma IsMutation_add {X Y : Chromosome} (Z : Chromosome)
    (h : IsMutation X Y) : IsMutation (X + Z) (Y + Z) where
  le := add_le_add_right h.le Z
  ne := by simp [h.ne]
  sign_eq := by simp [h.sign_eq]

lemma IsMutation_of_add {X Y Z : Chromosome}
    (h : IsMutation (X + Z) (Y + Z)) : IsMutation X Y where
  le := le_of_add_le_add_right h.le
  ne := by simpa using h.ne
  sign_eq := by simpa using h.sign_eq

lemma IsMutation_iff_add {X Y Z : Chromosome} :
    IsMutation (X + Z) (Y + Z) ↔ IsMutation X Y :=
  ⟨IsMutation_of_add, IsMutation_add Z⟩

section type_1_isMutation

lemma type_1_is_mutation_ne {ε : GeneType}
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

lemma type_1_is_mutation_sign_eq {ε : GeneType} (hε : ε ≠ .NonPolarized)
  {m n : ℕ} (h_le : m ≤ n) (hm : 1 ≤ m) :
    (Gene.ofRank m ε + Gene.ofRank n (- ε)).signature =
    (Gene.ofRank (m - 1) (- ε) + Gene.ofRank (n + 1) ε).signature := by
  cases ε
  · tauto
  · rw [map_add, map_add, signature_it_ofRank_pos hm,
      signature_it_ofRank_pos (Nat.le_add_right_of_le <| hm.trans h_le),
      Nat.add_sub_cancel]
    ac_rfl
  · rw [map_add, map_add, signature_it_ofRank_neg hm,
      signature_it_ofRank_neg (Nat.le_add_right_of_le <| hm.trans h_le),
      Nat.add_sub_cancel]
    ac_rfl

lemma type_1_is_mutation_le_pos {m n : ℕ} (h_le : m ≤ n) :
    (Gene.ofRank m .Positive + Gene.ofRank n (- .Positive)) ≤
    (Gene.ofRank (m - 1) (- .Positive) + Gene.ofRank (n + 1) .Positive) := by
  rw [le_iff_dominates]
  intro k
  simp only [GeneType.neg_pos_eq_neg, iterate_map_add, map_add]
  repeat rw [prime_ofRank_it]
  by_cases hk1 : k < m
  · rw [signature_it_ofRank_pos (by omega), signature_it_ofRank_pos (by omega)]
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
      zero_add, signature_it_ofRank_pos (by omega)]
    convert_to _ ≤ (Gene.ofRank (n - k) .Negative).signature + (1, 0)
    · congr 3; omega
    simp; exact posPart_eq_self.mp rfl
  · rw [Nat.sub_right_comm, Nat.sub_eq_zero_of_le <| Nat.le_of_not_lt hk1,
      Nat.zero_sub, signature_ofRank_zero, signature_ofRank_zero, zero_add,
      zero_add, Nat.sub_eq_zero_of_le <| Nat.le_of_not_lt hk2,
      signature_ofRank_zero]
    exact signature_nonneg _

lemma type_1_is_mutation_le_neg {m n : ℕ} (h_le : m ≤ n) :
    (Gene.ofRank m .Negative + Gene.ofRank n (- .Negative)) ≤
    (Gene.ofRank (m - 1) (- .Negative) + Gene.ofRank (n + 1) .Negative) := by
  rw [le_iff_dominates]
  intro k
  simp only [GeneType.neg_neg_eq_pos, iterate_map_add, map_add]
  repeat rw [prime_ofRank_it]
  by_cases hk1 : k < m
  · rw [signature_it_ofRank_neg (by omega), signature_it_ofRank_neg (by omega)]
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
      zero_add, signature_it_ofRank_neg (by omega)]
    convert_to _ ≤ (Gene.ofRank (n - k) .Positive).signature + (0, 1)
    · congr 3; omega
    simp; exact posPart_eq_self.mp rfl
  · rw [Nat.sub_right_comm, Nat.sub_eq_zero_of_le <| Nat.le_of_not_lt hk1,
      Nat.zero_sub, signature_ofRank_zero, signature_ofRank_zero, zero_add,
      zero_add, Nat.sub_eq_zero_of_le <| Nat.le_of_not_lt hk2,
      signature_ofRank_zero]
    exact signature_nonneg _

lemma type_1_is_mutation_le {ε : GeneType} (hε : ε ≠ .NonPolarized)
  {m n : ℕ} (h_le : m ≤ n) :
    (Gene.ofRank m ε + Gene.ofRank n (- ε)) ≤
    (Gene.ofRank (m - 1) (- ε) + Gene.ofRank (n + 1) ε) :=
  match ε with
  | .NonPolarized => by absurd hε; decide
  | .Positive => type_1_is_mutation_le_pos h_le
  | .Negative => type_1_is_mutation_le_neg h_le

end type_1_isMutation

inductive PrimitiveMutation : Chromosome → Chromosome → Prop
  | type_1 {ε : GeneType} (hε : ε ≠ .NonPolarized)
    {m n : ℕ} (hle : m ≤ n) (hm : 1 ≤ m) :
      PrimitiveMutation
        (Gene.ofRank m ε + Gene.ofRank n (- ε))
        (Gene.ofRank (m - 1) (- ε) + Gene.ofRank (n + 1) ε)
  | type_2 {ε : GeneType} (hε : ε ≠ .NonPolarized)
    {m n : ℕ} (hle : m ≤ n) (hm : 1 < m) :
      PrimitiveMutation
        (Gene.ofRank m ε + Gene.ofRank n (- ε))
        (Gene.ofRank (m - 2) ε + Gene.ofRank (n + 2) ε)
  | type_3 {ε : GeneType} (hε : ε ≠ .NonPolarized)
    {m n : ℕ} (hle : m ≤ n) (hm : 1 ≤ m) :
      PrimitiveMutation
        (Gene.ofRank' m ε + Gene.ofRank' n (- ε))
        (Gene.ofRank' (m - 1) ε + Gene.ofRank' (n + 1) (- ε))

lemma PrimitiveMutation_isMutation {X Y : Chromosome} (h : PrimitiveMutation X Y) :
    IsMutation X Y := by
  cases h with
  | @type_1 ε hε m n hle hm =>
    exact ⟨type_1_is_mutation_le hε hle,
      type_1_is_mutation_ne hle hm, type_1_is_mutation_sign_eq hε hle hm⟩
  | @type_2 ε hε m n hle hm => sorry
  | @type_3 ε hε m n hle hm => sorry
