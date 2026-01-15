import YoungDiagram.Chromosome

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

inductive PrimitiveMutation : Chromosome → Chromosome → Prop
  | type_1 {ε : GeneType} {hε : ε ≠ .NonPolarized}
    {m n : ℕ} (hle : m ≤ n) (hm : 1 ≤ m) :
      PrimitiveMutation
        (Gene.ofRank m ε + Gene.ofRank n (- ε))
        (Gene.ofRank (m - 1) (- ε) + Gene.ofRank (n + 1) ε)
  | type_2 {ε : GeneType} {hε : ε ≠ .NonPolarized}
    {m n : ℕ} (hle : m ≤ n) (hm : 1 < m) :
      PrimitiveMutation
        (Gene.ofRank m ε + Gene.ofRank n (- ε))
        (Gene.ofRank (m - 2) ε + Gene.ofRank (n + 2) ε)
  | type_3 {ε : GeneType} {hε : ε ≠ .NonPolarized}
    {m n : ℕ} (hle : m ≤ n) (hm : 1 ≤ m) :
      PrimitiveMutation
        (Gene.ofRank' m ε + Gene.ofRank' n (- ε))
        (Gene.ofRank' (m - 1) ε + Gene.ofRank' (n + 1) (- ε))

lemma type_1_is_mutation_ne {ε : GeneType}
  {m n : ℕ} (h_le : m ≤ n) (hm : 1 ≤ m) :
    (Gene.ofRank m ε + Gene.ofRank n (- ε)) ≠
    (Gene.ofRank (m - 1) (- ε) + Gene.ofRank (n + 1) ε) := by
  have h_n : n ≠ 0 := by omega
  have h_m : m ≠ 0 := by omega
  simp [h_n, h_m]
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

lemma type_1_is_mutation_sign_eq {ε : GeneType} {hε : ε ≠ .NonPolarized}
  {m n : ℕ} (h_le : m ≤ n) (hm : 1 ≤ m) :
    (Gene.ofRank m ε + Gene.ofRank n (- ε)).signature =
    (Gene.ofRank (m - 1) (- ε) + Gene.ofRank (n + 1) ε).signature := by
  cases ε
  · tauto
  · rw [signature_add, signature_add, signature_it_ofRank_pos hm,
      signature_it_ofRank_pos (Nat.le_add_right_of_le <| hm.trans h_le),
      Nat.add_sub_cancel]
    ac_rfl
  · rw [signature_add, signature_add, signature_it_ofRank_neg hm,
      signature_it_ofRank_neg (Nat.le_add_right_of_le <| hm.trans h_le),
      Nat.add_sub_cancel]
    ac_rfl

lemma type_1_is_mutation_le {ε : GeneType} {hε : ε ≠ .NonPolarized}
  {m n : ℕ} (h_le : m ≤ n) (hm : 1 ≤ m) :
    (Gene.ofRank m ε + Gene.ofRank n (- ε)) ≤
    (Gene.ofRank (m - 1) (- ε) + Gene.ofRank (n + 1) ε) := by
  have h_n : n ≠ 0 := by omega
  have h_m  : m ≠ 0 := by omega
  simp [h_n, h_m]
  split_ifs with h <;> intro k
  · sorry
  · sorry
