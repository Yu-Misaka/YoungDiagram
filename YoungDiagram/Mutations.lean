import YoungDiagram.Defs

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

#exit

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

lemma type_1_is_mutation_ne {ε : GeneType} {hε : ε ≠ .NonPolarized}
  {m n : ℕ} (h_le : m ≤ n) (hm : 1 ≤ m) :
    (Gene.ofRank m ε + Gene.ofRank n (- ε)) ≠
    (Gene.ofRank (m - 1) (- ε) + Gene.ofRank (n + 1) ε) := by

  sorry

lemma type_1_is_mutation_le {ε : GeneType} {hε : ε ≠ .NonPolarized}
  {m n : ℕ} (h_le : m ≤ n) (hm : 1 ≤ m) :
    (Gene.ofRank m ε + Gene.ofRank n (- ε)) ≤
    (Gene.ofRank (m - 1) (- ε) + Gene.ofRank (n + 1) ε) := by
  have h_n : n ≠ 0 := by omega
  have h_m  : m ≠ 0 := by omega
  simp [h_n, h_m, dominates]
  split_ifs with h <;> intro k
  ·
  sorry
