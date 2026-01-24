import YoungDiagram.MutationsAux
import YoungDiagram.Variety

namespace Chromosome

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

namespace Pi

variable {m n : ℕ} {ε : GeneType} (hε : ε ≠ .NonPolarized)

noncomputable section type_1

variable (hle : m ≤ n) (hm : 1 ≤ m)

def X₁ : Pi := by
  use Gene.ofRank m ε + Gene.ofRank n (- ε)
  rw [mem_Pi_iff, IsPolarized_iff_add]
  exact ⟨by rwa [IsPolarized_ofRank hm],
    by rwa [IsPolarized_ofRank (hm.trans hle),
      ← GeneType.nonpolarized_iff_neg_non]⟩

lemma X₁_eq : X₁ hε hle hm =
  Gene.ofRank m ε + Gene.ofRank n (- ε) := rfl

def Y₁ : Pi := by
  use Gene.ofRank (m - 1) (- ε) + Gene.ofRank (n + 1) ε
  rw [mem_Pi_iff, IsPolarized_iff_add]
  refine ⟨?_, by rwa [IsPolarized_ofRank (Nat.le_add_left 1 n)]⟩
  match m with
  | 1 =>
    rw [← mem_Pi_iff, Nat.sub_self, Gene.ofRank_zero]
    exact zero_mem _
  | m + 2 =>
    rwa [IsPolarized_ofRank (Nat.le_of_ble_eq_true rfl),
      ← GeneType.nonpolarized_iff_neg_non]

lemma Y₁_eq : Y₁ hε hle hm =
  Gene.ofRank (m - 1) (- ε) + Gene.ofRank (n + 1) ε := rfl

end type_1

noncomputable section type_2

variable (hle : m ≤ n) (hm : 1 < m)

def X₂ : Pi := X₁ hε hle (le_of_lt hm)

lemma X₂_eq : X₂ hε hle hm =
  Gene.ofRank m ε + Gene.ofRank n (- ε) := rfl

def Y₂ : Pi := by
  use Gene.ofRank (m - 2) ε + Gene.ofRank (n + 2) ε
  rw [mem_Pi_iff, IsPolarized_iff_add]
  refine ⟨?_, by rwa [IsPolarized_ofRank (Nat.le_add_left 1 (n + 1))]⟩
  match m with
  | 2 =>
    rw [← mem_Pi_iff, Nat.sub_self, Gene.ofRank_zero]
    exact zero_mem _
  | m + 3 => rwa [IsPolarized_ofRank (by omega)]

lemma Y₂_eq : Y₂ hε hle hm =
  Gene.ofRank (m - 2) ε + Gene.ofRank (n + 2) ε := rfl

end type_2

noncomputable section type_3

variable (hle : m ≤ n) (hm : 1 ≤ m)

def X₃ : Pi := by
  use Gene.ofRank' m ε + Gene.ofRank' n (- ε)
  rw [mem_Pi_iff, IsPolarized_iff_add]
  exact ⟨by rwa [IsPolarized_ofRank' hm], by
    rwa [IsPolarized_ofRank' (hm.trans hle),
      ← GeneType.nonpolarized_iff_neg_non]⟩

lemma X₃_eq : X₃ hε hle hm =
  Gene.ofRank' m ε + Gene.ofRank' n (- ε) := rfl

def Y₃ : Pi := by
  use Gene.ofRank' (m - 1) ε + Gene.ofRank' (n + 1) (- ε)
  rw [mem_Pi_iff, IsPolarized_iff_add]
  refine ⟨?_, by rwa [IsPolarized_ofRank' (by omega),
    ← GeneType.nonpolarized_iff_neg_non]⟩
  match m with
  | 1 =>
    rw [Nat.sub_self, Gene.ofRank'_def, Gene.ofRank_zero, ← mem_Pi_iff]
    exact zero_mem _
  | m + 2 => rwa [IsPolarized_ofRank' (by omega)]

end type_3

inductive PrimitiveMutation : Pi → Pi → Prop
  | type_1 (ε : GeneType) (hε : ε ≠ .NonPolarized)
    {m n : ℕ} (hle : m ≤ n) (hm : 1 ≤ m) :
      PrimitiveMutation (X₁ hε hle hm) (Y₁ hε hle hm)
  | type_2 (ε : GeneType) (hε : ε ≠ .NonPolarized)
    {m n : ℕ} (hle : m ≤ n) (hm : 1 < m) :
      PrimitiveMutation (X₂ hε hle hm) (Y₂ hε hle hm)
  | type_3 (ε : GeneType) (hε : ε ≠ .NonPolarized)
    {m n : ℕ} (hle : m ≤ n) (hm : 1 ≤ m) :
      PrimitiveMutation (X₃ hε hle hm) (Y₃ hε hle hm)

inductive MutationStep : Pi → Pi → Prop
  | mk (X Y Z : Pi) (h : PrimitiveMutation X Y) :
      MutationStep (X + Z) (Y + Z)

lemma PrimitiveMutation_isMutation {X Y : Pi}
  (h : PrimitiveMutation X Y) :
    IsMutation X Y := by
  cases h with
  | type_1 ε hε hle hm =>
    exact ⟨type_1_is_mutation_le hε hle,
      type_1_is_mutation_ne hle hm, type_1_is_mutation_sign_eq hε hle hm⟩
  | @type_2 ε hε m n hle hm => sorry
  | @type_3 ε hε m n hle hm => sorry

lemma MutationStep_isMutation {X Y : Pi}
  (h : MutationStep X Y) :
    IsMutation X Y := by
  cases h with
  | mk X Y Z h =>
    exact IsMutation_add _ (PrimitiveMutation_isMutation h)

end Pi

end Chromosome
