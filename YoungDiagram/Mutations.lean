import YoungDiagram.MutationsAux
import YoungDiagram.Variety

namespace Mutation

open Chromosome Variety

structure IsMutation (X Y : Chromosome) : Prop where
  le : X ≤ Y
  ne : X ≠ Y
  signature_eq : signature X = signature Y

lemma IsMutation_add {X Y : Chromosome} (Z : Chromosome)
    (h : IsMutation X Y) : IsMutation (X + Z) (Y + Z) where
  le := add_le_add_right h.le Z
  ne := by simp [h.ne]
  signature_eq := by simp [h.signature_eq]

lemma IsMutation_of_add {X Y Z : Chromosome}
    (h : IsMutation (X + Z) (Y + Z)) : IsMutation X Y where
  le := le_of_add_le_add_right h.le
  ne := by simpa using h.ne
  signature_eq := by simpa using h.signature_eq

lemma IsMutation_iff_add {X Y Z : Chromosome} :
    IsMutation (X + Z) (Y + Z) ↔ IsMutation X Y :=
  ⟨IsMutation_of_add, IsMutation_add Z⟩

namespace Pi

variable {m n : ℕ} {ε : GeneType} (hε : ε ≠ .NonPolarized)

noncomputable section type1

variable (hle : m ≤ n) (hm : 1 ≤ m)

def X1 : Pi := by
  use Gene.ofRank m ε + Gene.ofRank n (- ε)
  rw [mem_Pi_iff, IsPolarized_iff_add]
  exact ⟨by rwa [IsPolarized_ofRank hm],
    by rwa [IsPolarized_ofRank (hm.trans hle),
      ← GeneType.ne_nonPolarized_iff_neg_ne]⟩

lemma X1_eq : X1 hε hle hm =
  Gene.ofRank m ε + Gene.ofRank n (- ε) := rfl

def Y1 : Pi := by
  use Gene.ofRank (m - 1) (- ε) + Gene.ofRank (n + 1) ε
  rw [mem_Pi_iff, IsPolarized_iff_add]
  refine ⟨?_, by rwa [IsPolarized_ofRank (Nat.le_add_left 1 n)]⟩
  match m with
  | 1 =>
    rw [← mem_Pi_iff, Nat.sub_self, Gene.ofRank_zero]
    exact zero_mem _
  | m + 2 =>
    rwa [IsPolarized_ofRank (Nat.le_of_ble_eq_true rfl),
      ← GeneType.ne_nonPolarized_iff_neg_ne]

lemma Y1_eq : Y1 hε hle hm =
  Gene.ofRank (m - 1) (- ε) + Gene.ofRank (n + 1) ε := rfl

end type1

noncomputable section type2

variable (hle : m ≤ n) (hm : 1 < m)

def X2 : Pi := X1 hε hle (le_of_lt hm)

lemma X2_eq : X2 hε hle hm =
  Gene.ofRank m ε + Gene.ofRank n (- ε) := rfl

def Y2 : Pi := by
  use Gene.ofRank (m - 2) ε + Gene.ofRank (n + 2) ε
  rw [mem_Pi_iff, IsPolarized_iff_add]
  refine ⟨?_, by rwa [IsPolarized_ofRank (Nat.le_add_left 1 (n + 1))]⟩
  match m with
  | 2 =>
    rw [← mem_Pi_iff, Nat.sub_self, Gene.ofRank_zero]
    exact zero_mem _
  | m + 3 => rwa [IsPolarized_ofRank (by omega)]

lemma Y2_eq : Y2 hε hle hm =
  Gene.ofRank (m - 2) ε + Gene.ofRank (n + 2) ε := rfl

end type2

noncomputable section type3

variable (hle : m ≤ n) (hm : 1 ≤ m)

def X3 : Pi := by
  use Gene.ofRankAlt m ε + Gene.ofRankAlt n (- ε)
  rw [mem_Pi_iff, IsPolarized_iff_add]
  exact ⟨by rwa [IsPolarized_ofRankAlt hm], by
    rwa [IsPolarized_ofRankAlt (hm.trans hle),
      ← GeneType.ne_nonPolarized_iff_neg_ne]⟩

lemma X3_eq : X3 hε hle hm =
  Gene.ofRankAlt m ε + Gene.ofRankAlt n (- ε) := rfl

def Y3 : Pi := by
  use Gene.ofRankAlt (m - 1) ε + Gene.ofRankAlt (n + 1) (- ε)
  rw [mem_Pi_iff, IsPolarized_iff_add]
  refine ⟨?_, by rwa [IsPolarized_ofRankAlt (by omega),
    ← GeneType.ne_nonPolarized_iff_neg_ne]⟩
  match m with
  | 1 =>
    rw [Nat.sub_self, Gene.ofRankAlt_def, Gene.ofRank_zero, ← mem_Pi_iff]
    exact zero_mem _
  | m + 2 => rwa [IsPolarized_ofRankAlt (by omega)]

end type3

inductive Primitive : Pi → Pi → Prop
  | type1 (ε : GeneType) (hε : ε ≠ .NonPolarized)
    {m n : ℕ} (hle : m ≤ n) (hm : 1 ≤ m) :
      Primitive (X1 hε hle hm) (Y1 hε hle hm)
  | type2 (ε : GeneType) (hε : ε ≠ .NonPolarized)
    {m n : ℕ} (hle : m ≤ n) (hm : 1 < m) :
      Primitive (X2 hε hle hm) (Y2 hε hle hm)
  | type3 (ε : GeneType) (hε : ε ≠ .NonPolarized)
    {m n : ℕ} (hle : m ≤ n) (hm : 1 ≤ m) :
      Primitive (X3 hε hle hm) (Y3 hε hle hm)

inductive Step : Pi → Pi → Prop
  | mk (X Y Z : Pi) (h : Primitive X Y) :
      Step (X + Z) (Y + Z)

lemma Primitive.isMutation {X Y : Pi} (h : Primitive X Y) : IsMutation X Y := by
  cases h with
  | type1 ε hε hle hm =>
    exact ⟨mutation_type1_le hε hle,
      mutation_type1_ne hle hm, mutation_type1_signature_eq hε hle hm⟩
  | @type2 ε hε m n hle hm =>
    exact ⟨mutation_type2_le hε hle hm,
      mutation_type2_ne hle hm, mutation_type2_signature_eq hε hle hm⟩
  | @type3 ε hε m n hle hm =>
    exact ⟨mutation_type3_le hε hle hm,
      mutation_type3_ne hle hm, mutation_type3_signature_eq hε hle hm⟩

lemma Step.isMutation {X Y : Pi} (h : Step X Y) : IsMutation X Y := by
  cases h with
  | mk X Y Z h =>
    exact IsMutation_add _ (Primitive.isMutation h)

end Pi

def Step : (i : Fin 5) → (Label i) → (Label i) → Prop
  | 0 => Pi.Step
  | 1 => sorry
  | 2 => sorry
  | 3 => sorry
  | 4 => sorry

end Mutation
