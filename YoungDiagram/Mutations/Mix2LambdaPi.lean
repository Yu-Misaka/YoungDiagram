import YoungDiagram.Mutations.Mix2LambdaPi.type9
import YoungDiagram.Mutations.Mix2LambdaPi.type10
import YoungDiagram.Mutations.Mix2LambdaPi.type11
import YoungDiagram.Mutations.Mix2LambdaPi.type12
import YoungDiagram.Mutations.Mix2LambdaPi.type13
import YoungDiagram.Mutations.Mix2LambdaPi.type14
import YoungDiagram.Mutations.Mix2LambdaPi.type15
import YoungDiagram.Mutations.Mix2LambdaPi.type16
import YoungDiagram.Mutations.Mix2LambdaPi.type17
import YoungDiagram.Mutations.Basic

open Chromosome Variety Pointwise

variable {ε ε' : GeneType} {m n : ℕ}

namespace Mix2LambdaPi

inductive Primitive : Mix (2 • Lambda, Pi) → Mix (2 • Lambda, Pi) → Prop
  | type9 (ε : GeneType) (hε : ε ≠ .NonPolarized) (k : ℕ) :
      Primitive (X9 k) (Y9 hε k)
  | type10 (ε ε' : GeneType) (hε : ε ≠ .NonPolarized) (hε' : ε' ≠ .NonPolarized)
    {m n : ℕ} (h_le : m ≤ n) :
      Primitive (X10 h_le hε hε') (Y10 h_le hε hε')
  | type11 (ε : GeneType) (hε : ε ≠ .NonPolarized)
    {m n : ℕ} (h_le : m ≤ n) :
      Primitive (X11 h_le hε) (Y11 h_le hε)
  | type12 (ε : GeneType) (hε : ε ≠ .NonPolarized)
    {m n : ℕ} (h_le : m ≤ n) :
      Primitive (X12 h_le hε) (Y12 h_le hε)
  | type13 {m n : ℕ} (h_le : m ≤ n) :
      Primitive (X13 h_le) (Y13 h_le)
  | type14 (ε : GeneType) (hε : ε ≠ .NonPolarized)
    {m n : ℕ} (h_le : m ≤ n) :
      Primitive (X14 h_le hε) (Y14 h_le hε)
  | type15 (ε : GeneType) (hε : ε ≠ .NonPolarized)
    {m n : ℕ} (h_le : m ≤ n) :
      Primitive (X15 h_le hε) (Y15 h_le hε)
  | type16 (ε : GeneType) (hε : ε ≠ .NonPolarized)
    {m n : ℕ} (h_le : m ≤ n) :
      Primitive (X16 h_le hε) (Y16 h_le hε)
  | type17 (ε : GeneType) (hε : ε ≠ .NonPolarized)
    {m n : ℕ} (h_le : m ≤ n) :
      Primitive (X17 h_le hε) (Y17 h_le hε)

inductive Step : Mix (2 • Lambda, Pi) → Mix (2 • Lambda, Pi) → Prop
  | mk (X Y Z : Mix (2 • Lambda, Pi)) (h : Primitive X Y) :
      Step (X + Z) (Y + Z)

lemma Primitive.isMutation {X Y : Mix (2 • Lambda, Pi)} (h : Primitive X Y) :
    IsMutation X Y := by
  cases h with
  | type9 ε hε k =>
    exact ⟨mutation_type9_le,
      mutation_type9_ne, mutation_type9_signature_eq⟩
  | type10 ε ε' hε hε' h_le =>
    exact ⟨mutation_type10_le h_le,
      mutation_type10_ne h_le, mutation_type10_signature_eq h_le⟩
  | type11 ε hε h_le =>
    exact ⟨mutation_type11_le h_le,
      mutation_type11_ne, mutation_type11_signature_eq h_le⟩
  | type12 ε hε h_le =>
    exact ⟨mutation_type12_le h_le,
      mutation_type12_ne h_le, mutation_type12_signature_eq h_le⟩
  | type13 h_le =>
    exact ⟨mutation_type13_le h_le,
      mutation_type13_ne, mutation_type13_signature_eq⟩
  | type14 ε hε h_le =>
    exact ⟨mutation_type14_le h_le,
      mutation_type14_ne, mutation_type14_signature_eq⟩
  | type15 ε hε h_le =>
    exact ⟨mutation_type15_le h_le,
      mutation_type15_ne h_le, mutation_type15_signature_eq h_le⟩
  | type16 ε hε h_le =>
    exact ⟨mutation_type16_le h_le,
      mutation_type16_ne, mutation_type16_signature_eq h_le⟩
  | type17 ε hε h_le =>
    exact ⟨mutation_type17_le h_le,
      mutation_type17_ne, mutation_type17_signature_eq h_le⟩

lemma Primitive.neg {X Y : Mix (2 • Lambda, Pi)} (h : Primitive X Y) :
    Primitive (- X) (- Y) := by
  cases h with
  | type9 ε hε k =>
    rw [neg_X9, neg_Y9]; exact Primitive.type9 ..
  | type10 ε ε' hε hε' h_le =>
    rw [neg_X10, neg_Y10]; exact Primitive.type10 ..
  | type11 ε hε h_le =>
    rw [neg_X11, neg_Y11]; exact Primitive.type11 ..
  | type12 ε hε h_le =>
    rw [neg_X12, neg_Y12]; exact Primitive.type12 ..
  | type13 h_le =>
    rw [neg_X13, neg_Y13]; exact Primitive.type13 ..
  | type14 ε hε h_le =>
    rw [neg_X14, neg_Y14]; exact Primitive.type14 ..
  | type15 ε hε h_le =>
    rw [neg_X15, neg_Y15]; exact Primitive.type15 ..
  | type16 ε hε h_le =>
    rw [neg_X16, neg_Y16]; exact Primitive.type16 ..
  | type17 ε hε h_le =>
    rw [neg_X17, neg_Y17]; exact Primitive.type17 ..

lemma Step.isMutation {X Y : Mix (2 • Lambda, Pi)} (h : Step X Y) :
    IsMutation X Y := by
  cases h with
  | mk X Y Z h =>
    exact .add_right _ (Primitive.isMutation h)

lemma Step.neg {X Y : Mix (2 • Lambda, Pi)} (h : Step X Y) : Step (- X) (- Y) := by
  cases h with
  | mk X Y Z hPrime =>
    rw [Mix.tLambda_Pi_neg_add, Mix.tLambda_Pi_neg_add]
    exact Step.mk (- X) (- Y) (- Z) hPrime.neg

lemma Step.add_right (W : Mix (2 • Lambda, Pi)) {A B : Mix (2 • Lambda, Pi)}
    (h : Step A B) : Step (A + W) (B + W) := by
  cases h with
  | mk X Y Z hPrim =>
    rw [add_assoc, add_assoc]
    exact Step.mk X Y (Z + W) hPrim

lemma Step.of_neg {X Y : Mix (2 • Lambda, Pi)} (h : Step (-X) (-Y)) : Step X Y := by
  rw [← neg_neg X, ← neg_neg Y]
  exact h.neg

end Mix2LambdaPi
