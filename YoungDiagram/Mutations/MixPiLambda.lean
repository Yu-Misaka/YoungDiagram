import YoungDiagram.Mutations.MixPiLambda.type4
import YoungDiagram.Mutations.MixPiLambda.type5
import YoungDiagram.Mutations.MixPiLambda.type6
import YoungDiagram.Mutations.MixPiLambda.type7
import YoungDiagram.Mutations.MixPiLambda.type8
import YoungDiagram.Mutations.Basic

open Chromosome Variety

variable {ε : GeneType} {m n : ℕ}

namespace MixPiLambda

inductive Primitive : Mix (Pi, Lambda) → Mix (Pi, Lambda) → Prop
  | type4 (ε : GeneType) (hε : ε ≠ .NonPolarized)
    {m n : ℕ} (h_le : m ≤ n) :
      Primitive (X4 h_le) (Y4 h_le hε)
  | type5 (ε : GeneType) (hε : ε ≠ .NonPolarized)
    {m n : ℕ} (h_le : m ≤ n) :
      Primitive (X5 h_le hε) (Y5 h_le hε)
  | type6 (ε : GeneType) (hε : ε ≠ .NonPolarized)
    {m n : ℕ} (h_le : m ≤ n) :
      Primitive (X6 h_le hε) (Y6 h_le hε)
  | type7 (ε : GeneType) (hε : ε ≠ .NonPolarized)
    {m n : ℕ} (h_le : m ≤ n) :
      Primitive (X7 h_le hε) (Y7 h_le)
  | type8 (ε : GeneType) (hε : ε ≠ .NonPolarized)
    {m n : ℕ} (h_le : m ≤ n) :
      Primitive (X8 h_le hε) (Y8 h_le hε)

inductive Step : Mix (Pi, Lambda) → Mix (Pi, Lambda) → Prop
  | mk (X Y Z : Mix (Pi, Lambda)) (h : Primitive X Y) :
      Step (X + Z) (Y + Z)

lemma Primitive.isMutation {X Y : Mix (Pi, Lambda)} (h : Primitive X Y) :
    IsMutation X Y := by
  cases h with
  | type4 ε hε h_le =>
    exact ⟨mutation_type4_le h_le,
      mutation_type4_ne, mutation_type4_signature_eq h_le⟩
  | type5 ε hε h_le =>
    exact ⟨mutation_type5_le h_le,
      mutation_type5_ne h_le, mutation_type5_signature_eq h_le⟩
  | type6 ε hε h_le =>
    exact ⟨mutation_type6_le h_le,
      mutation_type6_ne h_le, mutation_type6_signature_eq h_le⟩
  | type7 ε hε h_le =>
    exact ⟨mutation_type7_le h_le,
      mutation_type7_ne, mutation_type7_signature_eq h_le⟩
  | type8 ε hε h_le =>
    exact ⟨mutation_type8_le h_le,
      mutation_type8_ne h_le, mutation_type8_signature_eq h_le⟩

lemma Primitive.neg {X Y : Mix (Pi, Lambda)} (h : Primitive X Y) :
    Primitive (- X) (- Y) := by
  cases h with
  | type4 ε hε h_le =>
    rw [neg_X4, neg_Y4]; exact Primitive.type4 ..
  | type5 ε hε h_le =>
    rw [neg_X5, neg_Y5]; exact Primitive.type5 ..
  | type6 ε hε h_le =>
    rw [neg_X6, neg_Y6]; exact Primitive.type6 ..
  | type7 ε hε h_le =>
    rw [neg_X7, neg_Y7]; exact Primitive.type7 ..
  | type8 ε hε h_le =>
    rw [neg_X8, neg_Y8]; exact Primitive.type8 ..

lemma Step.isMutation {X Y : Mix (Pi, Lambda)} (h : Step X Y) :
    IsMutation X Y := by
  cases h with
  | mk X Y Z h =>
    exact .add_right _ (Primitive.isMutation h)

lemma Step.neg {X Y : Mix (Pi, Lambda)} (h : Step X Y) : Step (- X) (- Y) := by
  cases h with
  | mk X Y Z hPrime =>
    rw [Mix.Pi_Lambda_neg_add, Mix.Pi_Lambda_neg_add]
    exact Step.mk (- X) (- Y) (- Z) hPrime.neg

lemma Step.add_right (W : Mix (Pi, Lambda)) {A B : Mix (Pi, Lambda)}
    (h : Step A B) : Step (A + W) (B + W) := by
  cases h with
  | mk X Y Z hPrim =>
    rw [add_assoc, add_assoc]
    exact Step.mk X Y (Z + W) hPrim

lemma Step.of_neg {X Y : Mix (Pi, Lambda)} (h : Step (-X) (-Y)) : Step X Y := by
  rw [← neg_neg X, ← neg_neg Y]
  exact h.neg

end MixPiLambda
