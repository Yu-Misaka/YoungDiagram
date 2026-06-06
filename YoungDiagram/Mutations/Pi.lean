import YoungDiagram.Mutations.Pi.type1
import YoungDiagram.Mutations.Pi.type2
import YoungDiagram.Mutations.Pi.type3
import YoungDiagram.Mutations.Basic

open Chromosome Variety

variable {ε : GeneType} {m n : ℕ}

namespace Pi

variable (hε : ε ≠ .NonPolarized)

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

lemma Primitive.isMutation {X Y : Pi} (h : Primitive X Y) :
    IsMutation X Y := by
  cases h with
  | type1 ε hε hle hm =>
    exact ⟨mutation_type1_le hε hle,
      mutation_type1_ne hle hm, mutation_type1_signature_eq hε hle hm⟩
  | type2 ε hε hle hm =>
    exact ⟨mutation_type2_le hε hle hm,
      mutation_type2_ne hle hm, mutation_type2_signature_eq hle hm⟩
  | type3 ε hε hle hm =>
    exact ⟨mutation_type3_le hε hle hm,
      mutation_type3_ne hle hm, mutation_type3_signature_eq hε hle hm⟩

lemma Primitive.neg {X Y : Pi} (h : Primitive X Y) :
    Primitive (- X) (- Y) := by
  cases h with
  | type1 ε hε hle hm =>
    rw [neg_X1, neg_Y1]; exact Primitive.type1 ..
  | type2 ε hε hle hm =>
    rw [neg_X2, neg_Y2]; exact Primitive.type2 ..
  | type3 ε hε hle hm =>
    rw [neg_X3, neg_Y3]; exact Primitive.type3 ..

lemma Step.isMutation {X Y : Pi} (h : Pi.Step X Y) :
    IsMutation X Y := by
  cases h with
  | mk X Y Z h =>
    exact .add_right _ (Pi.Primitive.isMutation h)

lemma Step.neg {X Y : Pi} (h : Step X Y) : Step (- X) (- Y) := by
  cases h with
  | mk X Y Z hPrime =>
    rw [neg_add, neg_add]; exact Step.mk (- X) (- Y) (- Z) hPrime.neg

lemma Step.add_right (W : Variety.Pi) {A B : Variety.Pi}
    (h : Pi.Step A B) : Pi.Step (A + W) (B + W) := by
  cases h with
  | mk X Y Z hPrim =>
    rw [add_assoc, add_assoc]
    exact Pi.Step.mk X Y (Z + W) hPrim

lemma Step.of_neg {X Y : Pi} (h : Step (-X) (-Y)) : Step X Y := by
  rw [← neg_neg X, ← neg_neg Y]
  exact h.neg

end Pi
