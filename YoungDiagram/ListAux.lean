import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Data.List.Iterate
import Mathlib.Data.Rat.Star

abbrev List.IsAlt {l : List Bool} (hl : l ≠ [] := by decide) : Prop :=
  l = List.iterate not (l.head hl) l.length

section signature_eq_pos

lemma iterate_not_true_succ_of_odd {n : ℕ} (hn : ¬ Even n) :
    List.iterate not true (n + 1) = List.iterate not true n ++ [false] := by
  have h := List.iterate_add not true n 1
  have hiter : not^[n] = not :=
    Function.Involutive.iterate_odd (f := not) Bool.involutive_not <|
      (Nat.not_even_iff_odd).1 hn
  rw [h, hiter]; rfl

lemma iterate_not_true_succ_of_even {n : ℕ} (hn : Even n) :
    List.iterate not true (n + 1) = List.iterate not true n ++ [true] := by
  have h := List.iterate_add not true n 1
  have hiter : not^[n] = id :=
    Function.Involutive.iterate_even Bool.involutive_not hn
  rw [h, hiter]; rfl

lemma count_false_eq_length_sub_count_true {l : List Bool} :
    List.count false l = l.length - List.count true l := by
  rw [List.count_eq_length_filter, List.count_eq_length_filter]
  refine (Nat.sub_eq_of_eq_add ?_).symm
  rw [List.length_eq_length_filter_add id]
  simp; ac_rfl

lemma count_iterate_not_true {n : ℕ} :
  (↑(List.count true (List.iterate not true n)),
   ↑(List.count false (List.iterate not true n))) =
    if Even n then ((n : ℚ) / 2, (n : ℚ) / 2)
    else (((n : ℚ) + 1) / 2, ((n : ℚ) - 1) / 2) := by
  induction n with
  | zero => simp
  | succ n hn =>
    split_ifs with h
    · replace h : ¬ Even n := Nat.even_add_one.mp h
      simp only [h, ↓reduceIte, Prod.mk.injEq, Nat.cast_add, Nat.cast_one] at hn ⊢
      have : List.count true (List.iterate not true (n + 1)) = (n + 1 : ℚ) / 2 := by
        rw [← hn.1, iterate_not_true_succ_of_odd h]; simp
      refine ⟨this, ?_⟩
      rw [count_false_eq_length_sub_count_true, Nat.cast_sub List.count_le_length, this,
        List.length_iterate, Nat.cast_add]
      linarith
    · replace h : Even n := Nat.not_odd_iff_even.mp <| Nat.odd_add_one.mp <|
        Nat.not_even_iff_odd.1 h
      simp only [h, ↓reduceIte, Prod.mk.injEq, Nat.cast_add, Nat.cast_one] at hn ⊢
      have : List.count true (List.iterate not true (n + 1)) =
          ((n : ℚ) + 1 + 1) / 2 := by
        rw [add_assoc, add_div, add_self_div_two, ← hn.1, iterate_not_true_succ_of_even h]; simp
      refine ⟨this, ?_⟩
      rw [count_false_eq_length_sub_count_true, Nat.cast_sub List.count_le_length, this,
        List.length_iterate, Nat.cast_add]
      linarith

end signature_eq_pos

section signature_eq_neg

lemma iterate_not_false_eq_map_not_iterate_not_true {n : ℕ} :
    List.iterate not false n = List.map not (List.iterate not true n) := by
  rw [← List.range_map_iterate, ← List.range_map_iterate, ← List.comp_map]
  congr
  funext x
  change (not^[x] ∘ not) true = (not ∘ not^[x]) true
  rw [← Function.iterate_succ', Function.iterate_succ]

lemma count_true_iterate_not_false {n : ℕ} :
    List.count true (List.iterate not false n) =
    n - List.count true (List.iterate not true n) := by
  nth_rw 2 [← List.length_iterate not true n]
  rw [← count_false_eq_length_sub_count_true, List.count_eq_length_filter,
    List.count_eq_length_filter]
  have := List.filter_map (f := not) (p := fun x ↦ x == true)
    (l := List.iterate not true n)
  rw [iterate_not_false_eq_map_not_iterate_not_true, this, List.length_map]
  congr
  funext x
  simp only [beq_true, Function.comp_apply, beq_false]

lemma count_iterate_not_false {n : ℕ} :
  (↑(List.count true (List.iterate not false n)),
   ↑(List.count false (List.iterate not false n))) =
    if Even n then ((n : ℚ) / 2, (n : ℚ) / 2)
    else (((n : ℚ) - 1) / 2, ((n : ℚ) + 1) / 2) := by
  have := @count_iterate_not_true n
  split_ifs with h
  all_goals
    simp [h] at this ⊢
    split_ands
    · rw [count_true_iterate_not_false, Nat.cast_sub, this.1]
      · linarith
      convert List.count_le_length; exact (List.length_iterate _ _ _).symm
    · rw [count_false_eq_length_sub_count_true, List.length_iterate, count_true_iterate_not_false,
        Nat.sub_sub_self, this.1]
      convert List.count_le_length; exact (List.length_iterate _ _ _).symm

end signature_eq_neg
