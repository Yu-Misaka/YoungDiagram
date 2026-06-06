import YoungDiagram

open Chromosome

variable {ε : GeneType} {m n : ℕ}

-- Φ = (Λ, Π): g ranks even, g^ε ranks odd.

local notation "type7X" =>
  Gene.ofRank (2 * m + 1) ε +
  Gene.ofRank (2 * n + 1) (- ε)
local notation "type7Y" =>
  Gene.ofRank (2 * m) GeneType.NonPolarized +
  Gene.ofRank (2 * n + 2) GeneType.NonPolarized

variable (h_le : m ≤ n)

include h_le

section Aux

section type7_isMutation

omit h_le in
lemma mutation_type7_ne : type7X ≠ type7Y := by
  intro h
  replace h := congr_arg (· ⟨2 * n + 2, .NonPolarized, by omega⟩) h
  have h_m : 2 * m + 1 ≠ 0 := by omega
  have h_n : 2 * n + 1 ≠ 0 := by omega
  have h_n' : 2 * n + 2 ≠ 0 := by omega
  simp only [Gene.ofRank_def, h_m, h_n, h_n', ↓reduceDIte, Finsupp.coe_add,
    Pi.add_apply, Finsupp.single_eq_same, Finsupp.single_apply, Gene.mk.injEq,
    Nat.reduceEqDiff, Nat.add_left_cancel_iff, false_and] at h
  split_ifs at h <;> omega

lemma mutation_type7_iterate_signature_eq (i k : ℕ) (hi : i ≤ k) :
    (prime^[i] (Gene.ofRank (2 * m + 1 + k) ε +
      Gene.ofRank (2 * n + 1 + k) (- ε))).signature =
    (prime^[i] (Gene.ofRank (2 * m + k) .NonPolarized +
      Gene.ofRank (2 * n + 2 + k) .NonPolarized)).signature := by
  have eq1 : 2 * m + 1 + k - i = 2 * m + k - i + 1 := by omega
  have eq2 : 2 * n + 1 + k - i = 2 * n + 2 + k - i - 1 := by omega
  have hn : 1 ≤ 2 * n + 2 + k - i := by omega
  rw [iterate_map_add, iterate_map_add, prime_iterate_ofRank, prime_iterate_ofRank,
    prime_iterate_ofRank, prime_iterate_ofRank, map_add, map_add, eq1, eq2,
    signature_ofRank_succ_add_pred_neg hn]
  grind only [= Nat.even_iff]

lemma mutation_type7_signature_eq :
    signature type7X = signature type7Y := by
  have := mutation_type7_iterate_signature_eq (ε := ε) h_le 0 0 le_rfl
  rwa [Function.iterate_zero_apply, Function.iterate_zero_apply, add_zero, add_zero] at this

lemma mutation_type7_le : type7X ≤ type7Y := by
  intro k
  simp only [iterate_map_add, map_add, prime_iterate_ofRank]
  by_cases hle1 : k ≤ 2 * m
  · have eq1 : 2 * m + 1 - k = 2 * m - k + 1 := by omega
    have eq2 : 2 * n + 1 - k = 2 * n + 2 - k - 1 := by omega
    have hn : 1 ≤ 2 * n + 2 - k := by omega
    rw [eq1, eq2, signature_ofRank_succ_add_pred_neg hn]
    grind only [= Nat.even_iff]
  · by_cases hle2 : k ≤ 2 * n + 1
    · have eq1 : 2 * m + 1 - k = 0 := by omega
      have eq2 : 2 * m - k = 0 := by omega
      have le1 : k ≤ 2 * n + 2 := by omega
      rw [eq1, eq2, Gene.ofRank_zero, Gene.ofRank_zero, map_zero, zero_add,
        zero_add, signature_ofRank_nonPolarized]
      convert Chromosome.signature_ofRank_le
      <;> (rw [Nat.cast_sub hle2, Nat.cast_sub le1, Nat.cast_add, Nat.cast_add]; ring)
    · have eq1 : 2 * m + 1 - k = 0 := by omega
      have eq2 : 2 * m - k = 0 := by omega
      have eq3 : 2 * n + 1 - k = 0 := by omega
      have eq4 : 2 * n + 2 - k = 0 := by omega
      simp [eq1, eq2, eq3, eq4, Gene.ofRank_zero]

end type7_isMutation

end Aux
