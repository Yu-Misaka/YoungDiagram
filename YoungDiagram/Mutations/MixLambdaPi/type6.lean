import YoungDiagram

open Chromosome

variable {ε : GeneType} {m n : ℕ}

-- Φ = (Λ, Π): g ranks even, g^ε ranks odd.

local notation "type6X" =>
  Gene.ofRank (2 * m + 1) ε +
  Gene.ofRank (2 * n + 2) GeneType.NonPolarized
local notation "type6Y" =>
  Gene.ofRank (2 * m) GeneType.NonPolarized +
  Gene.ofRank (2 * n + 3) ε

variable (h_le : m ≤ n)

include h_le

section Aux

section type6_isMutation

lemma mutation_type6_ne : type6X ≠ type6Y := by
  intro h
  replace h := congr_arg (· ⟨2 * n + 3, ε, by omega⟩) h
  have h_m : 2 * m + 1 ≠ 0 := by omega
  have h_n : 2 * n + 2 ≠ 0 := by omega
  have h_n' : 2 * n + 3 ≠ 0 := by omega
  simp only [Gene.ofRank_def, h_m, h_n, h_n', ↓reduceDIte, Finsupp.coe_add,
    Pi.add_apply, Finsupp.single_eq_same, Finsupp.single_apply, Gene.mk.injEq,
    Nat.reduceEqDiff, Nat.add_left_cancel_iff, false_and, and_true] at h
  split_ifs at h <;> omega

lemma mutation_type6_iterate_signature_eq (i k : ℕ) (hi : i ≤ k) :
    (prime^[i] (Gene.ofRank (2 * m + 1 + k) ε +
      Gene.ofRank (2 * n + 2 + k) .NonPolarized)).signature =
    (prime^[i] (Gene.ofRank (2 * m + k) .NonPolarized +
      Gene.ofRank (2 * n + 3 + k) ε)).signature := by
  have eq1 : 2 * m + 1 + k - i = 2 * m + k - i + 1 := by omega
  have eq2 : 2 * n + 3 + k - i = 2 * n + 2 + k - i + 1 := by omega
  rw [iterate_map_add, iterate_map_add, prime_iterate_ofRank, prime_iterate_ofRank,
    prime_iterate_ofRank, prime_iterate_ofRank, map_add, map_add, eq1, eq2,
    signature_ofRank_succ_add_nonPolarized]
  grind only [= Nat.even_iff]

lemma mutation_type6_signature_eq :
    signature type6X = signature type6Y := by
  have := mutation_type6_iterate_signature_eq (ε := ε) h_le 0 0 le_rfl
  rwa [Function.iterate_zero_apply, Function.iterate_zero_apply, add_zero, add_zero] at this

lemma mutation_type6_le : type6X ≤ type6Y := by
  intro k
  simp only [iterate_map_add, map_add, prime_iterate_ofRank]
  by_cases hle1 : k ≤ 2 * m
  · have eq1 : 2 * m + 1 - k = 2 * m - k + 1 := by omega
    have eq2 : 2 * n + 3 - k = 2 * n + 2 - k + 1 := by omega
    rw [eq1, eq2, signature_ofRank_succ_add_nonPolarized]
    grind only [= Nat.even_iff]
  · by_cases hle2 : k ≤ 2 * n + 2
    · have eq1 : 2 * m + 1 - k = 0 := by omega
      have eq2 : 2 * m - k = 0 := by omega
      have le1 : k ≤ 2 * n + 3 := by omega
      rw [eq1, eq2, Gene.ofRank_zero, Gene.ofRank_zero, map_zero, zero_add,
        zero_add, signature_ofRank_nonPolarized]
      convert Chromosome.signature_ofRank_ge
      <;> (rw [Nat.cast_sub hle2, Nat.cast_sub le1, Nat.cast_add, Nat.cast_add]; ring)
    · have eq1 : 2 * m + 1 - k = 0 := by omega
      have eq2 : 2 * m - k = 0 := by omega
      have eq3 : 2 * n + 2 - k = 0 := by omega
      have eq4 : 2 * n + 3 - k = 0 := by omega
      rw [eq1, eq2, eq3, eq4, Gene.ofRank_zero, Gene.ofRank_zero, map_zero]

end type6_isMutation

end Aux
