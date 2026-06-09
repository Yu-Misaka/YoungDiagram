import YoungDiagram.Variety

open Chromosome

variable {ε : GeneType} {m n : ℕ}

-- Φ = (Π, Λ): g ranks odd, g^ε ranks even.

local notation "type5X" =>
  Gene.ofRank (2 * m + 1) GeneType.NonPolarized +
  Gene.ofRank (2 * n + 2) ε
local notation "type5Y" =>
  Gene.ofRank (2 * m) ε +
  Gene.ofRank (2 * n + 3) GeneType.NonPolarized

variable (h_le : m ≤ n)

include h_le

section Aux

namespace MixPiLambda

section type5_isMutation

lemma mutation_type5_ne : type5X ≠ type5Y := by
  intro h
  replace h := congr_arg (· ⟨2 * n + 3, .NonPolarized, by omega⟩) h
  have h_m : 2 * m + 1 ≠ 0 := by omega
  have h_n : 2 * n + 2 ≠ 0 := by omega
  have h_n' : 2 * n + 3 ≠ 0 := by omega
  simp only [Gene.ofRank_def, h_m, h_n, h_n', ↓reduceDIte, Finsupp.coe_add,
    Pi.add_apply, Finsupp.single_eq_same, Finsupp.single_apply, Gene.mk.injEq,
    Nat.reduceEqDiff, Nat.add_left_cancel_iff, false_and, and_true] at h
  rcases eq_or_ne (2 * m) 0 with hm0 | hm0
  · rw [dif_pos hm0] at h
    simp at h
    omega
  · rw [dif_neg hm0] at h
    simp only [Finsupp.single_apply, Gene.mk.injEq] at h
    split_ifs at h <;> omega

lemma mutation_type5_iterate_signature_eq (i k : ℕ) (hi : i ≤ k) :
    (prime^[i] (Gene.ofRank (2 * m + 1 + k) .NonPolarized +
      Gene.ofRank (2 * n + 2 + k) ε)).signature =
    (prime^[i] (Gene.ofRank (2 * m + k) ε +
      Gene.ofRank (2 * n + 3 + k) .NonPolarized)).signature := by
  have eq1 : 2 * m + 1 + k - i = 2 * m + k - i + 1 := by omega
  have eq2 : 2 * n + 3 + k - i = 2 * n + 2 + k - i + 1 := by omega
  rw [iterate_map_add, iterate_map_add, prime_iterate_ofRank, prime_iterate_ofRank,
    prime_iterate_ofRank, prime_iterate_ofRank, map_add, map_add, eq1, eq2,
    signature_ofRank_nonPolarized_succ_add]
  grind only [= Nat.even_iff]

lemma mutation_type5_signature_eq :
    signature type5X = signature type5Y := by
  have := mutation_type5_iterate_signature_eq (ε := ε) h_le 0 0 le_rfl
  rwa [Function.iterate_zero_apply, Function.iterate_zero_apply, add_zero, add_zero] at this

lemma mutation_type5_le : type5X ≤ type5Y := by
  intro k
  simp only [iterate_map_add, map_add, prime_iterate_ofRank]
  by_cases hle1 : k ≤ 2 * m
  · have eq1 : 2 * m + 1 - k = 2 * m - k + 1 := by omega
    have eq2 : 2 * n + 3 - k = 2 * n + 2 - k + 1 := by omega
    rw [eq1, eq2, signature_ofRank_nonPolarized_succ_add]
    grind only [= Nat.even_iff]
  · by_cases hle2 : k ≤ 2 * n + 2
    · have eq1 : 2 * m + 1 - k = 0 := by omega
      have eq2 : 2 * m - k = 0 := by omega
      have le1 : k ≤ 2 * n + 3 := by omega
      rw [eq1, eq2, Gene.ofRank_zero, Gene.ofRank_zero, map_zero, zero_add,
        zero_add, signature_ofRank_nonPolarized]
      convert Chromosome.signature_ofRank_le
      <;> (rw [Nat.cast_sub le1, Nat.cast_sub hle2, Nat.cast_add, Nat.cast_add]; ring)
    · have eq1 : 2 * m + 1 - k = 0 := by omega
      have eq2 : 2 * m - k = 0 := by omega
      have eq3 : 2 * n + 2 - k = 0 := by omega
      have eq4 : 2 * n + 3 - k = 0 := by omega
      rw [eq1, eq2, eq3, eq4, Gene.ofRank_zero, Gene.ofRank_zero, map_zero]

end type5_isMutation

end MixPiLambda

end Aux

section MixDefs

open Variety

namespace MixPiLambda

variable (hε : ε ≠ .NonPolarized)

include h_le

section type5

noncomputable def X5 : Mix (Pi, Lambda) := by
  have _ := h_le
  refine ⟨Gene.ofRank (2 * m + 1) GeneType.NonPolarized +
    Gene.ofRank (2 * n + 2) ε, ?_⟩
  rw [mem_Mix_iff, map_add, map_add,
    evenPart_ofRank, if_neg (by grind),
    evenPart_ofRank, if_pos (by grind),
    oddPart_ofRank, if_neg (by grind),
    oddPart_ofRank, if_pos (by grind),
    zero_add, add_zero]
  rw [mem_Pi_iff, mem_Lambda_iff,
    IsPolarized_ofRank (k := 2 * n + 2) (by omega),
    IsNonPolarized_ofRank (k := 2 * m + 1) (by omega)]
  exact ⟨hε, rfl⟩

lemma X5_eq : (X5 h_le hε).1 =
  Gene.ofRank (2 * m + 1) GeneType.NonPolarized +
  Gene.ofRank (2 * n + 2) ε := rfl

@[simp] lemma neg_X5 :
    - (X5 h_le hε) = X5 h_le (GeneType.neg_ne_nonPolarized_iff.1 hε) := by
  apply Subtype.ext
  rw [Mix.Pi_Lambda_neg_val, X5_eq, X5_eq, Chromosome.neg_add, neg_ofRank, neg_ofRank,
    GeneType.neg_nonPolarized]

noncomputable def Y5 : Mix (Pi, Lambda) := by
  have _ := h_le
  refine ⟨Gene.ofRank (2 * m) ε +
    Gene.ofRank (2 * n + 3) GeneType.NonPolarized, ?_⟩
  rw [mem_Mix_iff, map_add, map_add, evenPart_ofRank, if_pos (by grind),
    oddPart_ofRank, if_pos (by grind), evenPart_ofRank, if_neg (by grind),
    oddPart_ofRank, if_neg (by grind), zero_add, add_zero]
  match m with
  | 0 =>
    rw [Nat.mul_zero, Gene.ofRank_zero]
    refine ⟨zero_mem _, ?_⟩
    rw [mem_Lambda_iff, IsNonPolarized_ofRank (k := 2 * n + 3) (by omega)]
  | m + 1 =>
    refine ⟨?_, ?_⟩
    · rw [mem_Pi_iff, IsPolarized_ofRank (k := 2 * (m + 1)) (by omega)]
      exact hε
    · rw [mem_Lambda_iff, IsNonPolarized_ofRank (k := 2 * n + 3) (by omega)]

lemma Y5_eq : (Y5 h_le hε).1 =
  Gene.ofRank (2 * m) ε +
  Gene.ofRank (2 * n + 3) GeneType.NonPolarized := rfl

@[simp] lemma neg_Y5 :
    - (Y5 h_le hε) = Y5 h_le (GeneType.neg_ne_nonPolarized_iff.1 hε) := by
  apply Subtype.ext
  rw [Mix.Pi_Lambda_neg_val, Y5_eq, Y5_eq, Chromosome.neg_add, neg_ofRank, neg_ofRank,
    GeneType.neg_nonPolarized]

end type5

end MixPiLambda

end MixDefs
