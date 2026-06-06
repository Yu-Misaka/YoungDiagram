import YoungDiagram.Variety

open Chromosome

variable {ε : GeneType} {m n : ℕ}

-- Φ = (Π, Λ): g ranks odd, g^ε ranks even.

local notation "type6X" =>
  Gene.ofRank (2 * m + 2) ε +
  Gene.ofRank (2 * n + 3) GeneType.NonPolarized
local notation "type6Y" =>
  Gene.ofRank (2 * m + 1) GeneType.NonPolarized +
  Gene.ofRank (2 * n + 4) ε

variable (h_le : m ≤ n)

include h_le

section Aux

namespace MixPiLambda

section type6_isMutation

lemma mutation_type6_ne : type6X ≠ type6Y := by
  intro h
  replace h := congr_arg (· ⟨2 * n + 4, ε, by omega⟩) h
  have h_m : 2 * m + 2 ≠ 0 := by omega
  have h_n : 2 * n + 3 ≠ 0 := by omega
  have h_m' : 2 * m + 1 ≠ 0 := by omega
  have h_n' : 2 * n + 4 ≠ 0 := by omega
  simp only [Gene.ofRank_def, h_m, h_n, h_m', h_n', ↓reduceDIte, Finsupp.coe_add,
    Pi.add_apply, Finsupp.single_eq_same, Finsupp.single_apply, Gene.mk.injEq,
    Nat.reduceEqDiff, Nat.add_left_cancel_iff, false_and, and_true] at h
  split_ifs at h <;> omega

lemma mutation_type6_iterate_signature_eq (i k : ℕ) (hi : i ≤ k) :
    (prime^[i] (Gene.ofRank (2 * m + 2 + k) ε +
      Gene.ofRank (2 * n + 3 + k) .NonPolarized)).signature =
    (prime^[i] (Gene.ofRank (2 * m + 1 + k) .NonPolarized +
      Gene.ofRank (2 * n + 4 + k) ε)).signature := by
  have eq1 : 2 * m + 2 + k - i = 2 * m + 1 + k - i + 1 := by omega
  have eq2 : 2 * n + 4 + k - i = 2 * n + 3 + k - i + 1 := by omega
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
  by_cases hle1 : k ≤ 2 * m + 1
  · have eq1 : 2 * m + 2 - k = 2 * m + 1 - k + 1 := by omega
    have eq2 : 2 * n + 4 - k = 2 * n + 3 - k + 1 := by omega
    rw [eq1, eq2, signature_ofRank_succ_add_nonPolarized]
    grind only [= Nat.even_iff]
  · by_cases hle2 : k ≤ 2 * n + 3
    · have eq1 : 2 * m + 2 - k = 0 := by omega
      have eq2 : 2 * m + 1 - k = 0 := by omega
      have le1 : k ≤ 2 * n + 4 := by omega
      rw [eq1, eq2, Gene.ofRank_zero, Gene.ofRank_zero, map_zero, zero_add,
        zero_add, signature_ofRank_nonPolarized]
      convert Chromosome.signature_ofRank_ge
      <;> (rw [Nat.cast_sub hle2, Nat.cast_sub le1, Nat.cast_add, Nat.cast_add]; ring)
    · have eq1 : 2 * m + 2 - k = 0 := by omega
      have eq2 : 2 * m + 1 - k = 0 := by omega
      have eq3 : 2 * n + 3 - k = 0 := by omega
      have eq4 : 2 * n + 4 - k = 0 := by omega
      rw [eq1, eq2, eq3, eq4, Gene.ofRank_zero, Gene.ofRank_zero, map_zero]

end type6_isMutation

end MixPiLambda

end Aux

section MixDefs

open Variety

namespace MixPiLambda

omit h_le in
private lemma evenPart_ofRank_even {k : ℕ} {ε : GeneType} (hk : k ≠ 0) (he : Even k) :
    (Gene.ofRank k ε).evenPart = Gene.ofRank k ε := by
  rw [Gene.ofRank_def, dif_neg hk]
  exact Finsupp.filter_single_of_pos _ he

omit h_le in
private lemma evenPart_ofRank_odd {k : ℕ} {ε : GeneType} (ho : ¬ Even k) :
    (Gene.ofRank k ε).evenPart = 0 := by
  rcases eq_or_ne k 0 with rfl | hk
  · rw [Gene.ofRank_zero, map_zero]
  · rw [Gene.ofRank_def, dif_neg hk]
    exact Finsupp.filter_single_of_neg _ ho

omit h_le in
private lemma oddPart_ofRank_even {k : ℕ} {ε : GeneType} (he : Even k) :
    (Gene.ofRank k ε).oddPart = 0 := by
  rcases eq_or_ne k 0 with rfl | hk
  · rw [Gene.ofRank_zero, map_zero]
  · rw [Gene.ofRank_def, dif_neg hk]
    exact Finsupp.filter_single_of_neg _ (Nat.not_odd_iff_even.2 he)

omit h_le in
private lemma oddPart_ofRank_odd {k : ℕ} {ε : GeneType} (hk : k ≠ 0) (ho : ¬ Even k) :
    (Gene.ofRank k ε).oddPart = Gene.ofRank k ε := by
  rw [Gene.ofRank_def, dif_neg hk]
  exact Finsupp.filter_single_of_pos _ (Nat.not_even_iff_odd.1 ho)

variable (hε : ε ≠ .NonPolarized)

include h_le

section type6

noncomputable def X6 : Mix (Pi, Lambda) := by
  have _ := h_le
  refine ⟨Gene.ofRank (2 * m + 2) ε +
    Gene.ofRank (2 * n + 3) GeneType.NonPolarized, ?_⟩
  rw [mem_Mix_iff, map_add, map_add,
    evenPart_ofRank_even (k := 2 * m + 2) (by omega) ⟨m + 1, by ring⟩,
    evenPart_ofRank_odd (k := 2 * n + 3)
      (by rw [Nat.not_even_iff_odd]; exact ⟨n + 1, by ring⟩),
    oddPart_ofRank_even (k := 2 * m + 2) ⟨m + 1, by ring⟩,
    oddPart_ofRank_odd (k := 2 * n + 3) (by omega)
      (by rw [Nat.not_even_iff_odd]; exact ⟨n + 1, by ring⟩),
    add_zero, zero_add]
  rw [mem_Pi_iff, mem_Lambda_iff,
    IsPolarized_ofRank (k := 2 * m + 2) (by omega),
    IsNonPolarized_ofRank (k := 2 * n + 3) (by omega)]
  exact ⟨hε, rfl⟩

lemma X6_eq : (X6 h_le hε).1 =
  Gene.ofRank (2 * m + 2) ε +
  Gene.ofRank (2 * n + 3) GeneType.NonPolarized := rfl

@[simp] lemma neg_X6 :
    - (X6 h_le hε) = X6 h_le (GeneType.neg_ne_nonPolarized_iff.1 hε) := by
  apply Subtype.ext
  rw [Mix.Pi_Lambda_neg_val, X6_eq, X6_eq, Chromosome.neg_add, neg_ofRank, neg_ofRank,
    GeneType.neg_nonPolarized]

noncomputable def Y6 : Mix (Pi, Lambda) := by
  have _ := h_le
  refine ⟨Gene.ofRank (2 * m + 1) GeneType.NonPolarized +
    Gene.ofRank (2 * n + 4) ε, ?_⟩
  rw [mem_Mix_iff, map_add, map_add,
    evenPart_ofRank_odd (k := 2 * m + 1)
      (by rw [Nat.not_even_iff_odd]; exact ⟨m, rfl⟩),
    evenPart_ofRank_even (k := 2 * n + 4) (by omega) ⟨n + 2, by ring⟩,
    oddPart_ofRank_odd (k := 2 * m + 1) (by omega)
      (by rw [Nat.not_even_iff_odd]; exact ⟨m, rfl⟩),
    oddPart_ofRank_even (k := 2 * n + 4) ⟨n + 2, by ring⟩,
    zero_add, add_zero]
  rw [mem_Pi_iff, mem_Lambda_iff,
    IsPolarized_ofRank (k := 2 * n + 4) (by omega),
    IsNonPolarized_ofRank (k := 2 * m + 1) (by omega)]
  exact ⟨hε, rfl⟩

lemma Y6_eq : (Y6 h_le hε).1 =
  Gene.ofRank (2 * m + 1) GeneType.NonPolarized +
  Gene.ofRank (2 * n + 4) ε := rfl

@[simp] lemma neg_Y6 :
    - (Y6 h_le hε) = Y6 h_le (GeneType.neg_ne_nonPolarized_iff.1 hε) := by
  apply Subtype.ext
  rw [Mix.Pi_Lambda_neg_val, Y6_eq, Y6_eq, Chromosome.neg_add, neg_ofRank, neg_ofRank,
    GeneType.neg_nonPolarized]

end type6

end MixPiLambda

end MixDefs
