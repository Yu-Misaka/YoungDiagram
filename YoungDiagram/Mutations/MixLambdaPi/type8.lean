import YoungDiagram.Variety

open Chromosome

variable {ε : GeneType} {m n : ℕ}

-- Φ = (Λ, Π): g ranks even, g^ε ranks odd.

local notation "type8X" =>
  Gene.ofRank (2 * m + 3) ε +
  Gene.ofRank (2 * n + 3) ε
local notation "type8Y" =>
  Gene.ofRank (2 * m + 1) ε +
  Gene.ofRank (2 * n + 5) ε

variable (h_le : m ≤ n)

include h_le

section Aux

namespace MixLambdaPi

section type8_isMutation

lemma mutation_type8_ne : type8X ≠ type8Y := by
  intro h
  replace h := congr_arg (· ⟨2 * n + 5, ε, by omega⟩) h
  have h_m : 2 * m + 3 ≠ 0 := by omega
  have h_n : 2 * n + 3 ≠ 0 := by omega
  have h_m' : 2 * m + 1 ≠ 0 := by omega
  have h_n' : 2 * n + 5 ≠ 0 := by omega
  simp only [Gene.ofRank_def, h_m, h_n, h_m', h_n', ↓reduceDIte, Finsupp.coe_add,
    Pi.add_apply, Finsupp.single_eq_same, Finsupp.single_apply, Gene.mk.injEq,
    Nat.reduceEqDiff, Nat.add_left_cancel_iff, and_true] at h
  split_ifs at h <;> omega

lemma mutation_type8_iterate_signature_eq (i k : ℕ) (hi : i ≤ k) :
    (prime^[i] (Gene.ofRank (2 * m + 3 + k) ε +
      Gene.ofRank (2 * n + 3 + k) ε)).signature =
    (prime^[i] (Gene.ofRank (2 * m + 1 + k) ε +
      Gene.ofRank (2 * n + 5 + k) ε)).signature := by
  have eq1 : 2 * m + 3 + k - i = 2 * m + 1 + k - i + 2 := by omega
  have eq2 : 2 * n + 5 + k - i = 2 * n + 3 + k - i + 2 := by omega
  rw [iterate_map_add, iterate_map_add, prime_iterate_ofRank, prime_iterate_ofRank,
    prime_iterate_ofRank, prime_iterate_ofRank, map_add, map_add, eq1, eq2,
    signature_ofRank_add_two_add]

lemma mutation_type8_signature_eq :
    signature type8X = signature type8Y := by
  have := mutation_type8_iterate_signature_eq (ε := ε) h_le 0 0 le_rfl
  rwa [Function.iterate_zero_apply, Function.iterate_zero_apply, add_zero, add_zero] at this

lemma mutation_type8_le : type8X ≤ type8Y := by
  intro k
  simp only [iterate_map_add, map_add, prime_iterate_ofRank]
  by_cases hk1 : 2 * n + 3 < k
  · have eq1 : 2 * m + 3 - k = 0 := by omega
    have eq2 : 2 * m + 1 - k = 0 := by omega
    rw [eq1, eq2, Nat.sub_eq_zero_of_le hk1.le, Gene.ofRank_zero, map_zero,
      add_zero, zero_add]
    exact signature_nonneg _
  by_cases hk2 : 2 * m + 1 < k
  · have eq1 : 2 * n + 5 - k - 2 = 2 * n + 3 - k := by omega
    have le1 : 2 * m + 3 - k < 2 := by omega
    rw [Nat.sub_eq_zero_of_le hk2.le, Gene.ofRank_zero, map_zero, zero_add,
      signature_ofRank_eq₂ (k := 2 * n + 5 - k) (by omega), eq1, add_comm]
    gcongr
    match 2 * m + 3 - k, le1 with
    | 0, _ => rw [Gene.ofRank_zero, map_zero]; decide
    | 1, _ =>
      cases ε
      · rw [signature_ofRank_nonPolarized]; decide +kernel
      · rw [signature_ofRank_one_positive]; decide
      · rw [signature_ofRank_one_negative]; decide
  · have eq1 : 2 * m + 3 - k = 2 * m + 1 - k + 2 := by omega
    have eq2 : 2 * n + 5 - k = 2 * n + 3 - k + 2 := by omega
    rw [eq1, eq2, signature_ofRank_add_two_add]

end type8_isMutation

end MixLambdaPi

end Aux

section MixDefs

open Variety

namespace MixLambdaPi

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

section type8

noncomputable def X8 : Mix (Lambda, Pi) := by
  have _ := h_le
  refine ⟨Gene.ofRank (2 * m + 3) ε + Gene.ofRank (2 * n + 3) ε, ?_⟩
  rw [mem_Mix_iff, map_add, map_add,
    evenPart_ofRank_odd (k := 2 * m + 3)
      (by rw [Nat.not_even_iff_odd]; exact ⟨m + 1, by ring⟩),
    evenPart_ofRank_odd (k := 2 * n + 3)
      (by rw [Nat.not_even_iff_odd]; exact ⟨n + 1, by ring⟩),
    oddPart_ofRank_odd (k := 2 * m + 3) (by omega)
      (by rw [Nat.not_even_iff_odd]; exact ⟨m + 1, by ring⟩),
    oddPart_ofRank_odd (k := 2 * n + 3) (by omega)
      (by rw [Nat.not_even_iff_odd]; exact ⟨n + 1, by ring⟩),
    zero_add]
  refine ⟨zero_mem _, ?_⟩
  rw [mem_Pi_iff_add, mem_Pi_iff, mem_Pi_iff,
    IsPolarized_ofRank (k := 2 * m + 3) (by omega),
    IsPolarized_ofRank (k := 2 * n + 3) (by omega)]
  exact ⟨hε, hε⟩

lemma X8_eq : (X8 h_le hε).1 =
  Gene.ofRank (2 * m + 3) ε + Gene.ofRank (2 * n + 3) ε := rfl

@[simp] lemma neg_X8 :
    - (X8 h_le hε) = X8 h_le (GeneType.neg_ne_nonPolarized_iff.1 hε) := by
  apply Subtype.ext
  rw [Mix.Lambda_Pi_neg_val, X8_eq, X8_eq, Chromosome.neg_add, neg_ofRank, neg_ofRank]

noncomputable def Y8 : Mix (Lambda, Pi) := by
  have _ := h_le
  refine ⟨Gene.ofRank (2 * m + 1) ε + Gene.ofRank (2 * n + 5) ε, ?_⟩
  rw [mem_Mix_iff, map_add, map_add,
    evenPart_ofRank_odd (k := 2 * m + 1)
      (by rw [Nat.not_even_iff_odd]; exact ⟨m, rfl⟩),
    evenPart_ofRank_odd (k := 2 * n + 5)
      (by rw [Nat.not_even_iff_odd]; exact ⟨n + 2, by ring⟩),
    oddPart_ofRank_odd (k := 2 * m + 1) (by omega)
      (by rw [Nat.not_even_iff_odd]; exact ⟨m, rfl⟩),
    oddPart_ofRank_odd (k := 2 * n + 5) (by omega)
      (by rw [Nat.not_even_iff_odd]; exact ⟨n + 2, by ring⟩),
    zero_add]
  refine ⟨zero_mem _, ?_⟩
  rw [mem_Pi_iff_add, mem_Pi_iff, mem_Pi_iff,
    IsPolarized_ofRank (k := 2 * m + 1) (by omega),
    IsPolarized_ofRank (k := 2 * n + 5) (by omega)]
  exact ⟨hε, hε⟩

lemma Y8_eq : (Y8 h_le hε).1 =
  Gene.ofRank (2 * m + 1) ε + Gene.ofRank (2 * n + 5) ε := rfl

@[simp] lemma neg_Y8 :
    - (Y8 h_le hε) = Y8 h_le (GeneType.neg_ne_nonPolarized_iff.1 hε) := by
  apply Subtype.ext
  rw [Mix.Lambda_Pi_neg_val, Y8_eq, Y8_eq, Chromosome.neg_add, neg_ofRank, neg_ofRank]

end type8

end MixLambdaPi

end MixDefs
