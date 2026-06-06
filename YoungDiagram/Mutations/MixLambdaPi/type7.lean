import YoungDiagram.Variety

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

namespace MixLambdaPi

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

section type7

noncomputable def X7 : Mix (Lambda, Pi) := by
  have _ := h_le
  have _ := hε
  refine ⟨Gene.ofRank (2 * m + 1) ε + Gene.ofRank (2 * n + 1) (- ε), ?_⟩
  rw [mem_Mix_iff, map_add, map_add,
    evenPart_ofRank_odd (k := 2 * m + 1)
      (by rw [Nat.not_even_iff_odd]; exact ⟨m, rfl⟩),
    evenPart_ofRank_odd (k := 2 * n + 1)
      (by rw [Nat.not_even_iff_odd]; exact ⟨n, rfl⟩),
    oddPart_ofRank_odd (k := 2 * m + 1) (by omega)
      (by rw [Nat.not_even_iff_odd]; exact ⟨m, rfl⟩),
    oddPart_ofRank_odd (k := 2 * n + 1) (by omega)
      (by rw [Nat.not_even_iff_odd]; exact ⟨n, rfl⟩),
    zero_add]
  refine ⟨zero_mem _, ?_⟩
  rw [mem_Pi_iff_add, mem_Pi_iff, mem_Pi_iff,
    IsPolarized_ofRank (k := 2 * m + 1) (by omega),
    IsPolarized_ofRank (k := 2 * n + 1) (by omega)]
  exact ⟨hε, by rwa [ne_eq, ← GeneType.neg_eq_nonPolarized_iff]⟩

lemma X7_eq : (X7 h_le hε).1 =
  Gene.ofRank (2 * m + 1) ε + Gene.ofRank (2 * n + 1) (- ε) := rfl

@[simp] lemma neg_X7 :
    - (X7 h_le hε) = X7 h_le (GeneType.neg_ne_nonPolarized_iff.1 hε) := by
  apply Subtype.ext
  rw [Mix.Lambda_Pi_neg_val, X7_eq, X7_eq, Chromosome.neg_add, neg_ofRank, neg_ofRank]

noncomputable def Y7 : Mix (Lambda, Pi) := by
  have _ := h_le
  refine ⟨Gene.ofRank (2 * m) GeneType.NonPolarized +
    Gene.ofRank (2 * n + 2) GeneType.NonPolarized, ?_⟩
  rw [mem_Mix_iff, map_add, map_add,
    evenPart_ofRank_even (k := 2 * n + 2) (by omega) ⟨n + 1, by ring⟩,
    oddPart_ofRank_even (k := 2 * n + 2) ⟨n + 1, by ring⟩,
    add_zero]
  match m with
  | 0 =>
    rw [Nat.mul_zero, Gene.ofRank_zero, map_zero, map_zero, zero_add]
    refine ⟨?_, zero_mem _⟩
    rw [mem_Lambda_iff, IsNonPolarized_ofRank (k := 2 * n + 2) (by omega)]
  | m + 1 =>
    rw [evenPart_ofRank_even (k := 2 * (m + 1)) (by omega) ⟨m + 1, by ring⟩,
      oddPart_ofRank_even (k := 2 * (m + 1)) ⟨m + 1, by ring⟩]
    refine ⟨?_, zero_mem _⟩
    rw [mem_Lambda_iff_add, mem_Lambda_iff, mem_Lambda_iff,
      IsNonPolarized_ofRank (k := 2 * (m + 1)) (by omega),
      IsNonPolarized_ofRank (k := 2 * n + 2) (by omega)]
    exact ⟨rfl, rfl⟩

lemma Y7_eq : (Y7 h_le).1 =
  Gene.ofRank (2 * m) GeneType.NonPolarized +
  Gene.ofRank (2 * n + 2) GeneType.NonPolarized := rfl

@[simp] lemma neg_Y7 : - (Y7 h_le) = Y7 h_le := by
  apply Subtype.ext
  rw [Mix.Lambda_Pi_neg_val, Y7_eq, Chromosome.neg_add, neg_ofRank, neg_ofRank,
    GeneType.neg_nonPolarized]

end type7

end MixLambdaPi

end MixDefs
