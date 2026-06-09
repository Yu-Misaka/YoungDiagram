import YoungDiagram.Variety

open Chromosome

variable {ε : GeneType} {m n : ℕ}

-- Φ = (Λ, Π): g ranks even, g^ε ranks odd.

local notation "type4X" =>
  Gene.ofRank (2 * m + 2) GeneType.NonPolarized +
  Gene.ofRank (2 * n + 2) GeneType.NonPolarized
local notation "type4Y" =>
  Gene.ofRank (2 * m + 1) ε +
  Gene.ofRank (2 * n + 3) (- ε)

variable (h_le : m ≤ n)

include h_le

section Aux

namespace MixLambdaPi

section type4_isMutation

omit h_le in
lemma mutation_type4_ne : type4X ≠ type4Y := by
  intro h
  replace h := congr_arg (· ⟨2 * m + 2, .NonPolarized, by omega⟩) h
  have h_n : 2 * n + 2 ≠ 0 := by omega
  have h_m : 2 * m + 2 ≠ 0 := by omega
  simp only [Gene.ofRank_def, h_m, ↓reduceDIte, h_n, Finsupp.coe_add, Pi.add_apply,
    Finsupp.single_eq_same, Nat.add_eq_zero_iff, one_ne_zero, and_false] at h
  rw [dif_neg (by omega), Finsupp.single_apply] at h
  split_ifs at h <;> (simp [Finsupp.single_apply] at h; grind)

lemma mutation_type4_iterate_signature_eq (i k : ℕ) (hi : i ≤ k) :
    (prime^[i] (Gene.ofRank (2 * m + 2 + k) .NonPolarized +
      Gene.ofRank (2 * n + 2 + k) .NonPolarized)).signature =
    (prime^[i] (Gene.ofRank (2 * m + 1 + k) ε + Gene.ofRank (2 * n + 3 + k) (- ε))).signature := by
  have le1 : i ≤ 2 * n + 1 + k := by omega
  have le2 : i ≤ 2 * m + 1 + k := by omega
  have le3 : i ≤ 2 * m + 2 + k := by omega
  have eq1 : 2 * n + 3 + k - i - 2 = 2 * n + 1 + k - i := by omega
  have le4 : i ≤ 2 * n + 2 + k := by omega
  rw [iterate_map_add, iterate_map_add, prime_iterate_ofRank, prime_iterate_ofRank,
    prime_iterate_ofRank, prime_iterate_ofRank, map_add, map_add,
    signature_ofRank_nonPolarized, signature_ofRank_nonPolarized,
    signature_ofRank_eq₂ (k := 2 * n + 3 + k - i) (by omega), ← add_assoc,
    signature_ofRank_sum_even, Prod.mk_add_mk, ← add_div]
  · simp only [Nat.cast_add, Nat.cast_sub le3, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub le4, eq1,
    Nat.cast_sub le2, Nat.cast_one, Nat.cast_sub le1, Prod.mk_add_mk, Prod.mk.injEq, and_self]
    ring
  · grind only [= Nat.even_iff]

lemma mutation_type4_signature_eq :
    signature type4X = signature type4Y := by
  have := mutation_type4_iterate_signature_eq (ε := ε) h_le 0 0 le_rfl
  rwa [Function.iterate_zero_apply, Function.iterate_zero_apply, add_zero, add_zero] at this

lemma mutation_type4_le : type4X ≤ type4Y := by
  intro k
  simp only [iterate_map_add, map_add, prime_iterate_ofRank, signature_ofRank_nonPolarized]
  by_cases hle1 : k ≤ 2 * m + 1
  · have le1 : k ≤ 2 * m + 2 := by omega
    have le2 : k ≤ 2 * n + 2 := by omega
    have le3 : k ≤ 2 * n + 3 := by omega
    rw [signature_ofRank_sum_even, Prod.mk_add_mk, ← add_div, Nat.cast_sub le1,
      Nat.cast_sub le2, Nat.cast_sub hle1, Nat.cast_sub le3]
    · simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one,
        Prod.mk_le_mk, and_self, ge_iff_le]; linarith only []
    · grind only [= Nat.even_iff]
  · by_cases hle2 : k ≤ 2 * n + 3
    · have eq1 : 2 * m + 2 - k = 0 := by omega
      have eq2 : 2 * m + 1 - k = 0 := by omega
      rw [eq1, eq2, Nat.cast_zero, zero_div, Gene.ofRank_zero, map_zero,
        ← Prod.zero_eq_mk, zero_add, zero_add]
      by_cases heq1 : k = 2 * n + 3
      · simp only [heq1, add_le_add_iff_left, Nat.reduceLeDiff, Nat.sub_eq_zero_of_le,
        CharP.cast_eq_zero, zero_div, tsub_self, Gene.ofRank_zero, map_zero]
        rfl
      · have le1 : k ≤ 2 * n + 2 := by omega
        convert signature_ofRank_ge
        <;> (simp [Nat.cast_sub le1, Nat.cast_sub hle2]; grind)
    · have eq1 : 2 * m + 2 - k = 0 := by omega
      have eq2 : 2 * m + 1 - k = 0 := by omega
      have eq3 : 2 * n + 3 - k = 0 := by omega
      have eq4 : 2 * n + 2 - k = 0 := by omega
      rw [eq1, eq2, eq3, eq4, Gene.ofRank_zero, Gene.ofRank_zero, map_zero,
        Nat.cast_zero, zero_div]; rfl

end type4_isMutation

end MixLambdaPi

end Aux

section MixDefs

open Variety

namespace MixLambdaPi

variable (hε : ε ≠ .NonPolarized)

include h_le

section type4

noncomputable def X4 : Mix (Lambda, Pi) := by
  have _ := h_le
  refine ⟨Gene.ofRank (2 * m + 2) GeneType.NonPolarized +
    Gene.ofRank (2 * n + 2) GeneType.NonPolarized, ?_⟩
  rw [mem_Mix_iff, map_add, map_add,
    evenPart_ofRank, if_pos (by grind), evenPart_ofRank, if_pos (by grind),
    oddPart_ofRank, if_pos (by grind), oddPart_ofRank, if_pos (by grind)]
  refine ⟨?_, zero_mem _⟩
  rw [mem_Lambda_iff_add, mem_Lambda_iff, mem_Lambda_iff,
    IsNonPolarized_ofRank (by omega),
    IsNonPolarized_ofRank (by omega)]
  exact ⟨rfl, rfl⟩

lemma X4_eq : (X4 h_le).1 =
  Gene.ofRank (2 * m + 2) GeneType.NonPolarized +
  Gene.ofRank (2 * n + 2) GeneType.NonPolarized := rfl

@[simp] lemma neg_X4 : - (X4 h_le) = X4 h_le := by
  apply Subtype.ext
  rw [Mix.Lambda_Pi_neg_val, X4_eq, Chromosome.neg_add, neg_ofRank, neg_ofRank,
    GeneType.neg_nonPolarized]

noncomputable def Y4 : Mix (Lambda, Pi) := by
  have _ := h_le
  refine ⟨Gene.ofRank (2 * m + 1) ε + Gene.ofRank (2 * n + 3) (- ε), ?_⟩
  rw [mem_Mix_iff, map_add, map_add, evenPart_ofRank, if_neg m.not_even_bit1,
    evenPart_ofRank, if_neg (by grind), oddPart_ofRank, if_neg m.not_even_bit1,
    oddPart_ofRank, if_neg (by grind)]
  refine ⟨zero_mem _, ?_⟩
  rw [mem_Pi_iff_add, mem_Pi_iff, mem_Pi_iff,
    IsPolarized_ofRank (k := 2 * m + 1) (by omega),
    IsPolarized_ofRank (k := 2 * n + 3) (by omega)]
  exact ⟨hε, by rwa [ne_eq, ← GeneType.neg_eq_nonPolarized_iff]⟩

lemma Y4_eq : (Y4 h_le hε).1 =
  Gene.ofRank (2 * m + 1) ε +
  Gene.ofRank (2 * n + 3) (- ε) := rfl

@[simp] lemma neg_Y4 :
    - (Y4 h_le hε) = Y4 h_le (GeneType.neg_ne_nonPolarized_iff.1 hε) := by
  apply Subtype.ext
  rw [Mix.Lambda_Pi_neg_val, Y4_eq, Y4_eq, Chromosome.neg_add, neg_ofRank, neg_ofRank]

end type4

end MixLambdaPi

end MixDefs
