import YoungDiagram.Variety

open Chromosome Pointwise

variable {ε ε' : GeneType} {m n : ℕ}

-- Φ = (Π, 2 • Λ): g ranks odd, g^ε ranks even. Equation (8.10):
-- g^ε(m) + g^{ε'}(n) → g^ε(m-2) + g^{ε'}(n+2) with 1 < m ≤ n, m = 2m'+2, n = 2n'+2.

local notation "type10X" =>
  Gene.ofRank (2 * m + 2) ε +
  Gene.ofRank (2 * n + 2) ε'
local notation "type10Y" =>
  Gene.ofRank (2 * m) ε +
  Gene.ofRank (2 * n + 4) ε'

variable (h_le : m ≤ n)

include h_le

section Aux

namespace MixPi2Lambda

section type10_isMutation

lemma mutation_type10_ne : type10X ≠ type10Y := by
  intro h
  replace h := congr_arg (· ⟨2 * n + 4, ε', by omega⟩) h
  have h_m : 2 * m + 2 ≠ 0 := by omega
  have h_n : 2 * n + 2 ≠ 0 := by omega
  have h_n' : 2 * n + 4 ≠ 0 := by omega
  simp only [Gene.ofRank_def, h_m, h_n, h_n', ↓reduceDIte, Finsupp.coe_add,
    Pi.add_apply, Finsupp.single_eq_same, Finsupp.single_apply, Gene.mk.injEq,
    Nat.reduceEqDiff, Nat.add_left_cancel_iff, and_true] at h
  rcases eq_or_ne (2 * m) 0 with hm0 | hm0
  · rw [dif_pos hm0] at h
    simp at h
    omega
  · rw [dif_neg hm0, Finsupp.single_apply] at h
    simp only [Gene.mk.injEq] at h
    split_ifs at h <;> omega

lemma mutation_type10_iterate_signature_eq (i k : ℕ) (hi : i ≤ k) :
    (prime^[i] (Gene.ofRank (2 * m + 2 + k) ε +
      Gene.ofRank (2 * n + 2 + k) ε')).signature =
    (prime^[i] (Gene.ofRank (2 * m + k) ε +
      Gene.ofRank (2 * n + 4 + k) ε')).signature := by
  have eq1 : 2 * m + 2 + k - i = 2 * m + k - i + 2 := by omega
  have eq2 : 2 * n + 4 + k - i = 2 * n + 2 + k - i + 2 := by omega
  rw [iterate_map_add, iterate_map_add, prime_iterate_ofRank, prime_iterate_ofRank,
    prime_iterate_ofRank, prime_iterate_ofRank, map_add, map_add, eq1, eq2,
    signature_ofRank_eq₂', signature_ofRank_eq₂']
  ac_rfl

lemma mutation_type10_signature_eq :
    signature type10X = signature type10Y := by
  have := mutation_type10_iterate_signature_eq (ε := ε) (ε' := ε') h_le 0 0 le_rfl
  rwa [Function.iterate_zero_apply, Function.iterate_zero_apply, add_zero, add_zero] at this

lemma mutation_type10_le : type10X ≤ type10Y := by
  intro k
  simp only [iterate_map_add, map_add, prime_iterate_ofRank]
  by_cases hk1 : 2 * n + 2 < k
  · have eq1 : 2 * m + 2 - k = 0 := by omega
    have eq2 : 2 * m - k = 0 := by omega
    have eq3 : 2 * n + 2 - k = 0 := by omega
    rw [eq1, eq2, eq3, Gene.ofRank_zero, map_zero, zero_add, zero_add]
    exact signature_nonneg _
  by_cases hk2 : 2 * m < k
  · have eq1 : 2 * n + 4 - k - 2 = 2 * n + 2 - k := by omega
    have le1 : 2 * m + 2 - k < 2 := by omega
    rw [Nat.sub_eq_zero_of_le hk2.le, Gene.ofRank_zero, map_zero, zero_add,
      signature_ofRank_eq₂ (k := 2 * n + 4 - k) (by omega), eq1, add_comm]
    gcongr
    match 2 * m + 2 - k, le1 with
    | 0, _ => rw [Gene.ofRank_zero, map_zero]; decide
    | 1, _ =>
      cases ε
      · rw [signature_ofRank_nonPolarized]; decide +kernel
      · rw [signature_ofRank_one_positive]; decide
      · rw [signature_ofRank_one_negative]; decide
  · have eq1 : 2 * m + 2 - k = 2 * m - k + 2 := by omega
    have eq2 : 2 * n + 4 - k = 2 * n + 2 - k + 2 := by omega
    rw [eq1, eq2, signature_ofRank_eq₂', signature_ofRank_eq₂']
    rw [show (Gene.ofRank (2 * m - k) ε).signature + (1, 1) +
        (Gene.ofRank (2 * n + 2 - k) ε').signature =
        (Gene.ofRank (2 * m - k) ε).signature +
        ((Gene.ofRank (2 * n + 2 - k) ε').signature + (1, 1)) from by ac_rfl]

end type10_isMutation

end MixPi2Lambda

end Aux

section MixDefs

open Variety

namespace MixPi2Lambda

variable (hε : ε ≠ .NonPolarized) (hε' : ε' ≠ .NonPolarized)

section type10

noncomputable def X10 : Mix (Pi, 2 • Lambda) := by
  have _ := h_le
  refine ⟨Gene.ofRank (2 * m + 2) ε + Gene.ofRank (2 * n + 2) ε', ?_⟩
  rw [mem_Mix_iff, map_add, map_add,
    evenPart_ofRank, if_pos (by grind),
    evenPart_ofRank, if_pos (by grind),
    oddPart_ofRank, if_pos (by grind),
    oddPart_ofRank, if_pos (by grind),
    add_zero]
  refine ⟨?_, zero_mem _⟩
  rw [mem_Pi_iff_add, mem_Pi_iff, mem_Pi_iff,
    IsPolarized_ofRank (k := 2 * m + 2) (by omega),
    IsPolarized_ofRank (k := 2 * n + 2) (by omega)]
  exact ⟨hε, hε'⟩

lemma X10_eq : (X10 h_le hε hε').1 =
  Gene.ofRank (2 * m + 2) ε + Gene.ofRank (2 * n + 2) ε' := rfl

@[simp] lemma neg_X10 :
    - (X10 h_le hε hε') =
      X10 h_le (GeneType.neg_ne_nonPolarized_iff.1 hε)
        (GeneType.neg_ne_nonPolarized_iff.1 hε') := by
  apply Subtype.ext
  rw [Mix.Pi_2Lambda_neg_val, X10_eq, X10_eq, Chromosome.neg_add, neg_ofRank, neg_ofRank]

noncomputable def Y10 : Mix (Pi, 2 • Lambda) := by
  have _ := h_le
  have _ := hε
  have _ := hε'
  refine ⟨Gene.ofRank (2 * m) ε + Gene.ofRank (2 * n + 4) ε', ?_⟩
  rw [mem_Mix_iff, map_add, map_add,
    evenPart_ofRank, if_pos (by grind), oddPart_ofRank, if_pos (by grind),
    evenPart_ofRank, if_pos (by grind), oddPart_ofRank, if_pos (by grind),
    add_zero]
  match m with
  | 0 =>
    rw [Nat.mul_zero, Gene.ofRank_zero, zero_add]
    refine ⟨?_, zero_mem _⟩
    rw [mem_Pi_iff, IsPolarized_ofRank (k := 2 * n + 4) (by omega)]
    exact hε'
  | m + 1 =>
    refine ⟨?_, zero_mem _⟩
    rw [mem_Pi_iff_add, mem_Pi_iff, mem_Pi_iff,
      IsPolarized_ofRank (k := 2 * (m + 1)) (by omega),
      IsPolarized_ofRank (k := 2 * n + 4) (by omega)]
    exact ⟨hε, hε'⟩

lemma Y10_eq : (Y10 h_le hε hε').1 =
  Gene.ofRank (2 * m) ε + Gene.ofRank (2 * n + 4) ε' := rfl

@[simp] lemma neg_Y10 :
    - (Y10 h_le hε hε') =
      Y10 h_le (GeneType.neg_ne_nonPolarized_iff.1 hε)
        (GeneType.neg_ne_nonPolarized_iff.1 hε') := by
  apply Subtype.ext
  rw [Mix.Pi_2Lambda_neg_val, Y10_eq, Y10_eq, Chromosome.neg_add, neg_ofRank, neg_ofRank]

end type10

end MixPi2Lambda

end MixDefs
