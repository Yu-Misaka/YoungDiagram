import YoungDiagram.Variety

open Chromosome Pointwise

variable {ε : GeneType} {k : ℕ}

-- Φ = (Π, 2 • Λ): g ranks odd, g^ε ranks even. Equation (8.9):
-- 2 g(m) → g^ε(m-1) + g^{-ε}(m+1) with m = 2k+1 odd.

local notation "type9X" =>
  Gene.ofRank (2 * k + 1) GeneType.NonPolarized +
  Gene.ofRank (2 * k + 1) GeneType.NonPolarized
local notation "type9Y" =>
  Gene.ofRank (2 * k) ε +
  Gene.ofRank (2 * k + 2) (- ε)

section Aux

namespace MixPi2Lambda

section type9_isMutation

lemma mutation_type9_ne : type9X ≠ type9Y := by
  intro h
  replace h := congr_arg (· ⟨2 * k + 2, - ε, by omega⟩) h
  have h1 : 2 * k + 1 ≠ 0 := by omega
  have h2 : 2 * k + 2 ≠ 0 := by omega
  simp only [Gene.ofRank_def, h1, h2, ↓reduceDIte, Finsupp.coe_add, Pi.add_apply,
    Finsupp.single_eq_same, Finsupp.single_apply, Gene.mk.injEq, Nat.reduceEqDiff,
    Nat.add_left_cancel_iff, false_and] at h
  rcases eq_or_ne (2 * k) 0 with hk0 | hk0
  · rw [dif_pos hk0] at h
    simp at h
  · rw [dif_neg hk0, Finsupp.single_apply] at h
    simp only [Gene.mk.injEq] at h
    split_ifs at h <;> omega

lemma mutation_type9_iterate_signature_eq (i j : ℕ) (hi : i ≤ j) :
    (prime^[i] (Gene.ofRank (2 * k + 1 + j) .NonPolarized +
      Gene.ofRank (2 * k + 1 + j) .NonPolarized)).signature =
    (prime^[i] (Gene.ofRank (2 * k + j) ε +
      Gene.ofRank (2 * k + 2 + j) (- ε))).signature := by
  have le1 : i ≤ 2 * k + j := by omega
  have le2 : i ≤ 2 * k + 1 + j := by omega
  have eq1 : 2 * k + 2 + j - i - 2 = 2 * k + j - i := by omega
  simp only [iterate_map_add, prime_iterate_ofRank, map_add,
    signature_ofRank_nonPolarized]
  rw [signature_ofRank_eq₂ (k := 2 * k + 2 + j - i) (by omega), ← add_assoc,
    signature_ofRank_sum_even, Prod.mk_add_mk, ← add_div]
  · simp only [Nat.cast_add, Nat.cast_sub le2, Nat.cast_mul, Nat.cast_ofNat, eq1,
      Nat.cast_sub le1, Nat.cast_one, Prod.mk_add_mk, Prod.mk.injEq, and_self]
    ring
  · grind only [= Nat.even_iff]

lemma mutation_type9_signature_eq :
    signature type9X = signature type9Y := by
  have := mutation_type9_iterate_signature_eq (ε := ε) (k := k) 0 0 le_rfl
  rwa [Function.iterate_zero_apply, Function.iterate_zero_apply, add_zero, add_zero] at this

lemma mutation_type9_le : type9X ≤ type9Y := by
  intro i
  simp only [iterate_map_add, map_add, prime_iterate_ofRank, signature_ofRank_nonPolarized]
  by_cases hle1 : i ≤ 2 * k
  · have le1 : i ≤ 2 * k + 1 := by omega
    have le2 : i ≤ 2 * k + 2 := by omega
    rw [signature_ofRank_sum_even, Prod.mk_add_mk, ← add_div, Nat.cast_sub le1,
      Nat.cast_sub hle1, Nat.cast_sub le2]
    · simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one,
        Prod.mk_le_mk, and_self, ge_iff_le]; linarith only []
    · grind only [= Nat.even_iff]
  · by_cases hle2 : i ≤ 2 * k + 2
    · have eq1 : 2 * k + 1 - i = 0 := by omega
      have eq2 : 2 * k - i = 0 := by omega
      rw [eq1, eq2, Nat.cast_zero, zero_div, Gene.ofRank_zero, map_zero,
        ← Prod.zero_eq_mk, zero_add, zero_add]
      by_cases heq1 : i = 2 * k + 2
      · simp only [heq1, le_refl, tsub_self, Gene.ofRank_zero, map_zero]
      · have heq2 : i = 2 * k + 1 := by omega
        rw [heq2]
        have heq3 : 2 * k + 2 - (2 * k + 1) = 1 := by omega
        rw [heq3]
        match ε with
        | .NonPolarized =>
          rw [GeneType.neg_nonPolarized, signature_ofRank_nonPolarized,
            Nat.cast_one, Prod.mk_le_mk]
          refine ⟨?_, ?_⟩ <;> positivity
        | .Positive => rw [GeneType.neg_positive, signature_ofRank_one_negative]; decide
        | .Negative => rw [GeneType.neg_negative, signature_ofRank_one_positive]; decide
    · have eq1 : 2 * k + 1 - i = 0 := by omega
      have eq2 : 2 * k - i = 0 := by omega
      have eq3 : 2 * k + 2 - i = 0 := by omega
      rw [eq1, eq2, eq3, Gene.ofRank_zero, Gene.ofRank_zero, map_zero,
        Nat.cast_zero, zero_div]; rfl

end type9_isMutation

end MixPi2Lambda

end Aux

section MixDefs

open Variety

namespace MixPi2Lambda

variable (hε : ε ≠ .NonPolarized)

section type9

noncomputable def X9 (k : ℕ) : Mix (Pi, 2 • Lambda) := by
  refine ⟨Gene.ofRank (2 * k + 1) GeneType.NonPolarized +
    Gene.ofRank (2 * k + 1) GeneType.NonPolarized, ?_⟩
  rw [mem_Mix_iff, map_add, map_add,
    evenPart_ofRank, if_neg (by grind),
    oddPart_ofRank, if_neg (by grind),
    zero_add]
  refine ⟨zero_mem _, ?_⟩
  rw [AddSubmonoid.mem_smul_pointwise_iff_exists]
  refine ⟨Gene.ofRank (2 * k + 1) GeneType.NonPolarized, ?_, ?_⟩
  · rw [mem_Lambda_iff, IsNonPolarized_ofRank (k := 2 * k + 1) (by omega)]
  · rw [two_smul]

lemma X9_eq : (X9 k).1 =
  Gene.ofRank (2 * k + 1) GeneType.NonPolarized +
  Gene.ofRank (2 * k + 1) GeneType.NonPolarized := rfl

@[simp] lemma neg_X9 : - (X9 k) = X9 k := by
  apply Subtype.ext
  rw [Mix.Pi_2Lambda_neg_val, X9_eq, Chromosome.neg_add, neg_ofRank,
    GeneType.neg_nonPolarized]

noncomputable def Y9 (k : ℕ) : Mix (Pi, 2 • Lambda) := by
  refine ⟨Gene.ofRank (2 * k) ε + Gene.ofRank (2 * k + 2) (- ε), ?_⟩
  rw [mem_Mix_iff, map_add, map_add, evenPart_ofRank, if_pos (by grind),
    oddPart_ofRank, if_pos (by grind), evenPart_ofRank, if_pos (by grind),
    oddPart_ofRank, if_pos (by grind), add_zero]
  match k with
  | 0 =>
    rw [Nat.mul_zero, Gene.ofRank_zero, zero_add]
    refine ⟨?_, zero_mem _⟩
    rw [mem_Pi_iff, IsPolarized_ofRank (k := 2 * 0 + 2) (by omega)]
    rwa [ne_eq, ← GeneType.neg_eq_nonPolarized_iff]
  | k + 1 =>
    refine ⟨?_, zero_mem _⟩
    rw [mem_Pi_iff_add, mem_Pi_iff, mem_Pi_iff,
      IsPolarized_ofRank (k := 2 * (k + 1)) (by omega),
      IsPolarized_ofRank (k := 2 * (k + 1) + 2) (by omega)]
    exact ⟨hε, by rwa [ne_eq, ← GeneType.neg_eq_nonPolarized_iff]⟩

lemma Y9_eq : (Y9 hε k).1 =
  Gene.ofRank (2 * k) ε +
  Gene.ofRank (2 * k + 2) (- ε) := rfl

@[simp] lemma neg_Y9 :
    - (Y9 hε k) = Y9 (GeneType.neg_ne_nonPolarized_iff.1 hε) k := by
  apply Subtype.ext
  rw [Mix.Pi_2Lambda_neg_val, Y9_eq, Y9_eq, Chromosome.neg_add, neg_ofRank, neg_ofRank]

end type9

end MixPi2Lambda

end MixDefs
