import YoungDiagram.Variety

open Chromosome Pointwise

variable {ε ε' : GeneType} {m n : ℕ}

-- Φ = (Π, 2 • Λ): g ranks odd, g^ε ranks even. Equation (8.15):
-- g^ε(m) + g^{-ε}(n) → g^{-ε}(m-2) + g^ε(n+2) with 1 < m ≤ n,
-- m = 2m'+2, n = 2n'+2.

local notation "type15X" =>
  Gene.ofRank (2 * m + 2) ε +
  Gene.ofRank (2 * n + 2) (- ε)
local notation "type15Y" =>
  Gene.ofRank (2 * m) (- ε) +
  Gene.ofRank (2 * n + 4) ε

variable (h_le : m ≤ n)

include h_le

section Aux

namespace MixPi2Lambda

section type15_isMutation

lemma mutation_type15_ne : type15X ≠ type15Y := by
  intro h
  replace h := congr_arg (· ⟨2 * m + 2, ε, by omega⟩) h
  have h_m : 2 * m + 2 ≠ 0 := by omega
  have h_n : 2 * n + 2 ≠ 0 := by omega
  have h_n' : 2 * n + 4 ≠ 0 := by omega
  simp only [Gene.ofRank_def, h_m, h_n, h_n', ↓reduceDIte, Finsupp.coe_add,
    Pi.add_apply, Finsupp.single_eq_same, Finsupp.single_apply, Gene.mk.injEq,
    Nat.reduceEqDiff, and_true] at h
  rcases eq_or_ne (2 * m) 0 with hm0 | hm0
  · rw [dif_pos hm0] at h
    simp at h
    split_ifs at h <;> omega
  · rw [dif_neg hm0, Finsupp.single_apply] at h
    simp only [Gene.mk.injEq] at h
    split_ifs at h <;> omega

omit h_le in
private lemma signature_ofRank_add_two_mul (a d : ℕ) (ε : GeneType) :
    (Gene.ofRank (a + 2 * d) ε).signature =
      (Gene.ofRank a ε).signature + ((d : ℚ), (d : ℚ)) := by
  induction d with
  | zero => simp
  | succ d ih =>
    have heq : a + 2 * (d + 1) = (a + 2 * d) + 2 := by ring
    rw [heq, signature_ofRank_eq₂', ih]
    push_cast
    rw [Prod.mk_add_mk, Prod.mk_add_mk]
    congr 1 <;> ring

omit h_le in
private lemma neg_signature_sum_fst (k : ℕ) (ε : GeneType) :
    (Gene.ofRank k ε).signature.1 +
      (Gene.ofRank k (-ε)).signature.1 = (k : ℚ) := by
  have h := signature_sum_ofRank_neg_eq_rank (k := k) (ε := ε)
  have := congr_arg Prod.fst h; simpa using this

omit h_le in
private lemma neg_signature_sum_snd (k : ℕ) (ε : GeneType) :
    (Gene.ofRank k ε).signature.2 +
      (Gene.ofRank k (-ε)).signature.2 = (k : ℚ) := by
  have h := signature_sum_ofRank_neg_eq_rank (k := k) (ε := ε)
  have := congr_arg Prod.snd h; simpa using this

omit h_le in
private lemma sig_bound_fst (k : ℕ) (ε : GeneType) :
    ((k : ℚ) - 1) / 2 ≤ (Gene.ofRank k ε).signature.1 ∧
    (Gene.ofRank k ε).signature.1 ≤ ((k : ℚ) + 1) / 2 :=
  ⟨signature_ofRank_ge.1, signature_ofRank_le.1⟩

omit h_le in
private lemma sig_bound_snd (k : ℕ) (ε : GeneType) :
    ((k : ℚ) - 1) / 2 ≤ (Gene.ofRank k ε).signature.2 ∧
    (Gene.ofRank k ε).signature.2 ≤ ((k : ℚ) + 1) / 2 :=
  ⟨signature_ofRank_ge.2, signature_ofRank_le.2⟩

lemma mutation_type15_iterate_signature_eq (i k : ℕ) (hi : i ≤ k) :
    (prime^[i] (Gene.ofRank (2 * m + 2 + k) ε +
      Gene.ofRank (2 * n + 2 + k) (- ε))).signature =
    (prime^[i] (Gene.ofRank (2 * m + k) (- ε) +
      Gene.ofRank (2 * n + 4 + k) ε)).signature := by
  simp only [iterate_map_add, map_add, prime_iterate_ofRank]
  set a := 2 * m + k - i with ha
  have eq1 : 2 * m + 2 + k - i = a + 2 * 1 := by omega
  have eq2 : 2 * n + 2 + k - i = a + 2 * (n - m + 1) := by omega
  have eq3 : 2 * n + 4 + k - i = a + 2 * (n - m + 2) := by omega
  rw [eq1, eq2, eq3, signature_ofRank_add_two_mul, signature_ofRank_add_two_mul,
    signature_ofRank_add_two_mul]
  have hsum_a_fst := neg_signature_sum_fst a ε
  have hsum_a_snd := neg_signature_sum_snd a ε
  ext
  · simp only [Prod.fst_add]; push_cast; linarith
  · simp only [Prod.snd_add]; push_cast; linarith

lemma mutation_type15_signature_eq :
    signature type15X = signature type15Y := by
  have := mutation_type15_iterate_signature_eq (ε := ε) h_le 0 0 le_rfl
  rwa [Function.iterate_zero_apply, Function.iterate_zero_apply, add_zero, add_zero] at this

lemma mutation_type15_le : type15X ≤ type15Y := by
  intro k
  simp only [iterate_map_add, map_add, prime_iterate_ofRank]
  by_cases hk1 : 2 * n + 2 < k
  · have eq1 : 2 * m + 2 - k = 0 := by omega
    have eq2 : 2 * m - k = 0 := by omega
    have eq3 : 2 * n + 2 - k = 0 := by omega
    simp only [eq1, eq2, eq3, Gene.ofRank_zero, map_zero, zero_add, add_zero]
    exact signature_nonneg _
  by_cases hk2 : 2 * m < k
  · -- k > 2m, so 2m-k = 0 in nat. 2m+2-k ∈ {0, 1}.
    have heq_m : 2 * m - k = 0 := by omega
    have hk2n : k ≤ 2 * n + 2 := by omega
    rw [heq_m, Gene.ofRank_zero, map_zero, zero_add]
    -- Subcase on 2*m+2-k ∈ {0, 1}
    have hc_cases : 2 * m + 2 - k = 0 ∨ 2 * m + 2 - k = 1 := by omega
    rcases hc_cases with hc | hc
    · -- c = 0: k ≥ 2m+2.
      rw [hc, Gene.ofRank_zero, map_zero, zero_add]
      -- Now goal: sig(2n+2-k, -ε) ≤ sig(2n+4-k, ε)
      have eq_b5 : 2 * n + 4 - k = (2 * n + 2 - k) + 2 := by omega
      rw [eq_b5, signature_ofRank_eq₂']
      set b := 2 * n + 2 - k
      have hsum_fst := neg_signature_sum_fst b ε
      have hsum_snd := neg_signature_sum_snd b ε
      have hbound_fst := sig_bound_fst b ε
      have hbound_snd := sig_bound_snd b ε
      refine ⟨?_, ?_⟩
      · simp only [Prod.fst_add]; linarith [hbound_fst.1]
      · simp only [Prod.snd_add]; linarith [hbound_snd.1]
    · -- c = 1: k = 2m+1.
      have hk_eq : k = 2 * m + 1 := by omega
      have eq_b : 2 * n + 2 - k = 1 + 2 * (n - m) := by omega
      have eq_b5 : 2 * n + 4 - k = 1 + 2 * (n - m + 1) := by omega
      rw [hc, eq_b, eq_b5, signature_ofRank_add_two_mul,
        signature_ofRank_add_two_mul]
      have hsum_fst := neg_signature_sum_fst 1 ε
      have hsum_snd := neg_signature_sum_snd 1 ε
      have hsig_nn := signature_nonneg (Gene.ofRank 1 ε)
      have hsig_neg_nn := signature_nonneg (Gene.ofRank 1 (-ε))
      have hsig_nn1 : (0 : ℚ) ≤ (Gene.ofRank 1 ε).signature.1 := hsig_nn.1
      have hsig_nn2 : (0 : ℚ) ≤ (Gene.ofRank 1 ε).signature.2 := hsig_nn.2
      have hsig_neg_nn1 : (0 : ℚ) ≤ (Gene.ofRank 1 (-ε)).signature.1 := hsig_neg_nn.1
      have hsig_neg_nn2 : (0 : ℚ) ≤ (Gene.ofRank 1 (-ε)).signature.2 := hsig_neg_nn.2
      refine ⟨?_, ?_⟩
      · simp only [Prod.fst_add]; push_cast; push_cast at hsum_fst
        linarith
      · simp only [Prod.snd_add]; push_cast; push_cast at hsum_snd
        linarith
  · -- k ≤ 2m, so all four ranks are non-negative.
    set a := 2 * m - k with ha_def
    have eq1 : 2 * m + 2 - k = a + 2 * 1 := by omega
    have eq2 : 2 * n + 2 - k = a + 2 * (n - m + 1) := by omega
    have eq3 : 2 * n + 4 - k = a + 2 * (n - m + 2) := by omega
    rw [eq1, eq2, eq3, signature_ofRank_add_two_mul, signature_ofRank_add_two_mul,
      signature_ofRank_add_two_mul]
    have hsum_a_fst := neg_signature_sum_fst a ε
    have hsum_a_snd := neg_signature_sum_snd a ε
    refine ⟨?_, ?_⟩
    · simp only [Prod.fst_add]; push_cast; linarith
    · simp only [Prod.snd_add]; push_cast; linarith

end type15_isMutation

end MixPi2Lambda

end Aux

section MixDefs

open Variety

namespace MixPi2Lambda

variable (hε : ε ≠ .NonPolarized)

section type15

noncomputable def X15 : Mix (Pi, 2 • Lambda) := by
  have _ := h_le
  refine ⟨Gene.ofRank (2 * m + 2) ε + Gene.ofRank (2 * n + 2) (- ε), ?_⟩
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
  exact ⟨hε, by rwa [ne_eq, ← GeneType.neg_eq_nonPolarized_iff]⟩

lemma X15_eq : (X15 h_le hε).1 =
  Gene.ofRank (2 * m + 2) ε + Gene.ofRank (2 * n + 2) (- ε) := rfl

@[simp] lemma neg_X15 :
    - (X15 h_le hε) = X15 h_le (GeneType.neg_ne_nonPolarized_iff.1 hε) := by
  apply Subtype.ext
  rw [Mix.Pi_2Lambda_neg_val, X15_eq, X15_eq, Chromosome.neg_add, neg_ofRank, neg_ofRank,
    neg_neg]

noncomputable def Y15 : Mix (Pi, 2 • Lambda) := by
  have _ := h_le
  have _ := hε
  refine ⟨Gene.ofRank (2 * m) (- ε) + Gene.ofRank (2 * n + 4) ε, ?_⟩
  rw [mem_Mix_iff, map_add, map_add, evenPart_ofRank, if_pos (by grind),
    oddPart_ofRank, if_pos (by grind), evenPart_ofRank, if_pos (by grind),
    oddPart_ofRank, if_pos (by grind), add_zero]
  match m with
  | 0 =>
    rw [Nat.mul_zero, Gene.ofRank_zero, zero_add]
    refine ⟨?_, zero_mem _⟩
    rw [mem_Pi_iff, IsPolarized_ofRank (k := 2 * n + 4) (by omega)]
    exact hε
  | m + 1 =>
    refine ⟨?_, zero_mem _⟩
    rw [mem_Pi_iff_add, mem_Pi_iff, mem_Pi_iff,
      IsPolarized_ofRank (k := 2 * (m + 1)) (by omega),
      IsPolarized_ofRank (k := 2 * n + 4) (by omega)]
    exact ⟨by rwa [ne_eq, ← GeneType.neg_eq_nonPolarized_iff], hε⟩

lemma Y15_eq : (Y15 h_le hε).1 =
  Gene.ofRank (2 * m) (- ε) + Gene.ofRank (2 * n + 4) ε := rfl

@[simp] lemma neg_Y15 :
    - (Y15 h_le hε) = Y15 h_le (GeneType.neg_ne_nonPolarized_iff.1 hε) := by
  apply Subtype.ext
  rw [Mix.Pi_2Lambda_neg_val, Y15_eq, Y15_eq, Chromosome.neg_add, neg_ofRank, neg_ofRank,
    neg_neg]

end type15

end MixPi2Lambda

end MixDefs
