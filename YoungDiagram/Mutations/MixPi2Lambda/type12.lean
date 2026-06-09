import YoungDiagram.Variety

open Chromosome Pointwise

variable {ε : GeneType} {m n : ℕ}

-- Φ = (Π, 2 • Λ): g ranks odd, g^ε ranks even. Equation (8.12):
-- g^+(m) + g^-(m) + g^ε(n) → 2 g(m-1) + g^ε(n+2) with m ≤ n.
-- Parametrize m_paper = 2*m+2, n_paper = 2*n+2 (both even ≥ 2 for V_4).

local notation "type12X" =>
  Gene.ofRank (2 * m + 2) GeneType.Positive +
  Gene.ofRank (2 * m + 2) GeneType.Negative +
  Gene.ofRank (2 * n + 2) ε
local notation "type12Y" =>
  Gene.ofRank (2 * m + 1) GeneType.NonPolarized +
  Gene.ofRank (2 * m + 1) GeneType.NonPolarized +
  Gene.ofRank (2 * n + 4) ε

variable (h_le : m ≤ n)

include h_le

section Aux

namespace MixPi2Lambda

section type12_isMutation

lemma mutation_type12_ne : type12X ≠ type12Y := by
  intro h
  replace h := congr_arg (· ⟨2 * n + 4, ε, by omega⟩) h
  have h_m : 2 * m + 2 ≠ 0 := by omega
  have h_n : 2 * n + 2 ≠ 0 := by omega
  have h_m' : 2 * m + 1 ≠ 0 := by omega
  have h_n' : 2 * n + 4 ≠ 0 := by omega
  simp only [Gene.ofRank_def, h_m, h_n, h_m', h_n', ↓reduceDIte, Finsupp.coe_add,
    Pi.add_apply, Finsupp.single_eq_same, Finsupp.single_apply, Gene.mk.injEq,
    Nat.reduceEqDiff, Nat.add_left_cancel_iff, and_true] at h
  split_ifs at h <;> omega

omit h_le in
private lemma pos_neg_signature_sum_fst (k : ℕ) :
    (Gene.ofRank k GeneType.Positive).signature.1 +
      (Gene.ofRank k GeneType.Negative).signature.1 = (k : ℚ) := by
  have h := signature_sum_ofRank_neg_eq_rank (k := k) (ε := GeneType.Positive)
  rw [GeneType.neg_positive] at h
  have := congr_arg Prod.fst h; simpa using this

omit h_le in
private lemma pos_neg_signature_sum_snd (k : ℕ) :
    (Gene.ofRank k GeneType.Positive).signature.2 +
      (Gene.ofRank k GeneType.Negative).signature.2 = (k : ℚ) := by
  have h := signature_sum_ofRank_neg_eq_rank (k := k) (ε := GeneType.Positive)
  rw [GeneType.neg_positive] at h
  have := congr_arg Prod.snd h; simpa using this

omit h_le in
private lemma np_signature_fst (k : ℕ) :
    (Gene.ofRank k GeneType.NonPolarized).signature.1 = (k : ℚ) / 2 := by
  rw [signature_ofRank_nonPolarized]

omit h_le in
private lemma np_signature_snd (k : ℕ) :
    (Gene.ofRank k GeneType.NonPolarized).signature.2 = (k : ℚ) / 2 := by
  rw [signature_ofRank_nonPolarized]

lemma mutation_type12_iterate_signature_eq (i k : ℕ) (hi : i ≤ k) :
    (prime^[i] (Gene.ofRank (2 * m + 2 + k) GeneType.Positive +
      Gene.ofRank (2 * m + 2 + k) GeneType.Negative +
      Gene.ofRank (2 * n + 2 + k) ε)).signature =
    (prime^[i] (Gene.ofRank (2 * m + 1 + k) GeneType.NonPolarized +
      Gene.ofRank (2 * m + 1 + k) GeneType.NonPolarized +
      Gene.ofRank (2 * n + 4 + k) ε)).signature := by
  simp only [iterate_map_add, map_add, prime_iterate_ofRank]
  have eq1 : 2 * n + 4 + k - i = 2 * n + 2 + k - i + 2 := by omega
  have eq2 : 2 * m + 2 + k - i = 2 * m + 1 + k - i + 1 := by omega
  rw [eq1, signature_ofRank_eq₂' (2 * n + 2 + k - i), eq2]
  have hPN1 := pos_neg_signature_sum_fst (2 * m + 1 + k - i + 1)
  have hPN2 := pos_neg_signature_sum_snd (2 * m + 1 + k - i + 1)
  have hNP1 := np_signature_fst (2 * m + 1 + k - i)
  have hNP2 := np_signature_snd (2 * m + 1 + k - i)
  ext
  · simp only [Prod.fst_add]; push_cast at *; linarith
  · simp only [Prod.snd_add]; push_cast at *; linarith

lemma mutation_type12_signature_eq :
    signature type12X = signature type12Y := by
  have := mutation_type12_iterate_signature_eq (ε := ε) h_le 0 0 le_rfl
  rwa [Function.iterate_zero_apply, Function.iterate_zero_apply, add_zero, add_zero,
    add_zero, add_zero] at this

lemma mutation_type12_le : type12X ≤ type12Y := by
  intro k
  simp only [iterate_map_add, map_add, prime_iterate_ofRank]
  by_cases hk1 : k ≤ 2 * m + 1
  · have eq1 : 2 * n + 4 - k = 2 * n + 2 - k + 2 := by omega
    have eq2 : 2 * m + 2 - k = 2 * m + 1 - k + 1 := by omega
    rw [eq1, signature_ofRank_eq₂' (2 * n + 2 - k)]
    have hPN1 := pos_neg_signature_sum_fst (2 * m + 2 - k)
    have hPN2 := pos_neg_signature_sum_snd (2 * m + 2 - k)
    have hNP1 := np_signature_fst (2 * m + 1 - k)
    have hNP2 := np_signature_snd (2 * m + 1 - k)
    have hcast1 : ((2 * m + 2 - k : ℕ) : ℚ) = ((2 * m + 1 - k : ℕ) : ℚ) + 1 := by
      rw [eq2]; push_cast; ring
    rw [hcast1] at hPN1 hPN2
    refine ⟨?_, ?_⟩
    · simp only [Prod.fst_add]; linarith
    · simp only [Prod.snd_add]; linarith
  · by_cases hk2 : k ≤ 2 * n + 2
    · have eq1 : 2 * m + 2 - k = 0 := by omega
      have eq2 : 2 * m + 1 - k = 0 := by omega
      have eq3 : 2 * n + 4 - k = 2 * n + 2 - k + 2 := by omega
      rw [eq1, eq2]
      simp only [Gene.ofRank_zero, map_zero, zero_add, add_zero]
      rw [eq3, signature_ofRank_eq₂' (2 * n + 2 - k)]
      refine ⟨?_, ?_⟩
      · simp only [Prod.fst_add]
        linarith [signature_nonneg (Gene.ofRank (2 * n + 2 - k) ε)]
      · simp only [Prod.snd_add]
        linarith [signature_nonneg (Gene.ofRank (2 * n + 2 - k) ε)]
    · by_cases hk3 : k ≤ 2 * n + 4
      · have eq1 : 2 * m + 2 - k = 0 := by omega
        have eq2 : 2 * m + 1 - k = 0 := by omega
        have eq3 : 2 * n + 2 - k = 0 := by omega
        rw [eq1, eq2, eq3]
        simp only [Gene.ofRank_zero, map_zero, zero_add, add_zero]
        exact signature_nonneg _
      · have eq1 : 2 * m + 2 - k = 0 := by omega
        have eq2 : 2 * m + 1 - k = 0 := by omega
        have eq3 : 2 * n + 2 - k = 0 := by omega
        have eq4 : 2 * n + 4 - k = 0 := by omega
        rw [eq1, eq2, eq3, eq4]
        simp only [Gene.ofRank_zero, map_zero, add_zero]
        exact le_refl _

end type12_isMutation

end MixPi2Lambda

end Aux

section MixDefs

open Variety

namespace MixPi2Lambda

variable (hε : ε ≠ .NonPolarized)

include h_le

section type12

noncomputable def X12 : Mix (Pi, 2 • Lambda) := by
  have _ := h_le
  refine ⟨Gene.ofRank (2 * m + 2) GeneType.Positive +
    Gene.ofRank (2 * m + 2) GeneType.Negative +
    Gene.ofRank (2 * n + 2) ε, ?_⟩
  rw [mem_Mix_iff, map_add, map_add, map_add, map_add]
  rw [evenPart_ofRank, if_pos (by grind),
    evenPart_ofRank, if_pos (by grind),
    evenPart_ofRank, if_pos (by grind),
    oddPart_ofRank, if_pos (by grind),
    oddPart_ofRank, if_pos (by grind),
    oddPart_ofRank, if_pos (by grind)]
  simp only [add_zero]
  refine ⟨?_, zero_mem _⟩
  rw [mem_Pi_iff_add, mem_Pi_iff_add, mem_Pi_iff, mem_Pi_iff, mem_Pi_iff,
    IsPolarized_ofRank (k := 2 * m + 2) (by omega),
    IsPolarized_ofRank (k := 2 * m + 2) (by omega),
    IsPolarized_ofRank (k := 2 * n + 2) (by omega)]
  exact ⟨⟨by decide, by decide⟩, hε⟩

lemma X12_eq : (X12 h_le hε).1 =
  Gene.ofRank (2 * m + 2) GeneType.Positive +
  Gene.ofRank (2 * m + 2) GeneType.Negative +
  Gene.ofRank (2 * n + 2) ε := rfl

@[simp] lemma neg_X12 :
    - (X12 h_le hε) = X12 h_le (GeneType.neg_ne_nonPolarized_iff.1 hε) := by
  apply Subtype.ext
  rw [Mix.Pi_2Lambda_neg_val, X12_eq, X12_eq, Chromosome.neg_add, Chromosome.neg_add,
    neg_ofRank, neg_ofRank, neg_ofRank, GeneType.neg_positive, GeneType.neg_negative]
  rw [show Gene.ofRank (2 * m + 2) GeneType.Negative +
      Gene.ofRank (2 * m + 2) GeneType.Positive + Gene.ofRank (2 * n + 2) (-ε) =
      Gene.ofRank (2 * m + 2) GeneType.Positive +
      Gene.ofRank (2 * m + 2) GeneType.Negative + Gene.ofRank (2 * n + 2) (-ε)
      from by abel]

noncomputable def Y12 : Mix (Pi, 2 • Lambda) := by
  have _ := h_le
  refine ⟨Gene.ofRank (2 * m + 1) GeneType.NonPolarized +
    Gene.ofRank (2 * m + 1) GeneType.NonPolarized +
    Gene.ofRank (2 * n + 4) ε, ?_⟩
  rw [mem_Mix_iff, map_add, map_add, map_add, map_add]
  rw [evenPart_ofRank, if_neg (by grind),
    evenPart_ofRank, if_pos (by grind),
    oddPart_ofRank, if_neg (by grind),
    oddPart_ofRank, if_pos (by grind)]
  simp only [zero_add, add_zero]
  refine ⟨?_, ?_⟩
  · rw [mem_Pi_iff, IsPolarized_ofRank (k := 2 * n + 4) (by omega)]
    exact hε
  · rw [AddSubmonoid.mem_smul_pointwise_iff_exists]
    refine ⟨Gene.ofRank (2 * m + 1) GeneType.NonPolarized, ?_, ?_⟩
    · rw [mem_Lambda_iff, IsNonPolarized_ofRank (k := 2 * m + 1) (by omega)]
    · rw [two_smul]

lemma Y12_eq : (Y12 h_le hε).1 =
  Gene.ofRank (2 * m + 1) GeneType.NonPolarized +
  Gene.ofRank (2 * m + 1) GeneType.NonPolarized +
  Gene.ofRank (2 * n + 4) ε := rfl

@[simp] lemma neg_Y12 :
    - (Y12 h_le hε) = Y12 h_le (GeneType.neg_ne_nonPolarized_iff.1 hε) := by
  apply Subtype.ext
  rw [Mix.Pi_2Lambda_neg_val, Y12_eq, Y12_eq, Chromosome.neg_add, Chromosome.neg_add]
  simp only [neg_ofRank, GeneType.neg_nonPolarized]

end type12

end MixPi2Lambda

end MixDefs
