import YoungDiagram.Variety

open Chromosome Pointwise

variable {ε : GeneType} {m n : ℕ}

-- Φ = (Π, 2 • Λ): g ranks odd, g^ε ranks even. Equation (8.11):
-- g^ε(m) + g^+(n) + g^-(n) → g^ε(m-2) + 2 g(n+1) with 1 < m ≤ n.
-- Parametrize m_paper = 2*m+2, n_paper = 2*n+2 (both even ≥ 2 for V_4).

local notation "type11X" =>
  Gene.ofRank (2 * m + 2) ε +
  Gene.ofRank (2 * n + 2) GeneType.Positive +
  Gene.ofRank (2 * n + 2) GeneType.Negative
local notation "type11Y" =>
  Gene.ofRank (2 * m)     ε +
  Gene.ofRank (2 * n + 3) GeneType.NonPolarized +
  Gene.ofRank (2 * n + 3) GeneType.NonPolarized

variable (h_le : m ≤ n)

include h_le

section Aux

namespace MixPi2Lambda

section type11_isMutation

omit h_le in
lemma mutation_type11_ne : type11X ≠ type11Y := by
  intro h
  replace h := congr_arg (· ⟨2 * n + 3, GeneType.NonPolarized, by omega⟩) h
  have h_m : 2 * m + 2 ≠ 0 := by omega
  have h_n : 2 * n + 2 ≠ 0 := by omega
  have h_n' : 2 * n + 3 ≠ 0 := by omega
  simp only [Gene.ofRank_def, h_m, h_n, h_n', ↓reduceDIte, Finsupp.coe_add,
    Pi.add_apply, Finsupp.single_eq_same, Finsupp.single_apply, Gene.mk.injEq,
    Nat.reduceEqDiff, Nat.add_left_cancel_iff, false_and] at h
  rcases eq_or_ne (2 * m) 0 with hm0 | hm0
  · rw [dif_pos hm0] at h
    simp only [Finsupp.coe_zero, Pi.zero_apply, zero_add] at h
    split_ifs at h <;> omega
  · rw [dif_neg hm0, Finsupp.single_apply] at h
    simp only [Gene.mk.injEq] at h
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

lemma mutation_type11_iterate_signature_eq (i k : ℕ) (hi : i ≤ k) :
    (prime^[i] (Gene.ofRank (2 * m + 2 + k) ε +
      Gene.ofRank (2 * n + 2 + k) GeneType.Positive +
      Gene.ofRank (2 * n + 2 + k) GeneType.Negative)).signature =
    (prime^[i] (Gene.ofRank (2 * m + k) ε +
      Gene.ofRank (2 * n + 3 + k) GeneType.NonPolarized +
      Gene.ofRank (2 * n + 3 + k) GeneType.NonPolarized)).signature := by
  simp only [iterate_map_add, map_add, prime_iterate_ofRank]
  have eq1 : 2 * m + 2 + k - i = 2 * m + k - i + 2 := by omega
  have eq2 : 2 * n + 3 + k - i = 2 * n + 2 + k - i + 1 := by omega
  rw [eq1, signature_ofRank_eq₂' (2 * m + k - i), eq2]
  have hPN1 := pos_neg_signature_sum_fst (2 * n + 2 + k - i)
  have hPN2 := pos_neg_signature_sum_snd (2 * n + 2 + k - i)
  have hNP1 := np_signature_fst (2 * n + 2 + k - i + 1)
  have hNP2 := np_signature_snd (2 * n + 2 + k - i + 1)
  ext
  · simp only [Prod.fst_add]; push_cast at *; linarith
  · simp only [Prod.snd_add]; push_cast at *; linarith

lemma mutation_type11_signature_eq :
    signature type11X = signature type11Y := by
  have := mutation_type11_iterate_signature_eq (ε := ε) h_le 0 0 le_rfl
  rwa [Function.iterate_zero_apply, Function.iterate_zero_apply, add_zero, add_zero,
    add_zero, add_zero] at this

lemma mutation_type11_le : type11X ≤ type11Y := by
  intro k
  simp only [iterate_map_add, map_add, prime_iterate_ofRank]
  by_cases hk1 : k ≤ 2 * m
  · have eq1 : 2 * m + 2 - k = 2 * m - k + 2 := by omega
    have eq2 : 2 * n + 3 - k = 2 * n + 2 - k + 1 := by omega
    rw [eq1, signature_ofRank_eq₂' (2 * m - k), eq2]
    have hPN1 := pos_neg_signature_sum_fst (2 * n + 2 - k)
    have hPN2 := pos_neg_signature_sum_snd (2 * n + 2 - k)
    have hNP1 := np_signature_fst (2 * n + 2 - k + 1)
    have hNP2 := np_signature_snd (2 * n + 2 - k + 1)
    refine ⟨?_, ?_⟩
    · simp only [Prod.fst_add]; push_cast at *; linarith
    · simp only [Prod.snd_add]; push_cast at *; linarith
  · by_cases hk2 : k ≤ 2 * n + 2
    · have eq1 : 2 * m + 2 - k = 0 ∨ 2 * m + 2 - k = 1 := by omega
      have eq2 : 2 * m - k = 0 := by omega
      have eq3 : 2 * n + 3 - k = 2 * n + 2 - k + 1 := by omega
      rw [eq2, Gene.ofRank_zero, map_zero, zero_add, eq3]
      have hPN1 := pos_neg_signature_sum_fst (2 * n + 2 - k)
      have hPN2 := pos_neg_signature_sum_snd (2 * n + 2 - k)
      have hNP1 := np_signature_fst (2 * n + 2 - k + 1)
      have hNP2 := np_signature_snd (2 * n + 2 - k + 1)
      rcases eq1 with heq | heq
      · rw [heq, Gene.ofRank_zero, map_zero, zero_add]
        refine ⟨?_, ?_⟩
        · simp only [Prod.fst_add]; push_cast at *; linarith
        · simp only [Prod.snd_add]; push_cast at *; linarith
      · rw [heq]
        have hsig_one_nn :
            (Gene.ofRank 1 ε).signature.1 ≤ 1 ∧ (Gene.ofRank 1 ε).signature.2 ≤ 1 := by
          match ε with
          | .NonPolarized => rw [signature_ofRank_nonPolarized]; constructor <;>
              (push_cast; linarith only [])
          | .Positive => rw [signature_ofRank_one_positive]; constructor <;>
              (push_cast; linarith only [])
          | .Negative => rw [signature_ofRank_one_negative]; constructor <;>
              (push_cast; linarith only [])
        refine ⟨?_, ?_⟩
        · simp only [Prod.fst_add]; push_cast at *
          have := hsig_one_nn.1
          linarith
        · simp only [Prod.snd_add]; push_cast at *
          have := hsig_one_nn.2
          linarith
    · have eq1 : 2 * m + 2 - k = 0 := by omega
      have eq2 : 2 * m - k = 0 := by omega
      have eq3 : 2 * n + 2 - k = 0 := by omega
      have eq4 : 2 * n + 3 - k = 0 ∨ 2 * n + 3 - k = 1 := by omega
      rw [eq1, eq2, eq3]
      simp only [Gene.ofRank_zero, map_zero, zero_add, add_zero]
      rcases eq4 with heq | heq
      · rw [heq, Gene.ofRank_zero, map_zero, zero_add]
      · rw [heq, signature_ofRank_nonPolarized, Prod.mk_add_mk]
        push_cast
        refine ⟨?_, ?_⟩ <;> simp

end type11_isMutation

end MixPi2Lambda

end Aux

section MixDefs

open Variety

namespace MixPi2Lambda

variable (hε : ε ≠ .NonPolarized)

include h_le

section type11

noncomputable def X11 : Mix (Pi, 2 • Lambda) := by
  have _ := h_le
  refine ⟨Gene.ofRank (2 * m + 2) ε +
    Gene.ofRank (2 * n + 2) GeneType.Positive +
    Gene.ofRank (2 * n + 2) GeneType.Negative, ?_⟩
  rw [mem_Mix_iff, map_add, map_add, map_add, map_add]
  rw [evenPart_ofRank, if_pos (by grind),
    evenPart_ofRank, if_pos (by grind),
    evenPart_ofRank, if_pos (by grind),
    oddPart_ofRank, if_pos (by grind),
    oddPart_ofRank, if_pos (by grind),
    oddPart_ofRank, if_pos (by grind)]
  refine ⟨?_, zero_mem _⟩
  rw [mem_Pi_iff_add, mem_Pi_iff_add, mem_Pi_iff, mem_Pi_iff, mem_Pi_iff,
    IsPolarized_ofRank (k := 2 * m + 2) (by omega),
    IsPolarized_ofRank (k := 2 * n + 2) (by omega),
    IsPolarized_ofRank (k := 2 * n + 2) (by omega)]
  exact ⟨⟨hε, by decide⟩, by decide⟩

lemma X11_eq : (X11 h_le hε).1 =
  Gene.ofRank (2 * m + 2) ε +
  Gene.ofRank (2 * n + 2) GeneType.Positive +
  Gene.ofRank (2 * n + 2) GeneType.Negative := rfl

@[simp] lemma neg_X11 :
    - (X11 h_le hε) = X11 h_le (GeneType.neg_ne_nonPolarized_iff.1 hε) := by
  apply Subtype.ext
  rw [Mix.Pi_2Lambda_neg_val, X11_eq, X11_eq, Chromosome.neg_add, Chromosome.neg_add,
    neg_ofRank, neg_ofRank, neg_ofRank, GeneType.neg_positive, GeneType.neg_negative,
    add_assoc, add_assoc, add_right_inj, add_comm]

noncomputable def Y11 : Mix (Pi, 2 • Lambda) := by
  have _ := h_le
  refine ⟨Gene.ofRank (2 * m) ε +
    Gene.ofRank (2 * n + 3) GeneType.NonPolarized +
    Gene.ofRank (2 * n + 3) GeneType.NonPolarized, ?_⟩
  rw [mem_Mix_iff, map_add, map_add, map_add, map_add, evenPart_ofRank,
    if_pos (by grind), oddPart_ofRank, if_pos (by grind),
    evenPart_ofRank, if_neg (by grind), oddPart_ofRank, if_neg (by grind)]
  match m with
  | 0 =>
    rw [Nat.mul_zero, Gene.ofRank_zero, zero_add, add_zero, zero_add]
    refine ⟨zero_mem _, ?_⟩
    rw [AddSubmonoid.mem_smul_pointwise_iff_exists]
    refine ⟨Gene.ofRank (2 * n + 3) GeneType.NonPolarized, ?_, ?_⟩
    · rw [mem_Lambda_iff, IsNonPolarized_ofRank (k := 2 * n + 3) (by omega)]
    · rw [two_smul]
  | m + 1 =>
    simp only [zero_add, add_zero]
    refine ⟨?_, ?_⟩
    · rw [mem_Pi_iff, IsPolarized_ofRank (k := 2 * (m + 1)) (by omega)]
      exact hε
    · rw [AddSubmonoid.mem_smul_pointwise_iff_exists]
      refine ⟨Gene.ofRank (2 * n + 3) GeneType.NonPolarized, ?_, ?_⟩
      · rw [mem_Lambda_iff, IsNonPolarized_ofRank (k := 2 * n + 3) (by omega)]
      · rw [two_smul]

lemma Y11_eq : (Y11 h_le hε).1 =
  Gene.ofRank (2 * m) ε +
  Gene.ofRank (2 * n + 3) GeneType.NonPolarized +
  Gene.ofRank (2 * n + 3) GeneType.NonPolarized := rfl

@[simp] lemma neg_Y11 :
    - (Y11 h_le hε) = Y11 h_le (GeneType.neg_ne_nonPolarized_iff.1 hε) := by
  apply Subtype.ext
  rw [Mix.Pi_2Lambda_neg_val, Y11_eq, Y11_eq, Chromosome.neg_add, Chromosome.neg_add]
  simp only [neg_ofRank, GeneType.neg_nonPolarized]

end type11

end MixPi2Lambda

end MixDefs
