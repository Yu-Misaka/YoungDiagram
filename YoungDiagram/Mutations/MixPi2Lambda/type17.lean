import YoungDiagram.Variety

open Chromosome Pointwise

variable {ε : GeneType} {m n : ℕ}

-- Φ = (Π, 2 • Λ): g ranks odd, g^ε ranks even. Equation (8.17):
-- g^ε(m_paper) + 2 g^{-ε}(n_paper) → g^{-ε}(m_paper - 2) + 2 g(n_paper + 1)
-- with m_paper = 2 m + 2, n_paper = 2 n + 2 (both even, ≥ 2).

local notation "type17X" =>
  Gene.ofRank (2 * m + 2) ε +
  Gene.ofRank (2 * n + 2) (- ε) +
  Gene.ofRank (2 * n + 2) (- ε)
local notation "type17Y" =>
  Gene.ofRank (2 * m) (- ε) +
  Gene.ofRank (2 * n + 3) GeneType.NonPolarized +
  Gene.ofRank (2 * n + 3) GeneType.NonPolarized

variable (h_le : m ≤ n)

include h_le

section Aux

namespace MixPi2Lambda

section type17_isMutation

omit h_le in
lemma mutation_type17_ne : type17X ≠ type17Y := by
  intro h
  replace h := congr_arg (· ⟨2 * n + 3, GeneType.NonPolarized, by omega⟩) h
  have h_m : 2 * m + 2 ≠ 0 := by omega
  have h_n : 2 * n + 2 ≠ 0 := by omega
  have h_n' : 2 * n + 3 ≠ 0 := by omega
  rcases eq_or_ne (2 * m) 0 with hm0 | hm0
  · simp only [Gene.ofRank_def, h_n, h_n', hm0, ↓reduceDIte, Finsupp.coe_add,
      Pi.add_apply, Finsupp.single_eq_same, Finsupp.single_apply, Gene.mk.injEq,
      Nat.reduceEqDiff, Nat.add_left_cancel_iff, false_and] at h
    split_ifs at h; omega
  · simp only [Gene.ofRank_def, h_m, h_n, h_n', hm0, ↓reduceDIte, Finsupp.coe_add,
      Pi.add_apply, Finsupp.single_eq_same, Finsupp.single_apply, Gene.mk.injEq,
      Nat.reduceEqDiff, Nat.add_left_cancel_iff, false_and] at h
    split_ifs at h <;> omega

-- Helper: iterating signature_ofRank_eq₂' gives s(k + 2j, ε) = s(k, ε) + (j, j).
omit h_le in
private lemma signature_shift_two (k : ℕ) (ε : GeneType) :
    ∀ j : ℕ, (Gene.ofRank (k + 2 * j) ε).signature =
      (Gene.ofRank k ε).signature + ((j : ℚ), (j : ℚ)) := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
    have : k + 2 * (j + 1) = (k + 2 * j) + 2 := by ring
    rw [this, signature_ofRank_eq₂', ih]
    ext
    · simp only [Prod.fst_add]; push_cast; ring
    · simp only [Prod.snd_add]; push_cast; ring

omit h_le in
private lemma mutation_type17_sig_eq_aux (p d : ℕ) :
    (Gene.ofRank (2 * p + 2 + d) ε).signature +
      (Gene.ofRank (2 * (p + (n - m)) + 2 + d) (- ε)).signature +
      (Gene.ofRank (2 * (p + (n - m)) + 2 + d) (- ε)).signature =
    (Gene.ofRank (2 * p + d) (- ε)).signature +
      (Gene.ofRank (2 * (p + (n - m)) + 3 + d) .NonPolarized).signature +
      (Gene.ofRank (2 * (p + (n - m)) + 3 + d) .NonPolarized).signature := by
  set A := 2 * p + d with hA_def
  set B := 2 * (p + (n - m)) + 2 + d with hB_def
  -- A+2 = 2p+2+d, B = 2(p+(n-m))+2+d
  have hA2 : 2 * p + 2 + d = A + 2 := by change _ = 2 * p + d + 2; ring
  have hB1 : 2 * (p + (n - m)) + 3 + d = B + 1 := by change _ = 2 * (p + (n - m)) + 2 + d + 1; ring
  rw [hA2, hB1]
  -- s(A+2, ε) = s(A, ε) + (1, 1)
  have h_A2 : (Gene.ofRank (A + 2) ε).signature =
      (Gene.ofRank A ε).signature + (1, 1) := signature_ofRank_eq₂' A
  -- s(A, ε) + s(A, -ε) = (A, A)
  have h_sumA : (Gene.ofRank A ε).signature + (Gene.ofRank A (- ε)).signature =
      ((A : ℚ), (A : ℚ)) := by
    have h := signature_ofRank_sum_even (m := A) (n := A) (ε := ε) ⟨A, by ring⟩
    rw [h]; congr 1 <;> ring
  have h_Aneg : (Gene.ofRank A (- ε)).signature =
      ((A : ℚ), (A : ℚ)) - (Gene.ofRank A ε).signature := by
    rw [← h_sumA]; abel
  -- s(B, ε) + s(B, -ε) = (B, B)
  have h_sumB : (Gene.ofRank B ε).signature + (Gene.ofRank B (- ε)).signature =
      ((B : ℚ), (B : ℚ)) := by
    have h := signature_ofRank_sum_even (m := B) (n := B) (ε := ε) ⟨B, by ring⟩
    rw [h]; congr 1 <;> ring
  have h_Bneg : (Gene.ofRank B (- ε)).signature =
      ((B : ℚ), (B : ℚ)) - (Gene.ofRank B ε).signature := by
    rw [← h_sumB]; abel
  -- s(B, ε) = s(A, ε) + (n-m+1, n-m+1) by iterating eq₂'
  have h_BA : (Gene.ofRank B ε).signature =
      (Gene.ofRank A ε).signature + (((n - m + 1 : ℕ) : ℚ), ((n - m + 1 : ℕ) : ℚ)) := by
    have := signature_shift_two A ε (n - m + 1)
    have hrw : A + 2 * (n - m + 1) = B := by
      change 2 * p + d + 2 * (n - m + 1) = 2 * (p + (n - m)) + 2 + d
      ring
    rw [hrw] at this
    rw [this]
  -- s(B+1, NP) = ((B+1)/2, (B+1)/2)
  have h_BNP : (Gene.ofRank (B + 1) .NonPolarized).signature =
      (((B + 1 : ℕ) : ℚ) / 2, ((B + 1 : ℕ) : ℚ) / 2) := signature_ofRank_nonPolarized
  rw [h_A2, h_Aneg, h_Bneg, h_BA, h_BNP]
  -- B = A + 2((n-m)+1) (as nat)
  have hBA_nat : B = A + 2 * ((n - m) + 1) := by
    ring
  have hBA_arith : (B : ℚ) = (A : ℚ) + 2 * (((n - m : ℕ) : ℚ) + 1) := by
    rw [hBA_nat]; push_cast; ring
  ext
  · simp only [Prod.fst_add, Prod.fst_sub]
    push_cast
    rw [hBA_arith]
    ring
  · simp only [Prod.snd_add, Prod.snd_sub]
    push_cast
    rw [hBA_arith]
    ring

lemma mutation_type17_iterate_signature_eq (i j : ℕ) (hi : i ≤ j) :
    (prime^[i] (Gene.ofRank (2 * m + 2 + j) ε +
        Gene.ofRank (2 * n + 2 + j) (- ε) +
        Gene.ofRank (2 * n + 2 + j) (- ε))).signature =
    (prime^[i] (Gene.ofRank (2 * m + j) (- ε) +
        Gene.ofRank (2 * n + 3 + j) .NonPolarized +
        Gene.ofRank (2 * n + 3 + j) .NonPolarized)).signature := by
  simp only [iterate_map_add, map_add, prime_iterate_ofRank]
  have eq1 : 2 * m + 2 + j - i = 2 * m + 2 + (j - i) := by omega
  have eq2 : 2 * n + 2 + j - i = 2 * (m + (n - m)) + 2 + (j - i) := by
    have : 2 * (m + (n - m)) = 2 * n := by omega
    omega
  have eq3 : 2 * m + j - i = 2 * m + (j - i) := by omega
  have eq4 : 2 * n + 3 + j - i = 2 * (m + (n - m)) + 3 + (j - i) := by
    have : 2 * (m + (n - m)) = 2 * n := by omega
    omega
  rw [eq1, eq2, eq3, eq4]
  exact mutation_type17_sig_eq_aux m (j - i)

lemma mutation_type17_signature_eq :
    signature type17X = signature type17Y := by
  have := mutation_type17_iterate_signature_eq (ε := ε) h_le 0 0 le_rfl
  rwa [Function.iterate_zero_apply, Function.iterate_zero_apply, add_zero, add_zero] at this

lemma mutation_type17_le : type17X ≤ type17Y := by
  intro i
  simp only [iterate_map_add, map_add, prime_iterate_ofRank]
  by_cases hi1 : i ≤ 2 * m
  · -- equality from aux with p = (2m-i)/2, d = (2m-i)%2.
    have heq : (Gene.ofRank (2 * m + 2 - i) ε).signature +
        (Gene.ofRank (2 * n + 2 - i) (- ε)).signature +
        (Gene.ofRank (2 * n + 2 - i) (- ε)).signature =
      (Gene.ofRank (2 * m - i) (- ε)).signature +
        (Gene.ofRank (2 * n + 3 - i) .NonPolarized).signature +
        (Gene.ofRank (2 * n + 3 - i) .NonPolarized).signature := by
      have := mutation_type17_sig_eq_aux (n := n) (m := m) (ε := ε)
        ((2 * m - i) / 2) ((2 * m - i) % 2)
      have eq1 : 2 * ((2 * m - i) / 2) + 2 + (2 * m - i) % 2 = 2 * m + 2 - i := by omega
      have eq2 : 2 * ((2 * m - i) / 2 + (n - m)) + 2 + (2 * m - i) % 2 = 2 * n + 2 - i := by
        have : 2 * (n - m) = 2 * n - 2 * m := by omega
        omega
      have eq3 : 2 * ((2 * m - i) / 2) + (2 * m - i) % 2 = 2 * m - i := by omega
      have eq4 : 2 * ((2 * m - i) / 2 + (n - m)) + 3 + (2 * m - i) % 2 = 2 * n + 3 - i := by
        have : 2 * (n - m) = 2 * n - 2 * m := by omega
        omega
      rw [eq1, eq2, eq3, eq4] at this
      exact this
    rw [heq]
  · push Not at hi1
    by_cases hi2 : i ≤ 2 * n + 2
    · have e3 : 2 * m - i = 0 := by omega
      rw [e3, Gene.ofRank_zero, map_zero, zero_add]
      by_cases hi3 : 2 * m + 2 - i = 0
      · -- 2m+2-i = 0, i.e., i ≥ 2m+2
        rw [hi3, Gene.ofRank_zero, map_zero, zero_add]
        -- Goal: 2·s(2n+2-i, -ε) ≤ 2·s(2n+3-i, NP)
        -- Both are nonneg-half-style. Use signature_ofRank_le.
        have heq2n : 2 * n + 3 - i = (2 * n + 2 - i) + 1 := by omega
        rw [heq2n]
        simp only [signature_ofRank_nonPolarized]
        have hle := signature_ofRank_le (ε := -ε) (k := 2 * n + 2 - i)
        push_cast
        constructor
        · simp only [Prod.fst_add]
          have : (Gene.ofRank (2 * n + 2 - i) (-ε)).signature.1 ≤
              (((2 * n + 2 - i : ℕ) : ℚ) + 1) / 2 := hle.1
          linarith
        · simp only [Prod.snd_add]
          have : (Gene.ofRank (2 * n + 2 - i) (-ε)).signature.2 ≤
              (((2 * n + 2 - i : ℕ) : ℚ) + 1) / 2 := hle.2
          linarith
      · -- 2m+2-i = 1, i.e., i = 2m+1
        have hi_eq : i = 2 * m + 1 := by omega
        subst hi_eq
        have e1' : 2 * m + 2 - (2 * m + 1) = 1 := by omega
        have e2' : 2 * n + 2 - (2 * m + 1) = 2 * (n - m) + 1 := by omega
        have e3' : 2 * n + 3 - (2 * m + 1) = 2 * (n - m) + 2 := by omega
        simp only [e1', e2', e3']
        have h_succ : (Gene.ofRank 1 ε).signature +
            (Gene.ofRank (2 * (n - m) + 1) (- ε)).signature =
            (Gene.ofRank (2 * (n - m) + 2) GeneType.NonPolarized).signature := by
          have h := signature_ofRank_succ_add_pred_neg (ε := ε) (m := 0) (n := 2 * (n - m) + 2)
            (by omega) (by refine ⟨n - m + 1, ?_⟩; ring)
          simp only [Gene.ofRank_zero, map_zero, zero_add] at h
          have hrw : 2 * (n - m) + 2 - 1 = 2 * (n - m) + 1 := by omega
          rw [hrw] at h
          exact h
        have h_neg_eq : (Gene.ofRank (2 * (n - m) + 1) (- ε)).signature =
            (Gene.ofRank (2 * (n - m) + 2) GeneType.NonPolarized).signature -
              (Gene.ofRank 1 ε).signature := by
          rw [← h_succ]; abel
        rw [h_neg_eq]
        have hnn := signature_nonneg (Gene.ofRank 1 ε)
        have hnn1 : (0 : ℚ) ≤ (Gene.ofRank 1 ε).signature.1 := hnn.1
        have hnn2 : (0 : ℚ) ≤ (Gene.ofRank 1 ε).signature.2 := hnn.2
        constructor
        · simp only [Prod.fst_add, Prod.fst_sub]; linarith
        · simp only [Prod.snd_add, Prod.snd_sub]; linarith
    · push Not at hi2
      have e1 : 2 * m + 2 - i = 0 := by omega
      have e2 : 2 * n + 2 - i = 0 := by omega
      have e3 : 2 * m - i = 0 := by omega
      by_cases hi3 : i ≤ 2 * n + 3
      · have e4 : 2 * n + 3 - i = 0 ∨ 2 * n + 3 - i = 1 := by omega
        rcases e4 with e4 | e4
        · simp only [e1, e2, e3, e4, Gene.ofRank_zero, map_zero, add_zero]
          exact le_refl _
        · simp only [e1, e2, e3, e4, Gene.ofRank_zero, map_zero, zero_add, add_zero]
          have h1 := signature_nonneg (Gene.ofRank 1 GeneType.NonPolarized)
          exact add_nonneg h1 h1
      · push Not at hi3
        have e4 : 2 * n + 3 - i = 0 := by omega
        simp only [e1, e2, e3, e4, Gene.ofRank_zero, map_zero, add_zero]
        exact le_refl _

end type17_isMutation

end MixPi2Lambda

end Aux

section MixDefs

open Variety

namespace MixPi2Lambda

variable (hε : ε ≠ .NonPolarized)

include h_le

section type17

noncomputable def X17 : Mix (Pi, 2 • Lambda) := by
  have _ := h_le
  refine ⟨Gene.ofRank (2 * m + 2) ε + Gene.ofRank (2 * n + 2) (- ε) +
    Gene.ofRank (2 * n + 2) (- ε), ?_⟩
  rw [mem_Mix_iff, map_add, map_add, map_add, map_add,
    evenPart_ofRank, if_pos (by grind),
    evenPart_ofRank, if_pos (by grind),
    oddPart_ofRank, if_pos (by grind),
    oddPart_ofRank, if_pos (by grind),
    add_zero, add_zero]
  refine ⟨?_, zero_mem _⟩
  rw [mem_Pi_iff_add, mem_Pi_iff_add, mem_Pi_iff, mem_Pi_iff,
    IsPolarized_ofRank (k := 2 * m + 2) (by omega),
    IsPolarized_ofRank (k := 2 * n + 2) (by omega)]
  exact ⟨⟨hε, by rwa [ne_eq, ← GeneType.neg_eq_nonPolarized_iff]⟩,
    by rwa [ne_eq, ← GeneType.neg_eq_nonPolarized_iff]⟩

lemma X17_eq : (X17 h_le hε).1 =
  Gene.ofRank (2 * m + 2) ε + Gene.ofRank (2 * n + 2) (- ε) +
  Gene.ofRank (2 * n + 2) (- ε) := rfl

@[simp] lemma neg_X17 :
    - (X17 h_le hε) = X17 h_le (GeneType.neg_ne_nonPolarized_iff.1 hε) := by
  apply Subtype.ext
  simp only [Mix.Pi_2Lambda_neg_val, X17_eq, Chromosome.neg_add, neg_ofRank, neg_neg]

noncomputable def Y17 : Mix (Pi, 2 • Lambda) := by
  have _ := h_le
  have _ := hε
  refine ⟨Gene.ofRank (2 * m) (- ε) +
    Gene.ofRank (2 * n + 3) GeneType.NonPolarized +
    Gene.ofRank (2 * n + 3) GeneType.NonPolarized, ?_⟩
  rw [mem_Mix_iff, map_add, map_add, map_add, map_add, evenPart_ofRank, if_pos (by grind),
    evenPart_ofRank, if_neg (by grind), oddPart_ofRank, if_pos (by grind), oddPart_ofRank,
    if_neg (by grind)]
  match m with
  | 0 =>
    simp only [Nat.mul_zero, Gene.ofRank_zero, zero_add, add_zero]
    refine ⟨zero_mem _, ?_⟩
    rw [AddSubmonoid.mem_smul_pointwise_iff_exists]
    refine ⟨Gene.ofRank (2 * n + 3) GeneType.NonPolarized, ?_, ?_⟩
    · rw [mem_Lambda_iff, IsNonPolarized_ofRank (k := 2 * n + 3) (by omega)]
    · rw [two_smul]
  | m + 1 =>
    rw [zero_add, add_zero, add_zero]
    refine ⟨?_, ?_⟩
    · rw [mem_Pi_iff, IsPolarized_ofRank (k := 2 * (m + 1)) (by omega)]
      rwa [ne_eq, ← GeneType.neg_eq_nonPolarized_iff]
    · rw [AddSubmonoid.mem_smul_pointwise_iff_exists]
      refine ⟨Gene.ofRank (2 * n + 3) GeneType.NonPolarized, ?_, ?_⟩
      · rw [mem_Lambda_iff, IsNonPolarized_ofRank (k := 2 * n + 3) (by omega)]
      · rw [two_smul]

lemma Y17_eq : (Y17 h_le hε).1 =
  Gene.ofRank (2 * m) (- ε) +
  Gene.ofRank (2 * n + 3) GeneType.NonPolarized +
  Gene.ofRank (2 * n + 3) GeneType.NonPolarized := rfl

@[simp] lemma neg_Y17 :
    - (Y17 h_le hε) = Y17 h_le (GeneType.neg_ne_nonPolarized_iff.1 hε) := by
  apply Subtype.ext
  simp only [Mix.Pi_2Lambda_neg_val, Y17_eq, Chromosome.neg_add, neg_ofRank, neg_neg,
    GeneType.neg_nonPolarized]

end type17

end MixPi2Lambda

end MixDefs
