import YoungDiagram.Variety

open Chromosome Pointwise

variable {ε : GeneType} {m n : ℕ}

-- Φ = (2 • Λ, Π): g ranks even, g^ε ranks odd. Equation (8.16):
-- 2 g^ε(m_paper) + g^{-ε}(n_paper) → 2 g(m_paper - 1) + g^ε(n_paper + 2)
-- with m_paper = 2 m + 1, n_paper = 2 n + 1 (both odd, ≥ 1).

local notation "type16X" =>
  Gene.ofRank (2 * m + 1) ε +
  Gene.ofRank (2 * m + 1) ε +
  Gene.ofRank (2 * n + 1) (- ε)
local notation "type16Y" =>
  Gene.ofRank (2 * m) GeneType.NonPolarized +
  Gene.ofRank (2 * m) GeneType.NonPolarized +
  Gene.ofRank (2 * n + 3) ε

variable (h_le : m ≤ n)

include h_le

section Aux

namespace Mix2LambdaPi

section type16_isMutation

omit h_le in
lemma mutation_type16_ne : type16X ≠ type16Y := by
  intro h
  replace h := congr_arg (· ⟨2 * n + 3, ε, by omega⟩) h
  have h_m : 2 * m + 1 ≠ 0 := by omega
  have h_n : 2 * n + 1 ≠ 0 := by omega
  have h_n' : 2 * n + 3 ≠ 0 := by omega
  rcases eq_or_ne (2 * m) 0 with hm0 | hm0
  · simp only [Gene.ofRank_def, h_n, h_n', hm0, ↓reduceDIte, Finsupp.coe_add,
      Pi.add_apply, Finsupp.single_apply, Gene.mk.injEq, Nat.reduceEqDiff,
      Nat.add_left_cancel_iff, false_and] at h
    split_ifs at h; omega
  · simp only [Gene.ofRank_def, h_m, h_n, h_n', hm0, ↓reduceDIte, Finsupp.coe_add,
      Pi.add_apply, Finsupp.single_apply, Gene.mk.injEq, Nat.reduceEqDiff,
      Nat.add_left_cancel_iff, false_and] at h
    split_ifs at h <;> omega

omit h_le in
private lemma mutation_type16_sig_eq_aux (p d : ℕ) :
    (Gene.ofRank (2 * p + 1 + d) ε).signature +
      (Gene.ofRank (2 * p + 1 + d) ε).signature +
      (Gene.ofRank (2 * (p + (n - m)) + 1 + d) (- ε)).signature =
    (Gene.ofRank (2 * p + d) .NonPolarized).signature +
      (Gene.ofRank (2 * p + d) .NonPolarized).signature +
      (Gene.ofRank (2 * (p + (n - m)) + 3 + d) ε).signature := by
  set A := 2 * p + d
  set B := 2 * (p + (n - m)) + 2 + d
  have heven : Even (A + B) := by
    refine ⟨p + (p + (n - m)) + 1 + d, ?_⟩
    ring
  have h1 :
      (Gene.ofRank (A + 1) ε).signature + (Gene.ofRank (B - 1) (- ε)).signature =
      (Gene.ofRank A .NonPolarized).signature + (Gene.ofRank B .NonPolarized).signature :=
    signature_ofRank_succ_add_pred_neg (by omega) heven
  have h2 :
      (Gene.ofRank (A + 1) ε).signature + (Gene.ofRank B .NonPolarized).signature =
      (Gene.ofRank A .NonPolarized).signature + (Gene.ofRank (B + 1) ε).signature :=
    signature_ofRank_succ_add_nonPolarized heven
  have hB1 : B - 1 = 2 * (p + (n - m)) + 1 + d := by omega
  have hB1' : B + 1 = 2 * (p + (n - m)) + 3 + d := by ring
  have hA1 : A + 1 = 2 * p + 1 + d := by ring
  rw [hB1] at h1
  rw [hB1'] at h2
  rw [hA1] at h1 h2
  calc (Gene.ofRank (2 * p + 1 + d) ε).signature +
          (Gene.ofRank (2 * p + 1 + d) ε).signature +
          (Gene.ofRank (2 * (p + (n - m)) + 1 + d) (- ε)).signature
      = (Gene.ofRank (2 * p + 1 + d) ε).signature +
          ((Gene.ofRank (2 * p + 1 + d) ε).signature +
            (Gene.ofRank (2 * (p + (n - m)) + 1 + d) (- ε)).signature) := by rw [add_assoc]
    _ = (Gene.ofRank (2 * p + 1 + d) ε).signature +
          ((Gene.ofRank A .NonPolarized).signature +
            (Gene.ofRank B .NonPolarized).signature) := by rw [h1]
    _ = (Gene.ofRank A .NonPolarized).signature +
          ((Gene.ofRank (2 * p + 1 + d) ε).signature +
            (Gene.ofRank B .NonPolarized).signature) := by
        rw [← add_assoc, add_comm _ (Gene.ofRank A .NonPolarized).signature, add_assoc]
    _ = (Gene.ofRank A .NonPolarized).signature +
          ((Gene.ofRank A .NonPolarized).signature +
            (Gene.ofRank (2 * (p + (n - m)) + 3 + d) ε).signature) := by rw [h2]
    _ = (Gene.ofRank (2 * p + d) .NonPolarized).signature +
          (Gene.ofRank (2 * p + d) .NonPolarized).signature +
          (Gene.ofRank (2 * (p + (n - m)) + 3 + d) ε).signature := by
        rw [← add_assoc]

lemma mutation_type16_iterate_signature_eq (i j : ℕ) (hi : i ≤ j) :
    (prime^[i] (Gene.ofRank (2 * m + 1 + j) ε +
        Gene.ofRank (2 * m + 1 + j) ε +
        Gene.ofRank (2 * n + 1 + j) (- ε))).signature =
    (prime^[i] (Gene.ofRank (2 * m + j) .NonPolarized +
        Gene.ofRank (2 * m + j) .NonPolarized +
        Gene.ofRank (2 * n + 3 + j) ε)).signature := by
  simp only [iterate_map_add, map_add, prime_iterate_ofRank]
  have eq1 : 2 * m + 1 + j - i = 2 * m + 1 + (j - i) := by omega
  have eq2 : 2 * n + 1 + j - i = 2 * (m + (n - m)) + 1 + (j - i) := by
    have : 2 * (m + (n - m)) = 2 * n := by omega
    omega
  have eq3 : 2 * m + j - i = 2 * m + (j - i) := by omega
  have eq4 : 2 * n + 3 + j - i = 2 * (m + (n - m)) + 3 + (j - i) := by
    have : 2 * (m + (n - m)) = 2 * n := by omega
    omega
  rw [eq1, eq2, eq3, eq4]
  exact mutation_type16_sig_eq_aux m (j - i)

lemma mutation_type16_signature_eq :
    signature type16X = signature type16Y := by
  have := mutation_type16_iterate_signature_eq (ε := ε) h_le 0 0 le_rfl
  rwa [Function.iterate_zero_apply, Function.iterate_zero_apply, add_zero, add_zero] at this

lemma mutation_type16_le : type16X ≤ type16Y := by
  intro i
  simp only [iterate_map_add, map_add, prime_iterate_ofRank]
  by_cases hi1 : i ≤ 2 * m
  · -- Apply the helper with p = (2m-i)/2, d = (2m-i) % 2
    have heq : (Gene.ofRank (2 * m + 1 - i) ε).signature +
        (Gene.ofRank (2 * m + 1 - i) ε).signature +
        (Gene.ofRank (2 * n + 1 - i) (- ε)).signature =
      (Gene.ofRank (2 * m - i) .NonPolarized).signature +
        (Gene.ofRank (2 * m - i) .NonPolarized).signature +
        (Gene.ofRank (2 * n + 3 - i) ε).signature := by
      have := mutation_type16_sig_eq_aux (n := n) (m := m) (ε := ε)
        ((2 * m - i) / 2) ((2 * m - i) % 2)
      have eq1 : 2 * ((2 * m - i) / 2) + 1 + (2 * m - i) % 2 = 2 * m + 1 - i := by omega
      have eq2 : 2 * ((2 * m - i) / 2 + (n - m)) + 1 + (2 * m - i) % 2 = 2 * n + 1 - i := by
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
    by_cases hi2 : i ≤ 2 * n + 1
    · have e1 : 2 * m + 1 - i = 0 := by omega
      have e2 : 2 * m - i = 0 := by omega
      simp only [e1, e2, Gene.ofRank_zero, map_zero, zero_add, add_zero]
      have heq : 2 * n + 3 - i = (2 * n + 1 - i) + 2 := by omega
      rw [heq, signature_ofRank_eq₂' (2 * n + 1 - i)]
      -- need: s(2n+1-i, -ε) ≤ s(2n+1-i, ε) + (1, 1)
      have hsum : (Gene.ofRank (2 * n + 1 - i) ε).signature +
          (Gene.ofRank (2 * n + 1 - i) (- ε)).signature =
          (((2 * n + 1 - i : ℕ) : ℚ), ((2 * n + 1 - i : ℕ) : ℚ)) := by
        have h := signature_ofRank_sum_even (m := 2 * n + 1 - i) (n := 2 * n + 1 - i) (ε := ε)
          (by grind only [= Nat.even_iff])
        rw [h]
        congr 1 <;> ring
      have hge := signature_ofRank_ge (ε := ε) (k := 2 * n + 1 - i)
      -- s(2n+1-i, -ε) = (2n+1-i, 2n+1-i) - s(2n+1-i, ε)
      have heq2 : (Gene.ofRank (2 * n + 1 - i) (- ε)).signature =
          (((2 * n + 1 - i : ℕ) : ℚ), ((2 * n + 1 - i : ℕ) : ℚ)) -
            (Gene.ofRank (2 * n + 1 - i) ε).signature := by
        rw [← hsum]; abel
      rw [heq2]
      -- Goal: (2n+1-i, 2n+1-i) - s(2n+1-i, ε) ≤ s(2n+1-i, ε) + (1, 1)
      -- ⟺ (2n+1-i - 1, 2n+1-i - 1) ≤ 2 · s(2n+1-i, ε)
      -- ⟺ ((2n+1-i - 1)/2, (2n+1-i - 1)/2) ≤ s(2n+1-i, ε)
      -- which is signature_ofRank_ge
      have : (Gene.ofRank (2 * n + 1 - i) ε).signature.1 ≥ ((2 * n + 1 - i : ℕ) - 1 : ℚ) / 2 ∧
          (Gene.ofRank (2 * n + 1 - i) ε).signature.2 ≥ ((2 * n + 1 - i : ℕ) - 1 : ℚ) / 2 := by
        constructor
        · exact hge.1
        · exact hge.2
      rcases this with ⟨h1, h2⟩
      constructor
      · simp only [Prod.fst_sub, Prod.fst_add]
        linarith
      · simp only [Prod.snd_sub, Prod.snd_add]
        linarith
    · have e1 : 2 * m + 1 - i = 0 := by omega
      have e2 : 2 * m - i = 0 := by omega
      have e3 : 2 * n + 1 - i = 0 := by omega
      simp only [e1, e2, e3, Gene.ofRank_zero, map_zero, zero_add, add_zero]
      exact signature_nonneg _

end type16_isMutation

end Mix2LambdaPi

end Aux

section MixDefs

open Variety

namespace Mix2LambdaPi

variable (hε : ε ≠ .NonPolarized)

include h_le

section type16

noncomputable def X16 : Mix (2 • Lambda, Pi) := by
  have _ := h_le
  refine ⟨Gene.ofRank (2 * m + 1) ε + Gene.ofRank (2 * m + 1) ε +
    Gene.ofRank (2 * n + 1) (- ε), ?_⟩
  rw [mem_Mix_iff, map_add, map_add, map_add, map_add,
    evenPart_ofRank, if_neg (by grind), evenPart_ofRank, if_neg (by grind),
    oddPart_ofRank, if_neg (by grind), oddPart_ofRank, if_neg (by grind),
    zero_add, zero_add]
  refine ⟨zero_mem _, ?_⟩
  rw [mem_Pi_iff_add, mem_Pi_iff_add, mem_Pi_iff, mem_Pi_iff,
    IsPolarized_ofRank (k := 2 * m + 1) (by omega),
    IsPolarized_ofRank (k := 2 * n + 1) (by omega)]
  exact ⟨⟨hε, hε⟩, by rwa [ne_eq, ← GeneType.neg_eq_nonPolarized_iff]⟩

lemma X16_eq : (X16 h_le hε).1 =
  Gene.ofRank (2 * m + 1) ε + Gene.ofRank (2 * m + 1) ε +
  Gene.ofRank (2 * n + 1) (- ε) := rfl

@[simp] lemma neg_X16 :
    - (X16 h_le hε) = X16 h_le (GeneType.neg_ne_nonPolarized_iff.1 hε) := by
  apply Subtype.ext
  simp only [Mix.tLambda_Pi_neg_val, X16_eq, Chromosome.neg_add, neg_ofRank, neg_neg]

noncomputable def Y16 : Mix (2 • Lambda, Pi) := by
  have _ := h_le
  have _ := hε
  refine ⟨Gene.ofRank (2 * m) GeneType.NonPolarized +
    Gene.ofRank (2 * m) GeneType.NonPolarized +
    Gene.ofRank (2 * n + 3) ε, ?_⟩
  rw [mem_Mix_iff, map_add, map_add, map_add, map_add,
    evenPart_ofRank, if_pos (by grind), evenPart_ofRank, if_neg (by grind),
    oddPart_ofRank, if_pos (by grind), oddPart_ofRank, if_neg (by grind), add_zero]
  match m with
  | 0 =>
    simp only [Nat.mul_zero, Gene.ofRank_zero, zero_add, add_zero]
    refine ⟨zero_mem _, ?_⟩
    rw [mem_Pi_iff, IsPolarized_ofRank (k := 2 * n + 3) (by omega)]
    exact hε
  | m + 1 =>
    refine ⟨?_, ?_⟩
    · rw [AddSubmonoid.mem_smul_pointwise_iff_exists]
      refine ⟨Gene.ofRank (2 * (m + 1)) GeneType.NonPolarized, ?_, ?_⟩
      · rw [mem_Lambda_iff, IsNonPolarized_ofRank (k := 2 * (m + 1)) (by omega)]
      · rw [two_smul]
    · rw [mem_Pi_iff, zero_add, zero_add, IsPolarized_ofRank (by omega)]
      exact hε

lemma Y16_eq : (Y16 h_le hε).1 =
  Gene.ofRank (2 * m) GeneType.NonPolarized +
  Gene.ofRank (2 * m) GeneType.NonPolarized +
  Gene.ofRank (2 * n + 3) ε := rfl

@[simp] lemma neg_Y16 :
    - (Y16 h_le hε) = Y16 h_le (GeneType.neg_ne_nonPolarized_iff.1 hε) := by
  apply Subtype.ext
  simp only [Mix.tLambda_Pi_neg_val, Y16_eq, Chromosome.neg_add, neg_ofRank,
    GeneType.neg_nonPolarized]

end type16

end Mix2LambdaPi

end MixDefs
