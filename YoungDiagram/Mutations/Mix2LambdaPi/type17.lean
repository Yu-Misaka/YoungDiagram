import YoungDiagram.Variety

open Chromosome Pointwise

variable {ε : GeneType} {m n : ℕ}

-- Φ = (2 • Λ, Π): g ranks even, g^ε ranks odd. Equation (8.17):
-- g^ε(m_paper) + 2 g^{-ε}(n_paper) → g^{-ε}(m_paper - 2) + 2 g(n_paper + 1)
-- with m_paper = 2 m + 3, n_paper = 2 n + 3 (both odd, ≥ 3).

local notation "type17X" =>
  Gene.ofRank (2 * m + 3) ε +
  Gene.ofRank (2 * n + 3) (- ε) +
  Gene.ofRank (2 * n + 3) (- ε)
local notation "type17Y" =>
  Gene.ofRank (2 * m + 1) (- ε) +
  Gene.ofRank (2 * n + 4) GeneType.NonPolarized +
  Gene.ofRank (2 * n + 4) GeneType.NonPolarized

variable (h_le : m ≤ n)

include h_le

section Aux

namespace Mix2LambdaPi

section type17_isMutation

omit h_le in
lemma mutation_type17_ne : type17X ≠ type17Y := by
  intro h
  replace h := congr_arg (· ⟨2 * n + 3, - ε, by omega⟩) h
  have h_m : 2 * m + 3 ≠ 0 := by omega
  have h_n : 2 * n + 3 ≠ 0 := by omega
  have h_m' : 2 * m + 1 ≠ 0 := by omega
  have h_n' : 2 * n + 4 ≠ 0 := by omega
  simp only [Gene.ofRank_def, h_m, h_n, h_m', h_n', ↓reduceDIte, Finsupp.coe_add,
    Pi.add_apply, Finsupp.single_eq_same, Finsupp.single_apply, Gene.mk.injEq,
    Nat.reduceEqDiff, Nat.add_left_cancel_iff, and_true, false_and] at h
  split_ifs at h <;> omega

omit h_le in
private lemma mutation_type17_sig_eq_aux (p d : ℕ) :
    (Gene.ofRank (2 * p + 3 + d) ε).signature +
      (Gene.ofRank (2 * (p + (n - m)) + 3 + d) (- ε)).signature +
      (Gene.ofRank (2 * (p + (n - m)) + 3 + d) (- ε)).signature =
    (Gene.ofRank (2 * p + 1 + d) (- ε)).signature +
      (Gene.ofRank (2 * (p + (n - m)) + 4 + d) .NonPolarized).signature +
      (Gene.ofRank (2 * (p + (n - m)) + 4 + d) .NonPolarized).signature := by
  set A := 2 * p + d
  set B := 2 * (p + (n - m)) + 2 + d
  have heven : Even (A + B) := by
    refine ⟨p + (p + (n - m)) + 1 + d, ?_⟩
    change 2 * p + d + (2 * (p + (n - m)) + 2 + d) = _
    ring
  -- (1) s(A+1, ε) + s(B+1, -ε) = s(A, NP) + s(B+2, NP)
  have h1 :
      (Gene.ofRank (A + 1) ε).signature + (Gene.ofRank (B + 2 - 1) (- ε)).signature =
      (Gene.ofRank A .NonPolarized).signature + (Gene.ofRank (B + 2) .NonPolarized).signature :=
    signature_ofRank_succ_add_pred_neg (by omega)
      (by rw [show A + (B + 2) = (A + B) + 2 from by ring]; exact heven.add (⟨1, rfl⟩))
  -- (2) s(A+1, -ε) + s(B, NP) = s(A, NP) + s(B+1, -ε), via succ_add_nonPolarized with ε := -ε
  have h2 :
      (Gene.ofRank (A + 1) (- ε)).signature + (Gene.ofRank B .NonPolarized).signature =
      (Gene.ofRank A .NonPolarized).signature + (Gene.ofRank (B + 1) (- ε)).signature :=
    signature_ofRank_succ_add_nonPolarized heven
  -- (3) s(B+2, NP) = s(B, NP) + (1, 1)
  have h3 :
      (Gene.ofRank (B + 2) .NonPolarized).signature =
      (Gene.ofRank B .NonPolarized).signature + (1, 1) :=
    signature_ofRank_eq₂' B
  -- (4) s(A+3, ε) = s(A+1, ε) + (1, 1)
  have h4 :
      (Gene.ofRank (A + 3) ε).signature =
      (Gene.ofRank (A + 1) ε).signature + (1, 1) := by
    have := signature_ofRank_eq₂' (k := A + 1) (ε := ε)
    rw [show A + 1 + 2 = A + 3 from by ring] at this
    exact this
  -- Identify the abbreviations
  have hA1 : A + 1 = 2 * p + 1 + d := by change 2 * p + d + 1 = _; ring
  have hA3 : A + 3 = 2 * p + 3 + d := by change 2 * p + d + 3 = _; ring
  have hB1 : B + 2 - 1 = 2 * (p + (n - m)) + 3 + d := by
    change 2 * (p + (n - m)) + 2 + d + 2 - 1 = _; omega
  have hB1' : B + 1 = 2 * (p + (n - m)) + 3 + d := by
    change 2 * (p + (n - m)) + 2 + d + 1 = _; ring
  have hB2 : B + 2 = 2 * (p + (n - m)) + 4 + d := by
    change 2 * (p + (n - m)) + 2 + d + 2 = _; ring
  -- Don't rewrite h_i's with the hA/hB equalities; instead, do calc using A,B abbreviations,
  -- then convert at the end. Rewrite the LHS/RHS into A,B form.
  rw [← hA3, ← hB1', ← hA1, ← hB2]
  -- Goal: s(A+3, ε) + s(B+1, -ε) + s(B+1, -ε) = s(A+1, -ε) + s(B+2, NP) + s(B+2, NP)
  calc (Gene.ofRank (A + 3) ε).signature + (Gene.ofRank (B + 1) (- ε)).signature
          + (Gene.ofRank (B + 1) (- ε)).signature
      = (Gene.ofRank (A + 1) ε).signature + (1, 1) + (Gene.ofRank (B + 1) (- ε)).signature
          + (Gene.ofRank (B + 1) (- ε)).signature := by rw [h4]
    _ = ((Gene.ofRank (A + 1) ε).signature + (Gene.ofRank (B + 2 - 1) (- ε)).signature)
          + (Gene.ofRank (B + 1) (- ε)).signature + (1, 1) := by
        have : B + 2 - 1 = B + 1 := by show B + 2 - 1 = B + 1; omega
        rw [this]; abel
    _ = ((Gene.ofRank A .NonPolarized).signature + (Gene.ofRank (B + 2) .NonPolarized).signature)
          + (Gene.ofRank (B + 1) (- ε)).signature + (1, 1) := by rw [h1]
    _ = (Gene.ofRank A .NonPolarized).signature + (Gene.ofRank (B + 2) .NonPolarized).signature
          + ((Gene.ofRank (A + 1) (- ε)).signature + (Gene.ofRank B .NonPolarized).signature
            - (Gene.ofRank A .NonPolarized).signature) + (1, 1) := by
        have h2' : (Gene.ofRank (B + 1) (- ε)).signature =
            (Gene.ofRank (A + 1) (- ε)).signature + (Gene.ofRank B .NonPolarized).signature
              - (Gene.ofRank A .NonPolarized).signature := by
          rw [h2]; abel
        rw [h2']
    _ = (Gene.ofRank (B + 2) .NonPolarized).signature
          + (Gene.ofRank (A + 1) (- ε)).signature
          + (Gene.ofRank B .NonPolarized).signature + (1, 1) := by abel
    _ = (Gene.ofRank (B + 2) .NonPolarized).signature
          + (Gene.ofRank (A + 1) (- ε)).signature
          + ((Gene.ofRank (B + 2) .NonPolarized).signature - (1, 1)) + (1, 1) := by
        have h3' : (Gene.ofRank B .NonPolarized).signature =
            (Gene.ofRank (B + 2) .NonPolarized).signature - (1, 1) := by rw [h3]; abel
        rw [h3']
    _ = (Gene.ofRank (A + 1) (- ε)).signature
          + (Gene.ofRank (B + 2) .NonPolarized).signature
          + (Gene.ofRank (B + 2) .NonPolarized).signature := by abel

lemma mutation_type17_iterate_signature_eq (i j : ℕ) (hi : i ≤ j) :
    (prime^[i] (Gene.ofRank (2 * m + 3 + j) ε +
        Gene.ofRank (2 * n + 3 + j) (- ε) +
        Gene.ofRank (2 * n + 3 + j) (- ε))).signature =
    (prime^[i] (Gene.ofRank (2 * m + 1 + j) (- ε) +
        Gene.ofRank (2 * n + 4 + j) .NonPolarized +
        Gene.ofRank (2 * n + 4 + j) .NonPolarized)).signature := by
  simp only [iterate_map_add, map_add, prime_iterate_ofRank]
  have eq1 : 2 * m + 3 + j - i = 2 * m + 3 + (j - i) := by omega
  have eq2 : 2 * n + 3 + j - i = 2 * (m + (n - m)) + 3 + (j - i) := by
    have : 2 * (m + (n - m)) = 2 * n := by omega
    omega
  have eq3 : 2 * m + 1 + j - i = 2 * m + 1 + (j - i) := by omega
  have eq4 : 2 * n + 4 + j - i = 2 * (m + (n - m)) + 4 + (j - i) := by
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
  · -- equality from aux with p = (2m-i)/2, d = (2m-i)%2 -- but here ranks start at 2m+3,
    -- so we want 2p + d = 2m - i, giving 2p + 3 + d = 2m + 3 - i.
    have heq : (Gene.ofRank (2 * m + 3 - i) ε).signature +
        (Gene.ofRank (2 * n + 3 - i) (- ε)).signature +
        (Gene.ofRank (2 * n + 3 - i) (- ε)).signature =
      (Gene.ofRank (2 * m + 1 - i) (- ε)).signature +
        (Gene.ofRank (2 * n + 4 - i) .NonPolarized).signature +
        (Gene.ofRank (2 * n + 4 - i) .NonPolarized).signature := by
      have := mutation_type17_sig_eq_aux (n := n) (m := m) (ε := ε)
        ((2 * m - i) / 2) ((2 * m - i) % 2)
      have eq1 : 2 * ((2 * m - i) / 2) + 3 + (2 * m - i) % 2 = 2 * m + 3 - i := by omega
      have eq2 : 2 * ((2 * m - i) / 2 + (n - m)) + 3 + (2 * m - i) % 2 = 2 * n + 3 - i := by
        have : 2 * (n - m) = 2 * n - 2 * m := by omega
        omega
      have eq3 : 2 * ((2 * m - i) / 2) + 1 + (2 * m - i) % 2 = 2 * m + 1 - i := by omega
      have eq4 : 2 * ((2 * m - i) / 2 + (n - m)) + 4 + (2 * m - i) % 2 = 2 * n + 4 - i := by
        have : 2 * (n - m) = 2 * n - 2 * m := by omega
        omega
      rw [eq1, eq2, eq3, eq4] at this
      exact this
    rw [heq]
  · push Not at hi1
    by_cases hi2 : i ≤ 2 * m + 1
    · -- i = 2m + 1, then s(2m+3-i, ε) = s(2, ε), s(2m+1-i, -ε) = s(0, -ε) = 0
      -- s(2n+3-i, -ε) = s(2n+2, -ε) (even rank), s(2n+4-i, NP) = s(2n+3, NP)
      have hi3 : i = 2 * m + 1 := by omega
      subst hi3
      have e1 : 2 * m + 3 - (2 * m + 1) = 2 := by omega
      have e2 : 2 * n + 3 - (2 * m + 1) = 2 * (n - m) + 2 := by omega
      have e3 : 2 * m + 1 - (2 * m + 1) = 0 := by omega
      have e4 : 2 * n + 4 - (2 * m + 1) = 2 * (n - m) + 3 := by omega
      simp only [e1, e2, e3, e4, Gene.ofRank_zero, map_zero, zero_add]
      -- Goal: s(2, ε) + 2 · s(2(n-m)+2, -ε) ≤ 2 · s(2(n-m)+3, NP)
      -- s(2, ε) = (1, 1), s(2j+2, -ε) = (j+1, j+1) (even half),
      -- s(2(n-m)+3, NP) = ((2(n-m)+3)/2, ...)
      have h_eq₂ : (Gene.ofRank 2 ε).signature = ((1 : ℚ), (1 : ℚ)) := by
        rw [signature_ofRank_even_half (by exact ⟨1, rfl⟩)]; push_cast; ring_nf
      have h_eq_even : (Gene.ofRank (2 * (n - m) + 2) (-ε)).signature =
          (((2 * (n - m) + 2 : ℕ) : ℚ) / 2, ((2 * (n - m) + 2 : ℕ) : ℚ) / 2) :=
        signature_ofRank_even_half ⟨n - m + 1, by ring⟩
      rw [h_eq₂, h_eq_even]
      simp only [signature_ofRank_nonPolarized]
      push_cast
      constructor
      · simp only [Prod.fst_add]; linarith
      · simp only [Prod.snd_add]; linarith
    · push Not at hi2
      by_cases hi3 : i ≤ 2 * n + 3
      · have e1 : 2 * m + 3 - i = 0 ∨ 2 * m + 3 - i = 1 := by omega
        have e3 : 2 * m + 1 - i = 0 := by omega
        rw [e3, Gene.ofRank_zero, map_zero, zero_add]
        rcases e1 with e1 | e1
        · rw [e1, Gene.ofRank_zero, map_zero, zero_add]
          -- Goal: 2 · s(2n+3-i, -ε) ≤ 2 · s(2n+4-i, NP)
          -- We have i ≥ 2m+3, so 2n+3-i ≤ 2(n-m), and 2n+4-i = (2n+3-i)+1.
          -- Use that s(k+1, NP) = ((k+1)/2, (k+1)/2) ≥ s(k, -ε).
          have heq2n : 2 * n + 4 - i = (2 * n + 3 - i) + 1 := by omega
          rw [heq2n]
          simp only [signature_ofRank_nonPolarized]
          have hle := signature_ofRank_le (ε := -ε) (k := 2 * n + 3 - i)
          push_cast
          constructor
          · simp only [Prod.fst_add]
            have : (Gene.ofRank (2 * n + 3 - i) (-ε)).signature.1 ≤
                (((2 * n + 3 - i : ℕ) : ℚ) + 1) / 2 := hle.1
            linarith
          · simp only [Prod.snd_add]
            have : (Gene.ofRank (2 * n + 3 - i) (-ε)).signature.2 ≤
                (((2 * n + 3 - i : ℕ) : ℚ) + 1) / 2 := hle.2
            linarith
        · -- 2m + 3 - i = 1, so i = 2m + 2
          have hi_eq : i = 2 * m + 2 := by omega
          subst hi_eq
          have e1' : 2 * m + 3 - (2 * m + 2) = 1 := by omega
          have e2 : 2 * n + 3 - (2 * m + 2) = 2 * (n - m) + 1 := by omega
          have e4 : 2 * n + 4 - (2 * m + 2) = 2 * (n - m) + 2 := by omega
          simp only [e1', e2, e4]
          -- Goal: s(1, ε) + 2 · s(2(n-m)+1, -ε) ≤ 2 · s(2(n-m)+2, NP)
          -- s(2j+2, NP) = (j+1, j+1) (even half).
          -- s(2j+1, -ε) ≤ ((2j+1+1)/2, (2j+1+1)/2) = (j+1, j+1) by signature_ofRank_le.
          -- s(1, ε) ≥ 0 by signature_nonneg, but actually s(1, ε) ≤ (1, 1) at upper bound.
          -- The key: s(1, ε) + s(2j+1, -ε) = s(2j+2, NP)? Let's check with succ_add_nonPolarized:
          -- s(0+1, ε) + s(2j+1, NP) = s(0, NP) + s(2j+2, ε), nope.
          -- Use signature_ofRank_succ_add_pred_neg: s(m+1, ε) + s(n-1, -ε) = s(m, NP) + s(n, NP).
          -- With m = 0, n = 2(n-m)+2: s(1, ε) + s(2(n-m)+1, -ε) = s(0, NP) + s(2(n-m)+2, NP)
          --                                                     = 0 + s(2(n-m)+2, NP).
          have hsig : (Gene.ofRank 1 ε).signature +
              (Gene.ofRank (2 * (n - m) + 1) (- ε)).signature =
              (Gene.ofRank (2 * (n - m) + 2) GeneType.NonPolarized).signature := by
            have h := signature_ofRank_succ_add_pred_neg (ε := ε) (m := 0) (n := 2 * (n - m) + 2)
              (by omega) (by refine ⟨n - m + 1, ?_⟩; ring)
            simp only [Gene.ofRank_zero, map_zero, zero_add] at h
            have heq : 2 * (n - m) + 2 - 1 = 2 * (n - m) + 1 := by omega
            rw [heq] at h
            exact h
          -- Actually let's use direct rewriting instead of linarith trick.
          have hsig' : (Gene.ofRank (2 * (n - m) + 1) (- ε)).signature =
              (Gene.ofRank (2 * (n - m) + 2) GeneType.NonPolarized).signature -
              (Gene.ofRank 1 ε).signature := by
            rw [← hsig]; abel
          rw [hsig']
          -- Goal: s(1, ε) + 2 · (s(2(n-m)+2, NP) - s(1, ε)) ≤ 2 · s(2(n-m)+2, NP)
          -- = 2 · s(2(n-m)+2, NP) - s(1, ε) ≤ 2 · s(2(n-m)+2, NP)
          -- ⟺ 0 ≤ s(1, ε)
          have hnn := signature_nonneg (Gene.ofRank 1 ε)
          have hnn1 : (0 : ℚ) ≤ (Gene.ofRank 1 ε).signature.1 := hnn.1
          have hnn2 : (0 : ℚ) ≤ (Gene.ofRank 1 ε).signature.2 := hnn.2
          constructor
          · simp only [Prod.fst_add, Prod.fst_sub]; linarith
          · simp only [Prod.snd_add, Prod.snd_sub]; linarith
      · push Not at hi3
        have e1 : 2 * m + 3 - i = 0 := by omega
        have e2 : 2 * n + 3 - i = 0 := by omega
        have e3 : 2 * m + 1 - i = 0 := by omega
        by_cases hi4 : i ≤ 2 * n + 4
        · have e4_alt : 2 * n + 4 - i = 0 ∨ 2 * n + 4 - i = 1 := by omega
          rcases e4_alt with e4 | e4
          · simp only [e1, e2, e3, e4, Gene.ofRank_zero, map_zero, add_zero]
            exact le_refl _
          · simp only [e1, e2, e3, e4, Gene.ofRank_zero, map_zero, zero_add, add_zero]
            have h1 := signature_nonneg (Gene.ofRank 1 (GeneType.NonPolarized))
            exact add_nonneg h1 h1
        · push Not at hi4
          have e4 : 2 * n + 4 - i = 0 := by omega
          simp only [e1, e2, e3, e4, Gene.ofRank_zero, map_zero, add_zero]
          exact le_refl _

end type17_isMutation

end Mix2LambdaPi

end Aux

section MixDefs

open Variety

namespace Mix2LambdaPi

variable (hε : ε ≠ .NonPolarized)

include h_le

section type17

noncomputable def X17 : Mix (2 • Lambda, Pi) := by
  have _ := h_le
  refine ⟨Gene.ofRank (2 * m + 3) ε + Gene.ofRank (2 * n + 3) (- ε) +
    Gene.ofRank (2 * n + 3) (- ε), ?_⟩
  rw [mem_Mix_iff, map_add, map_add, map_add, map_add,
    evenPart_ofRank, if_neg (by grind),
    evenPart_ofRank, if_neg (by grind),
    oddPart_ofRank, if_neg (by grind),
    oddPart_ofRank, if_neg (by grind),
    zero_add, zero_add]
  refine ⟨zero_mem _, ?_⟩
  rw [mem_Pi_iff_add, mem_Pi_iff_add, mem_Pi_iff, mem_Pi_iff,
    IsPolarized_ofRank (k := 2 * m + 3) (by omega),
    IsPolarized_ofRank (k := 2 * n + 3) (by omega)]
  exact ⟨⟨hε, by rwa [ne_eq, ← GeneType.neg_eq_nonPolarized_iff]⟩,
    by rwa [ne_eq, ← GeneType.neg_eq_nonPolarized_iff]⟩

lemma X17_eq : (X17 h_le hε).1 =
  Gene.ofRank (2 * m + 3) ε + Gene.ofRank (2 * n + 3) (- ε) +
  Gene.ofRank (2 * n + 3) (- ε) := rfl

@[simp] lemma neg_X17 :
    - (X17 h_le hε) = X17 h_le (GeneType.neg_ne_nonPolarized_iff.1 hε) := by
  apply Subtype.ext
  simp only [Mix.tLambda_Pi_neg_val, X17_eq, Chromosome.neg_add, neg_ofRank, neg_neg]

noncomputable def Y17 : Mix (2 • Lambda, Pi) := by
  have _ := h_le
  have _ := hε
  refine ⟨Gene.ofRank (2 * m + 1) (- ε) +
    Gene.ofRank (2 * n + 4) GeneType.NonPolarized +
    Gene.ofRank (2 * n + 4) GeneType.NonPolarized, ?_⟩
  rw [mem_Mix_iff, map_add, map_add, map_add, map_add,
    evenPart_ofRank, if_neg (by grind),
    evenPart_ofRank, if_pos (by grind),
    oddPart_ofRank, if_neg (by grind),
    oddPart_ofRank, if_pos (by grind),
    zero_add, add_zero, add_zero]
  refine ⟨?_, ?_⟩
  · rw [AddSubmonoid.mem_smul_pointwise_iff_exists]
    refine ⟨Gene.ofRank (2 * n + 4) GeneType.NonPolarized, ?_, ?_⟩
    · rw [mem_Lambda_iff, IsNonPolarized_ofRank (k := 2 * n + 4) (by omega)]
    · rw [two_smul]
  · rw [mem_Pi_iff, IsPolarized_ofRank (k := 2 * m + 1) (by omega)]
    rwa [ne_eq, ← GeneType.neg_eq_nonPolarized_iff]

lemma Y17_eq : (Y17 h_le hε).1 =
  Gene.ofRank (2 * m + 1) (- ε) +
  Gene.ofRank (2 * n + 4) GeneType.NonPolarized +
  Gene.ofRank (2 * n + 4) GeneType.NonPolarized := rfl

@[simp] lemma neg_Y17 :
    - (Y17 h_le hε) = Y17 h_le (GeneType.neg_ne_nonPolarized_iff.1 hε) := by
  apply Subtype.ext
  simp only [Mix.tLambda_Pi_neg_val, Y17_eq, Chromosome.neg_add, neg_ofRank, neg_neg,
    GeneType.neg_nonPolarized]

end type17

end Mix2LambdaPi

end MixDefs
