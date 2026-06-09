import YoungDiagram.Variety

open Chromosome Pointwise

variable {ε : GeneType} {m n : ℕ}

-- Φ = (Π, 2 • Λ): g ranks odd, g^ε ranks even. Equation (8.14):
-- 2 g^ε(m) + 2 g^{-ε}(n) → 2 g(m-1) + 2 g(n+1)
-- with m = 2m+2 and n = 2n+2 even (parametrized by m, n : ℕ).

local notation "type14X" =>
  Gene.ofRank (2 * m + 2) ε +
  Gene.ofRank (2 * m + 2) ε +
  Gene.ofRank (2 * n + 2) (- ε) +
  Gene.ofRank (2 * n + 2) (- ε)
local notation "type14Y" =>
  Gene.ofRank (2 * m + 1) GeneType.NonPolarized +
  Gene.ofRank (2 * m + 1) GeneType.NonPolarized +
  Gene.ofRank (2 * n + 3) GeneType.NonPolarized +
  Gene.ofRank (2 * n + 3) GeneType.NonPolarized

variable (h_le : m ≤ n)

section Aux

namespace MixPi2Lambda

section type14_isMutation

lemma mutation_type14_ne : type14X ≠ type14Y := by
  intro h
  -- Apply both sides to (2n+3, NP); LHS is 0 (all polarized), RHS ≥ 2.
  replace h := congr_arg (· ⟨2 * n + 3, .NonPolarized, by omega⟩) h
  have h2m2 : 2 * m + 2 ≠ 0 := by omega
  have h2n2 : 2 * n + 2 ≠ 0 := by omega
  have h2n3 : 2 * n + 3 ≠ 0 := by omega
  have lhs_zero : (Gene.ofRank (2 * m + 2) ε +
      Gene.ofRank (2 * m + 2) ε +
      Gene.ofRank (2 * n + 2) (- ε) +
      Gene.ofRank (2 * n + 2) (- ε) : Chromosome)
        ⟨2 * n + 3, .NonPolarized, by omega⟩ = 0 := by
    simp only [Gene.ofRank_def, h2m2, h2n2, ↓reduceDIte,
      Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply,
      Gene.mk.injEq]
    split_ifs <;> first | rfl | (exfalso; omega)
  have rhs_ge : (Gene.ofRank (2 * m + 1) GeneType.NonPolarized +
      Gene.ofRank (2 * m + 1) GeneType.NonPolarized +
      Gene.ofRank (2 * n + 3) GeneType.NonPolarized +
      Gene.ofRank (2 * n + 3) GeneType.NonPolarized : Chromosome)
        ⟨2 * n + 3, .NonPolarized, by omega⟩ ≥ 2 := by
    have val2n3 :
        (Gene.ofRank (2 * n + 3) GeneType.NonPolarized : Chromosome)
          ⟨2 * n + 3, .NonPolarized, by omega⟩ = 1 := by
      simp only [Gene.ofRank_def, h2n3, ↓reduceDIte,
        Finsupp.single_apply, if_true]
    simp only [Finsupp.coe_add, Pi.add_apply, val2n3]
    omega
  rw [lhs_zero] at h
  omega

omit h_le in
private lemma sig_eps_neg_eps_eq (a : ℕ) (ε : GeneType) :
    (Gene.ofRank a ε).signature +
      (Gene.ofRank a (- ε)).signature =
    ((a : ℚ), (a : ℚ)) := by
  have h := signature_sum_ofRank_neg_eq_rank (k := a) (ε := ε)
  rw [h]
  rfl

omit h_le in
private lemma sig_two_NP_eq (a : ℕ) :
    (Gene.ofRank a GeneType.NonPolarized).signature +
      (Gene.ofRank a GeneType.NonPolarized).signature =
    ((a : ℚ), (a : ℚ)) := by
  rw [signature_ofRank_nonPolarized, Prod.mk_add_mk]
  refine Prod.mk.injEq .. |>.mpr ⟨?_, ?_⟩ <;> ring

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

omit h_le in
lemma mutation_type14_iterate_signature_eq (i j : ℕ) (hi : i ≤ j) :
    (prime^[i] (Gene.ofRank (2 * m + 2 + j) ε +
      Gene.ofRank (2 * m + 2 + j) ε +
      Gene.ofRank (2 * n + 2 + j) (- ε) +
      Gene.ofRank (2 * n + 2 + j) (- ε))).signature =
    (prime^[i] (Gene.ofRank (2 * m + 1 + j) GeneType.NonPolarized +
      Gene.ofRank (2 * m + 1 + j) GeneType.NonPolarized +
      Gene.ofRank (2 * n + 3 + j) GeneType.NonPolarized +
      Gene.ofRank (2 * n + 3 + j) GeneType.NonPolarized)).signature := by
  have le1 : i ≤ 2 * m + 2 + j := by omega
  have le2 : i ≤ 2 * n + 2 + j := by omega
  have le3 : i ≤ 2 * n + 3 + j := by omega
  have le4 : i ≤ 2 * m + 1 + j := by omega
  simp only [iterate_map_add, prime_iterate_ofRank, map_add]
  -- Group LHS as (sig(2m+2+j-i, ε) + sig(2n+2+j-i, -ε)) + (same).
  -- Even((2m+2+j-i) + (2n+2+j-i)) = Even(2(m+n+2+j-i)).
  have ev_lhs : Even ((2 * m + 2 + j - i) + (2 * n + 2 + j - i)) := by
    use (m + n + 2 + j - i)
    omega
  rw [show
      (Gene.ofRank (2 * m + 2 + j - i) ε).signature +
            (Gene.ofRank (2 * m + 2 + j - i) ε).signature +
            (Gene.ofRank (2 * n + 2 + j - i) (- ε)).signature +
          (Gene.ofRank (2 * n + 2 + j - i) (- ε)).signature =
        ((Gene.ofRank (2 * m + 2 + j - i) ε).signature +
          (Gene.ofRank (2 * n + 2 + j - i) (- ε)).signature) +
        ((Gene.ofRank (2 * m + 2 + j - i) ε).signature +
          (Gene.ofRank (2 * n + 2 + j - i) (- ε)).signature) by ring,
      signature_ofRank_sum_even ev_lhs,
      show
        (Gene.ofRank (2 * m + 1 + j - i) GeneType.NonPolarized).signature +
              (Gene.ofRank (2 * m + 1 + j - i) GeneType.NonPolarized).signature +
              (Gene.ofRank (2 * n + 3 + j - i) GeneType.NonPolarized).signature +
            (Gene.ofRank (2 * n + 3 + j - i) GeneType.NonPolarized).signature =
          ((Gene.ofRank (2 * m + 1 + j - i) GeneType.NonPolarized).signature +
            (Gene.ofRank (2 * m + 1 + j - i) GeneType.NonPolarized).signature) +
          ((Gene.ofRank (2 * n + 3 + j - i) GeneType.NonPolarized).signature +
            (Gene.ofRank (2 * n + 3 + j - i) GeneType.NonPolarized).signature) by ring,
      sig_two_NP_eq, sig_two_NP_eq, Prod.mk_add_mk, Prod.mk_add_mk]
  refine Prod.mk.injEq .. |>.mpr ⟨?_, ?_⟩ <;>
    (rw [Nat.cast_sub le1, Nat.cast_sub le2, Nat.cast_sub le4, Nat.cast_sub le3]
     push_cast; ring)

lemma mutation_type14_signature_eq :
    signature type14X = signature type14Y := by
  have := mutation_type14_iterate_signature_eq (ε := ε) (m := m) (n := n) 0 0 le_rfl
  rwa [Function.iterate_zero_apply, Function.iterate_zero_apply, add_zero, add_zero] at this

include h_le in
lemma mutation_type14_le : type14X ≤ type14Y := by
  intro k
  simp only [iterate_map_add, map_add, prime_iterate_ofRank]
  by_cases hk1 : 2 * n + 3 < k
  · -- All four ranks on both sides are 0.
    have eq1 : 2 * m + 2 - k = 0 := by omega
    have eq2 : 2 * n + 2 - k = 0 := by omega
    have eq3 : 2 * m + 1 - k = 0 := by omega
    have eq4 : 2 * n + 3 - k = 0 := by omega
    simp only [eq1, eq2, eq3, eq4, Gene.ofRank_zero, map_zero, add_zero]
    exact le_refl _
  by_cases hk2 : 2 * n + 2 < k
  · -- k = 2n+3. LHS all zero, RHS first 2 zero, last 2 nonzero.
    have eq1 : 2 * m + 2 - k = 0 := by omega
    have eq2 : 2 * n + 2 - k = 0 := by omega
    have eq3 : 2 * m + 1 - k = 0 := by omega
    have eq4 : 2 * n + 3 - k = 0 := by omega
    simp only [eq1, eq2, eq3, eq4, Gene.ofRank_zero, map_zero, add_zero]
    exact le_refl _
  by_cases hk3 : 2 * m + 2 < k
  · -- 2m+2 < k ≤ 2n+2. LHS: 2m+2-k=0, 2n+2-k>0. RHS: 2m+1-k=0, 2n+3-k>0.
    have eq1 : 2 * m + 2 - k = 0 := by omega
    have eq3 : 2 * m + 1 - k = 0 := by omega
    have le2 : k ≤ 2 * n + 2 := by omega
    have le3 : k ≤ 2 * n + 3 := by omega
    rw [eq1, eq3]
    simp only [Gene.ofRank_zero, map_zero, zero_add, add_zero]
    -- Goal: sig(2n+2-k, -ε) + sig(2n+2-k, -ε) ≤ sig(2n+3-k, NP) + sig(2n+3-k, NP)
    rw [signature_ofRank_nonPolarized]
    have hbound_fst := sig_bound_fst (2 * n + 2 - k) (-ε)
    have hbound_snd := sig_bound_snd (2 * n + 2 - k) (-ε)
    have h2 : 2 * n + 3 - k = 2 * n + 2 - k + 1 := by omega
    rw [h2]
    refine ⟨?_, ?_⟩
    · simp only [Prod.fst_add, Prod.mk_add_mk]
      have h1 : ((2 * n + 2 - k + 1 : ℕ) : ℚ) / 2 + ((2 * n + 2 - k + 1 : ℕ) : ℚ) / 2 =
          ((2 * n + 2 - k : ℕ) : ℚ) + 1 := by push_cast; ring
      rw [h1]
      have hub := hbound_fst.2
      linarith
    · simp only [Prod.snd_add, Prod.mk_add_mk]
      have h1 : ((2 * n + 2 - k + 1 : ℕ) : ℚ) / 2 + ((2 * n + 2 - k + 1 : ℕ) : ℚ) / 2 =
          ((2 * n + 2 - k : ℕ) : ℚ) + 1 := by push_cast; ring
      rw [h1]
      have hub := hbound_snd.2
      linarith
  · -- k ≤ 2m+2. Compute via sum_even or use bounds.
    have le1 : k ≤ 2 * m + 2 := by omega
    have le2 : k ≤ 2 * n + 2 := by omega
    have le3 : k ≤ 2 * n + 3 := by omega
    by_cases hk4 : k ≤ 2 * m + 1
    · -- All four ranks ≥ 0. Use sum_even on (2m+2-k, ε) + (2n+2-k, -ε).
      have ev_lhs : Even ((2 * m + 2 - k) + (2 * n + 2 - k)) := by
        use (m + n + 2 - k); omega
      rw [show
            (Gene.ofRank (2 * m + 2 - k) ε).signature +
                  (Gene.ofRank (2 * m + 2 - k) ε).signature +
                  (Gene.ofRank (2 * n + 2 - k) (- ε)).signature +
                (Gene.ofRank (2 * n + 2 - k) (- ε)).signature =
              ((Gene.ofRank (2 * m + 2 - k) ε).signature +
                (Gene.ofRank (2 * n + 2 - k) (- ε)).signature) +
              ((Gene.ofRank (2 * m + 2 - k) ε).signature +
                (Gene.ofRank (2 * n + 2 - k) (- ε)).signature) by ring,
          signature_ofRank_sum_even ev_lhs,
          show
            (Gene.ofRank (2 * m + 1 - k) GeneType.NonPolarized).signature +
                  (Gene.ofRank (2 * m + 1 - k) GeneType.NonPolarized).signature +
                  (Gene.ofRank (2 * n + 3 - k) GeneType.NonPolarized).signature +
                (Gene.ofRank (2 * n + 3 - k) GeneType.NonPolarized).signature =
              ((Gene.ofRank (2 * m + 1 - k) GeneType.NonPolarized).signature +
                (Gene.ofRank (2 * m + 1 - k) GeneType.NonPolarized).signature) +
              ((Gene.ofRank (2 * n + 3 - k) GeneType.NonPolarized).signature +
                (Gene.ofRank (2 * n + 3 - k) GeneType.NonPolarized).signature) by ring,
          sig_two_NP_eq, sig_two_NP_eq, Prod.mk_add_mk, Prod.mk_add_mk]
      simp only [Prod.mk_le_mk]
      refine ⟨?_, ?_⟩ <;>
        (rw [Nat.cast_sub le1, Nat.cast_sub le2, Nat.cast_sub hk4, Nat.cast_sub le3]
         push_cast; linarith)
    · -- k = 2m+2. 2m+1-k = 0, 2m+2-k = 0.
      have hzero : 2 * m + 1 - k = 0 := by omega
      have hone : 2 * m + 2 - k = 0 := by omega
      rw [hzero, hone]
      simp only [Gene.ofRank_zero, map_zero, zero_add, add_zero]
      -- Goal: 2 sig(2n+2-k, -ε) ≤ 2 sig(2n+3-k, NP)
      rw [signature_ofRank_nonPolarized]
      have hbound_fst := sig_bound_fst (2 * n + 2 - k) (-ε)
      have hbound_snd := sig_bound_snd (2 * n + 2 - k) (-ε)
      have h2 : 2 * n + 3 - k = 2 * n + 2 - k + 1 := by omega
      rw [h2]
      refine ⟨?_, ?_⟩
      · simp only [Prod.fst_add, Prod.mk_add_mk]
        have hub := hbound_fst.2
        have h1 : ((2 * n + 2 - k + 1 : ℕ) : ℚ) / 2 + ((2 * n + 2 - k + 1 : ℕ) : ℚ) / 2 =
            ((2 * n + 2 - k : ℕ) : ℚ) + 1 := by push_cast; ring
        rw [h1]
        linarith
      · simp only [Prod.snd_add, Prod.mk_add_mk]
        have hub := hbound_snd.2
        have h1 : ((2 * n + 2 - k + 1 : ℕ) : ℚ) / 2 + ((2 * n + 2 - k + 1 : ℕ) : ℚ) / 2 =
            ((2 * n + 2 - k : ℕ) : ℚ) + 1 := by push_cast; ring
        rw [h1]
        linarith

end type14_isMutation

end MixPi2Lambda

end Aux

section MixDefs

open Variety

namespace MixPi2Lambda

variable (hε : ε ≠ .NonPolarized)

include h_le

section type14

noncomputable def X14 : Mix (Pi, 2 • Lambda) := by
  have _ := h_le
  have _ := hε
  refine ⟨Gene.ofRank (2 * m + 2) ε +
    Gene.ofRank (2 * m + 2) ε +
    Gene.ofRank (2 * n + 2) (- ε) +
    Gene.ofRank (2 * n + 2) (- ε), ?_⟩
  rw [mem_Mix_iff, map_add, map_add, map_add, map_add, map_add, map_add,
    evenPart_ofRank, if_pos (by grind),
    evenPart_ofRank, if_pos (by grind),
    oddPart_ofRank, if_pos (by grind),
    oddPart_ofRank, if_pos (by grind),
    add_zero, add_zero, add_zero]
  refine ⟨?_, zero_mem _⟩
  rw [mem_Pi_iff_add, mem_Pi_iff_add, mem_Pi_iff_add, mem_Pi_iff, mem_Pi_iff,
    IsPolarized_ofRank (k := 2 * m + 2) (ε := ε) (by omega),
    IsPolarized_ofRank (k := 2 * n + 2) (ε := -ε) (by omega)]
  have hne : (-ε) ≠ .NonPolarized := by rwa [ne_eq, ← GeneType.neg_eq_nonPolarized_iff]
  exact ⟨⟨⟨hε, hε⟩, hne⟩, hne⟩

lemma X14_eq : (X14 h_le hε).1 =
  Gene.ofRank (2 * m + 2) ε +
  Gene.ofRank (2 * m + 2) ε +
  Gene.ofRank (2 * n + 2) (- ε) +
  Gene.ofRank (2 * n + 2) (- ε) := rfl

@[simp] lemma neg_X14 :
    - (X14 h_le hε) = X14 h_le (GeneType.neg_ne_nonPolarized_iff.1 hε) := by
  apply Subtype.ext
  rw [Mix.Pi_2Lambda_neg_val, X14_eq, X14_eq,
    Chromosome.neg_add, Chromosome.neg_add, Chromosome.neg_add,
    neg_ofRank, neg_ofRank, neg_neg]

noncomputable def Y14 : Mix (Pi, 2 • Lambda) := by
  have _ := h_le
  have _ := hε
  refine ⟨Gene.ofRank (2 * m + 1) GeneType.NonPolarized +
    Gene.ofRank (2 * m + 1) GeneType.NonPolarized +
    Gene.ofRank (2 * n + 3) GeneType.NonPolarized +
    Gene.ofRank (2 * n + 3) GeneType.NonPolarized, ?_⟩
  have odd_m : ¬ Even (2 * m + 1) := by rw [Nat.not_even_iff_odd]; exact ⟨m, rfl⟩
  have odd_n : ¬ Even (2 * n + 3) := by
    rw [Nat.not_even_iff_odd]; exact ⟨n + 1, by ring⟩
  rw [mem_Mix_iff, map_add, map_add, map_add, map_add, map_add, map_add,
    evenPart_ofRank, if_neg (by grind),
    evenPart_ofRank, if_neg (by grind),
    oddPart_ofRank, if_neg (by grind),
    oddPart_ofRank, if_neg (by grind),
    add_zero, add_zero, zero_add]
  refine ⟨zero_mem _, ?_⟩
  rw [AddSubmonoid.mem_smul_pointwise_iff_exists]
  refine ⟨Gene.ofRank (2 * m + 1) GeneType.NonPolarized +
    Gene.ofRank (2 * n + 3) GeneType.NonPolarized, ?_, ?_⟩
  · rw [mem_Lambda_iff_add, mem_Lambda_iff, mem_Lambda_iff,
      IsNonPolarized_ofRank (k := 2 * m + 1) (by omega),
      IsNonPolarized_ofRank (k := 2 * n + 3) (by omega)]
    exact ⟨rfl, rfl⟩
  · rw [two_smul]; abel

lemma Y14_eq : (Y14 h_le hε).1 =
  Gene.ofRank (2 * m + 1) GeneType.NonPolarized +
  Gene.ofRank (2 * m + 1) GeneType.NonPolarized +
  Gene.ofRank (2 * n + 3) GeneType.NonPolarized +
  Gene.ofRank (2 * n + 3) GeneType.NonPolarized := rfl

@[simp] lemma neg_Y14 :
    - (Y14 h_le hε) = Y14 h_le (GeneType.neg_ne_nonPolarized_iff.1 hε) := by
  apply Subtype.ext
  rw [Mix.Pi_2Lambda_neg_val, Y14_eq, Y14_eq,
    Chromosome.neg_add, Chromosome.neg_add, Chromosome.neg_add]
  simp only [neg_ofRank, GeneType.neg_nonPolarized]

end type14

end MixPi2Lambda

end MixDefs
