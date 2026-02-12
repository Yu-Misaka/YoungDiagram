import YoungDiagram.Chromosome
import Mathlib.Tactic

open Chromosome

section type1_isMutation

lemma mutation_type1_ne {ε : GeneType}
  {m n : ℕ} (h_le : m ≤ n) (hm : 1 ≤ m) :
    (Gene.ofRank m ε + Gene.ofRank n (- ε)) ≠
    (Gene.ofRank (m - 1) (- ε) + Gene.ofRank (n + 1) ε) := by
  intro h
  replace h := congr_arg (· ⟨m, ε, hm⟩) h
  have h_n : n ≠ 0 := by omega
  have h_m : m ≠ 0 := by omega
  simp [h_n, h_m, Gene.ofRank_def] at h
  split_ifs at h <;> (simp [Finsupp.single_apply] at h; grind)

lemma mutation_type1_iterate_signature_eq {ε : GeneType} (hε : ε ≠ .NonPolarized)
  {m n : ℕ} (h_le : m ≤ n) (hm : 1 ≤ m) (i k : ℕ) (hi : i ≤ k) :
    (prime^[i] (Gene.ofRank (m + k) ε + Gene.ofRank (n + k) (- ε))).signature =
    (prime^[i] (Gene.ofRank (m + k - 1) (- ε) + Gene.ofRank (n + k + 1) ε)).signature := by
  rw [iterate_map_add, iterate_map_add, prime_iterate_ofRank, prime_iterate_ofRank,
      prime_iterate_ofRank, prime_iterate_ofRank, map_add, map_add]
  match ε, hε with
  | .Positive, _ =>
    rw [signature_ofRank_positive_eq (k := (m + k - i)) (by omega),
      signature_ofRank_positive_eq (k := (n + k + 1 - i)) (by omega),
      GeneType.neg_pos_eq_neg, Nat.sub_right_comm,
      show n + k + 1 - i - 1 = n + k - i by exact Nat.succ_sub_succ_eq_sub (n + k) i]
    ac_rfl
  | .Negative, _ =>
    rw [signature_ofRank_negative_eq (k := (m + k - i)) (by omega),
      signature_ofRank_negative_eq (k := (n + k + 1 - i)) (by omega),
      GeneType.neg_neg_eq_pos, Nat.sub_right_comm,
      show n + k + 1 - i - 1 = n + k - i by exact Nat.succ_sub_succ_eq_sub (n + k) i]
    ac_rfl

lemma mutation_type1_signature_eq {ε : GeneType} (hε : ε ≠ .NonPolarized)
  {m n : ℕ} (h_le : m ≤ n) (hm : 1 ≤ m) :
    (Gene.ofRank m ε + Gene.ofRank n (- ε)).signature =
    (Gene.ofRank (m - 1) (- ε) + Gene.ofRank (n + 1) ε).signature := by
  have := mutation_type1_iterate_signature_eq hε h_le hm 0 0 (le_of_eq rfl)
  rwa [Function.iterate_zero_apply, Function.iterate_zero_apply, add_zero, add_zero] at this

lemma mutation_type1_le_positive {m n : ℕ} (h_le : m ≤ n) :
    (Gene.ofRank m .Positive + Gene.ofRank n (- .Positive)) ≤
    (Gene.ofRank (m - 1) (- .Positive) + Gene.ofRank (n + 1) .Positive) := by
  rw [le_iff_dominates]
  intro k
  simp only [GeneType.neg_pos_eq_neg, iterate_map_add, map_add]
  repeat rw [prime_iterate_ofRank]
  by_cases hk1 : k < m
  · rw [signature_ofRank_positive_eq (by omega), signature_ofRank_positive_eq (by omega)]
    convert_to _ ≤
      (Gene.ofRank (m - k - 1) .Negative).signature +
      ((Gene.ofRank (n - k) .Negative).signature + (1, 0))
    · congr 3
      · omega
      · congr 1; omega
    abel_nf; rfl
  by_cases hk2 : k < n
  · rw [Nat.sub_right_comm, Nat.sub_eq_zero_of_le <| Nat.le_of_not_lt hk1,
      Nat.zero_sub, signature_ofRank_zero, signature_ofRank_zero, zero_add,
      zero_add, signature_ofRank_positive_eq (by omega)]
    convert_to _ ≤ (Gene.ofRank (n - k) .Negative).signature + (1, 0)
    · congr 3; omega
    simp; exact posPart_eq_self.mp rfl
  · rw [Nat.sub_right_comm, Nat.sub_eq_zero_of_le <| Nat.le_of_not_lt hk1,
      Nat.zero_sub, signature_ofRank_zero, signature_ofRank_zero, zero_add,
      zero_add, Nat.sub_eq_zero_of_le <| Nat.le_of_not_lt hk2,
      signature_ofRank_zero]
    exact signature_nonneg _

lemma mutation_type1_le_negative {m n : ℕ} (h_le : m ≤ n) :
    (Gene.ofRank m .Negative + Gene.ofRank n (- .Negative)) ≤
    (Gene.ofRank (m - 1) (- .Negative) + Gene.ofRank (n + 1) .Negative) := by
  rw [le_iff_dominates]
  intro k
  simp only [GeneType.neg_neg_eq_pos, iterate_map_add, map_add]
  repeat rw [prime_iterate_ofRank]
  by_cases hk1 : k < m
  · rw [signature_ofRank_negative_eq (by omega), signature_ofRank_negative_eq (by omega)]
    convert_to _ ≤
      (Gene.ofRank (m - k - 1) .Positive).signature +
      ((Gene.ofRank (n - k) .Positive).signature + (0, 1))
    · congr 3
      · omega
      · congr 1; omega
    abel_nf; rfl
  by_cases hk2 : k < n
  · rw [Nat.sub_right_comm, Nat.sub_eq_zero_of_le <| Nat.le_of_not_lt hk1,
      Nat.zero_sub, signature_ofRank_zero, signature_ofRank_zero, zero_add,
      zero_add, signature_ofRank_negative_eq (by omega)]
    convert_to _ ≤ (Gene.ofRank (n - k) .Positive).signature + (0, 1)
    · congr 3; omega
    simp; exact posPart_eq_self.mp rfl
  · rw [Nat.sub_right_comm, Nat.sub_eq_zero_of_le <| Nat.le_of_not_lt hk1,
      Nat.zero_sub, signature_ofRank_zero, signature_ofRank_zero, zero_add,
      zero_add, Nat.sub_eq_zero_of_le <| Nat.le_of_not_lt hk2,
      signature_ofRank_zero]
    exact signature_nonneg _

lemma mutation_type1_le {ε : GeneType} (hε : ε ≠ .NonPolarized)
  {m n : ℕ} (h_le : m ≤ n) :
    (Gene.ofRank m ε + Gene.ofRank n (- ε)) ≤
    (Gene.ofRank (m - 1) (- ε) + Gene.ofRank (n + 1) ε) :=
  match ε, hε with
  | .Positive, _ => mutation_type1_le_positive h_le
  | .Negative, _ => mutation_type1_le_negative h_le

end type1_isMutation

section type2_isMutation

lemma mutation_type2_ne {ε : GeneType}
  {m n : ℕ} (h_le : m ≤ n) (hm : 1 < m) :
    (Gene.ofRank m ε + Gene.ofRank n ε) ≠
    (Gene.ofRank (m - 2) ε + Gene.ofRank (n + 2) ε) := by
  intro h
  replace h := congr_arg (· ⟨m, ε, le_of_lt hm⟩) h
  have h_n : n ≠ 0 := by omega
  have h_m : m ≠ 0 := by omega
  simp [h_n, h_m, Gene.ofRank_def] at h
  split_ifs at h <;> (simp [Finsupp.single_apply] at h; grind)

lemma mutation_type2_iterate_signature_eq {ε : GeneType} (hε : ε ≠ .NonPolarized)
  {m n : ℕ} (h_le : m ≤ n) (hm : 1 < m) (i k : ℕ) (hi : i ≤ k) :
    (prime^[i] (Gene.ofRank (m + k) ε + Gene.ofRank (n + k) ε)).signature =
    (prime^[i] (Gene.ofRank (m + k - 2) ε + Gene.ofRank (n + k + 2) ε)).signature := by
  rw [iterate_map_add, iterate_map_add, prime_iterate_ofRank, prime_iterate_ofRank,
    prime_iterate_ofRank, prime_iterate_ofRank, map_add, map_add]
  match ε, hε with
  | .Positive, _ =>
    rw [signature_ofRank_positive_eq₂ (k := (m + k - i)) (by omega),
      signature_ofRank_positive_eq₂ (k := (n + k + 2 - i)) (by omega),
      Nat.sub_right_comm, show n + k + 2 - i - 2 = n + k - i by omega]
    ac_rfl
  | .Negative, hε =>
    rw [signature_ofRank_eq₂ (k := (m + k - i)) (by omega) hε,
      signature_ofRank_eq₂ (k := (n + k + 2 - i)) (by omega) hε,
      Nat.sub_right_comm, show n + k + 2 - i - 2 = n + k - i by omega]
    ac_rfl

lemma mutation_type2_signature_eq {ε : GeneType} (hε : ε ≠ .NonPolarized)
  {m n : ℕ} (h_le : m ≤ n) (hm : 1 < m) :
    (Gene.ofRank m ε + Gene.ofRank n ε).signature =
    (Gene.ofRank (m - 2) ε + Gene.ofRank (n + 2) ε).signature := by
  have := mutation_type2_iterate_signature_eq hε h_le hm 0 0 (le_of_eq rfl)
  rwa [Function.iterate_zero_apply, Function.iterate_zero_apply, add_zero, add_zero] at this

lemma mutation_type2_le_positive {m n : ℕ} (h_le : m ≤ n) (hm : 1 < m) :
    (Gene.ofRank m .Positive + Gene.ofRank n .Positive) ≤
    (Gene.ofRank (m - 2) .Positive + Gene.ofRank (n + 2) .Positive) := by
  sorry

lemma mutation_type2_le_negative {m n : ℕ} (h_le : m ≤ n) (hm : 1 < m) :
    (Gene.ofRank m .Negative + Gene.ofRank n .Negative) ≤
    (Gene.ofRank (m - 2) .Negative + Gene.ofRank (n + 2) .Negative) := by
  sorry

lemma mutation_type2_le {ε : GeneType} (hε : ε ≠ .NonPolarized)
  {m n : ℕ} (h_le : m ≤ n) (hm : 1 < m) :
    (Gene.ofRank m ε + Gene.ofRank n ε) ≤
    (Gene.ofRank (m - 2) ε + Gene.ofRank (n + 2) ε) :=
  match ε, hε with
  | .Positive, _ => mutation_type2_le_positive h_le hm
  | .Negative, _ => mutation_type2_le_negative h_le hm

end type2_isMutation

section type3_isMutation

lemma mutation_type3_ne {ε : GeneType}
  {m n : ℕ} (h_le : m ≤ n) (hm : 1 ≤ m) :
    (Gene.ofRankAlt m ε + Gene.ofRankAlt n (- ε)) ≠
    (Gene.ofRankAlt (m - 1) (- ε) + Gene.ofRankAlt (n + 1) ε) := by
  simp [Gene.ofRankAlt, Gene.ofRank]
  rcases m with ( _ | _ | m ) <;> rcases n with ( _ | _ | n ) <;> try grind
  · intro h
    simpa using congr_arg (· ⟨1, ε, hm⟩) h
  · intro h
    simpa using congr_arg (· ⟨1, ε, hm⟩) h
  · intro h
    have := congr_arg Finsupp.toMultiset h
    simp [Multiset.cons_eq_cons] at this
    omega

private lemma mutation_type3_iterate_signature_eq_case1
  {ε : GeneType} (hε : ε ≠ .NonPolarized) {n : ℕ} (h_le : 1 ≤ n) :
    (Gene.ofRankAlt 1 ε + Gene.ofRankAlt n (- ε)).signature =
    (Gene.ofRankAlt (n + 1) ε).signature := by
  simp [Gene.ofRankAlt_def, GeneType.neg_one_pow_smul]
  conv =>
    enter [2, 2, 2, 1]
    rw [(Nat.sub_eq_iff_eq_add h_le).1 rfl, Nat.even_add_one]
  cases ε
  · absurd hε; rfl
  all_goals
    split_ifs with h1
    · simp [signature_ofRank, show n ≠ 0 by omega, Gene.signature_eq_positive,
        Gene.signature_eq_negative, Nat.even_add_one, - Nat.not_even_iff_odd]
      split_ifs
      · absurd h1
        refine Nat.even_add_one.1 ?_
        rwa [Nat.sub_add_cancel h_le]
      · simp; ring
    · simp [signature_ofRank, show n ≠ 0 by omega, Gene.signature_eq_positive,
        Gene.signature_eq_negative, Nat.even_add_one, - Nat.not_even_iff_odd]
      split_ifs with h2
      · simp; ring
      · absurd h2
        rwa [← Nat.sub_add_cancel h_le, Nat.even_add_one]

lemma mutation_type3_iterate_signature_eq {ε : GeneType} (hε : ε ≠ .NonPolarized)
  {m n : ℕ} (h_le : m ≤ n) (hm : 1 ≤ m) (i k : ℕ) (hi : i ≤ k) :
    (prime^[i] (Gene.ofRankAlt (m + k) ((- 1) ^ k • ε) +
      Gene.ofRankAlt (n + k) ((- 1) ^ k • - ε))).signature =
    (prime^[i] (Gene.ofRankAlt (m + k - 1) ((- 1) ^ k • - ε) +
      Gene.ofRankAlt (n + k + 1) ((- 1) ^ k • ε))).signature := by
  by_cases hk : k = 0 <;> by_cases h_m : m = 1
  · subst hk h_m
    rw [Nat.eq_zero_of_le_zero hi, Function.iterate_zero_apply, Function.iterate_zero_apply,
      pow_zero, add_zero, add_zero, GeneType.one_smul, GeneType.one_smul, Nat.sub_self,
      Gene.ofRankAlt_zero, zero_add, mutation_type3_iterate_signature_eq_case1 hε h_le]
  · subst hk
    simp [Nat.eq_zero_of_le_zero hi, Gene.ofRankAlt_def,
      signature_ofRank_eq hm (GeneType.ne_nonPolarized_iff_one_pow_smul_ne.1 hε),
      signature_ofRank_eq (k := n + 1) (by omega)
      (GeneType.ne_nonPolarized_iff_one_pow_smul_ne.1 hε)]
    stop
    rw [Nat.eq_zero_of_le_zero hi, Function.iterate_zero_apply, Function.iterate_zero_apply,
      pow_zero, add_zero, add_zero, GeneType.one_smul, GeneType.one_smul, Gene.ofRankAlt_def,
      Gene.ofRankAlt_def, Gene.ofRankAlt_def, Gene.ofRankAlt_def, map_add, map_add,
      signature_ofRank_eq hm (GeneType.ne_nonPolarized_iff_one_pow_smul_ne.1 hε),
      signature_ofRank_eq (k := n + 1) (by omega)
      (GeneType.ne_nonPolarized_iff_one_pow_smul_ne.1 hε), Nat.add_sub_cancel,
      GeneType.neg_neg_one_pow_smul]

    sorry
  · subst h_m
    sorry
  · sorry

lemma mutation_type3_signature_eq {ε : GeneType} (hε : ε ≠ .NonPolarized)
  {m n : ℕ} (h_le : m ≤ n) (hm : 1 ≤ m) :
    (Gene.ofRankAlt m ε + Gene.ofRankAlt n (- ε)).signature =
    (Gene.ofRankAlt (m - 1) (- ε) + Gene.ofRankAlt (n + 1) ε).signature := by
  have := mutation_type3_iterate_signature_eq hε h_le hm 0 0 (le_of_eq rfl)
  rwa [Function.iterate_zero_apply, Function.iterate_zero_apply, add_zero, add_zero] at this

lemma mutation_type3_le {ε : GeneType} (hε : ε ≠ .NonPolarized)
  {m n : ℕ} (h_le : m ≤ n) (hm : 1 ≤ m) :
    (Gene.ofRankAlt m ε + Gene.ofRankAlt n (- ε)) ≤
    (Gene.ofRankAlt (m - 1) (- ε) + Gene.ofRankAlt (n + 1) ε) :=
  match ε, hε with
  | .Positive, _ => sorry
  | .Negative, _ => sorry

end type3_isMutation
