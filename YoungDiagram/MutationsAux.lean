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
    prime_iterate_ofRank, prime_iterate_ofRank, map_add, map_add,
    signature_ofRank_eq (k := (m + k - i)) (by omega) hε,
    signature_ofRank_eq (k := (n + k + 1 - i)) (by omega) hε, Nat.sub_right_comm,
    show n + k + 1 - i - 1 = n + k - i by exact Nat.succ_sub_succ_eq_sub (n + k) i]
  ac_rfl

lemma mutation_type1_signature_eq {ε : GeneType} (hε : ε ≠ .NonPolarized)
  {m n : ℕ} (h_le : m ≤ n) (hm : 1 ≤ m) :
    (Gene.ofRank m ε + Gene.ofRank n (- ε)).signature =
    (Gene.ofRank (m - 1) (- ε) + Gene.ofRank (n + 1) ε).signature := by
  have := mutation_type1_iterate_signature_eq hε h_le hm 0 0 le_rfl
  rwa [Function.iterate_zero_apply, Function.iterate_zero_apply, add_zero, add_zero] at this

lemma mutation_type1_le {ε : GeneType} (hε : ε ≠ .NonPolarized)
  {m n : ℕ} (h_le : m ≤ n) :
    (Gene.ofRank m ε + Gene.ofRank n (- ε)) ≤
    (Gene.ofRank (m - 1) (- ε) + Gene.ofRank (n + 1) ε) := by
  intro k
  simp only [iterate_map_add, map_add, prime_iterate_ofRank]
  by_cases hk1 : n < k
  · have eq1 : m - 1 - k = 0 := by omega
    simp [Nat.sub_eq_zero_iff_le.2 (h_le.trans hk1.le), eq1, Nat.sub_eq_zero_of_le hk1.le]
    exact signature_nonneg _
  by_cases hk2 : m ≤ k
  · have eq1 : m - 1 - k = 0 := by omega
    rw [signature_ofRank_eq (k := n + 1 - k) (by omega) hε, Nat.succ_sub_sub_succ]
    simp [Nat.sub_eq_zero_of_le hk2, eq1]
    exact signature_nonneg _
  · have le1 : 1 ≤ m - k := by omega
    have le2 : 1 ≤ n + 1 - k := by omega
    rw [signature_ofRank_eq le1 hε, signature_ofRank_eq le2 hε,
      Nat.succ_sub_sub_succ, Nat.sub_zero, Nat.sub_right_comm]
    exact le_of_eq <| by ac_rfl

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
    prime_iterate_ofRank, prime_iterate_ofRank, map_add, map_add,
    signature_ofRank_eq₂ (k := (m + k - i)) (by omega) hε,
    signature_ofRank_eq₂ (k := (n + k + 2 - i)) (by omega) hε, Nat.sub_right_comm,
    show n + k + 2 - i - 2 = n + k - i by omega]
  ac_rfl

lemma mutation_type2_signature_eq {ε : GeneType} (hε : ε ≠ .NonPolarized)
  {m n : ℕ} (h_le : m ≤ n) (hm : 1 < m) :
    (Gene.ofRank m ε + Gene.ofRank n ε).signature =
    (Gene.ofRank (m - 2) ε + Gene.ofRank (n + 2) ε).signature := by
  have := mutation_type2_iterate_signature_eq hε h_le hm 0 0 le_rfl
  rwa [Function.iterate_zero_apply, Function.iterate_zero_apply, add_zero, add_zero] at this

lemma mutation_type2_le {ε : GeneType} (hε : ε ≠ .NonPolarized)
  {m n : ℕ} (h_le : m ≤ n) (hm : 1 < m) :
    (Gene.ofRank m ε + Gene.ofRank n ε) ≤
    (Gene.ofRank (m - 2) ε + Gene.ofRank (n + 2) ε) := by
  intro k
  simp only [iterate_map_add, map_add, prime_iterate_ofRank]
  by_cases hk1 : n < k
  · have eq1 : m - 2 - k = 0 := by omega
    have eq2 : m - k = 0 := by omega
    rw [eq1, eq2, Nat.sub_eq_zero_of_le hk1.le, Gene.ofRank_zero, map_zero,
      add_zero, zero_add]
    exact signature_nonneg _
  by_cases hk2 : m - 2 < k
  · have eq1 : n + 2 - k - 2 = n - k := by omega
    rw [Nat.sub_eq_zero_of_le hk2.le, Gene.ofRank_zero, map_zero, zero_add,
      signature_ofRank_eq₂ (k := n + 2 - k) (by omega) hε, eq1, add_comm]
    gcongr
    have le1 : m - k < 2 := by omega
    match (m - k), le1 with
    | 0, _ => rw [Gene.ofRank_zero, map_zero]; decide
    | 1, _ => match ε, hε with | .Positive, _ => simp | .Negative, _ => simp
  · have eq1 : n + 2 - k - 2 = n - k := by omega
    rw [signature_ofRank_eq₂ (k := n + 2 - k) (by omega) hε, eq1,
      signature_ofRank_eq₂ (k := m - k) (by omega) hε, Nat.sub_right_comm]
    exact le_of_eq <| by ac_rfl

end type2_isMutation

section type3_isMutation

lemma mutation_type3_ne {ε : GeneType}
  {m n : ℕ} (h_le : m ≤ n) (hm : 1 ≤ m) :
    (Gene.ofRankAlt m ε + Gene.ofRankAlt n (- ε)) ≠
    (Gene.ofRankAlt (m - 1) (- ε) + Gene.ofRankAlt (n + 1) ε) := by
  simp [Gene.ofRankAlt, Gene.ofRank]
  rcases m with ( _ | _ | m ) <;> rcases n with ( _ | _ | n ) <;> try omega
  · intro h
    simpa using congr_arg (· ⟨1, ε, hm⟩) h
  · intro h
    simpa using congr_arg (· ⟨1, ε, hm⟩) h
  · intro h
    have := congr_arg Finsupp.toMultiset h
    simp [Multiset.cons_eq_cons] at this
    omega

lemma mutation_type3_iterate_signature_eq {ε : GeneType} (hε : ε ≠ .NonPolarized)
  {m n : ℕ} (h_le : m ≤ n) (hm : 1 ≤ m) (i k : ℕ) (hi : i ≤ k) :
    (prime^[i] (Gene.ofRankAlt (m + k) (Int.negOnePow k • ε) +
      Gene.ofRankAlt (n + k) (Int.negOnePow k • - ε))).signature =
    (prime^[i] (Gene.ofRankAlt (m + k - 1) (Int.negOnePow k • - ε) +
      Gene.ofRankAlt (n + k + 1) (Int.negOnePow k • ε))).signature := by
  simp [Gene.ofRankAlt_def, prime_iterate_ofRank]
  have le1 : 1 ≤ m + k - i := by omega
  have le2 : 1 ≤ n + k + 1 - i := by omega
  rw [signature_ofRank_eq' le1 (GeneType.ne_nonPolarized_iff_one_pow_smul_ne.1 hε),
    signature_ofRank_eq' le2 (GeneType.ne_nonPolarized_iff_one_pow_smul_ne.1 hε),
    Nat.sub_right_comm, Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_one, add_assoc,
    add_right_inj, Nat.succ_sub_sub_succ, Nat.sub_zero,
    add_comm (signature (Gene.ofRank (n + k - i) _)), add_left_inj]
  convert_to (if Even (m + k - i) then signature (Gene.ofRank 1 ((m + 2 * k : ℤ).negOnePow • ε))
    else signature (Gene.ofRank 1 ((m - 1 + 2 * k : ℤ).negOnePow • ε))) =
      if Even (n + k + 1 - i) then signature (Gene.ofRank 1 (-((n + 2 * k : ℤ).negOnePow • ε)))
    else signature (Gene.ofRank 1 ((n + 2 * k : ℤ).negOnePow • ε))
  · congr 5
    · rw [GeneType.neg_neg_one_pow_smul]
      congr 2; omega
    · omega
  · congr 5 <;> rw [two_mul, add_assoc]
  · rw [Int.negOnePow_add, Int.negOnePow_add, Int.negOnePow_add, Int.negOnePow_two_mul, mul_one,
      mul_one, mul_one, Int.negOnePow_sub, Int.negOnePow_one, mul_neg_one, ← GeneType.neg_smul]
    have iff1 := @Nat.even_sub (n + k + 1 - i) (m + k - i) (by omega)
    rw [show n + k + 1 - i - (m + k - i) = n + 1 - m by omega] at iff1
    split_ifs with h1 h2 h3
    · congr
      rw [← Int.negOnePow_succ, Int.negOnePow_eq_iff, ← even_neg, neg_sub, ← Nat.cast_one,
        ← Nat.cast_add, ← Nat.cast_sub (Nat.le_add_right_of_le h_le), Int.even_coe_nat, iff1]
      exact (iff_true_right h1).2 h2
    · congr 3
      rw [Int.negOnePow_eq_iff, ← even_neg, neg_sub, ← Nat.cast_sub h_le, Int.even_coe_nat]
      simpa [Nat.succ_sub h_le, Nat.even_add_one, h1, h2] using iff1
    · congr 4
      rw [Int.negOnePow_eq_iff, ← even_neg, neg_sub, ← Nat.cast_sub h_le, Int.even_coe_nat]
      simpa [Nat.succ_sub h_le, Nat.even_add_one, h1, h3] using iff1
    · congr
      rw [← Int.negOnePow_succ, Int.negOnePow_eq_iff, Int.even_sub, Int.even_add_one, iff_comm]
      contrapose!
      simpa [h1, h3, ← Int.even_coe_nat, Nat.le_add_right_of_le h_le,
        Int.even_sub, Int.even_add_one] using iff1

lemma mutation_type3_signature_eq {ε : GeneType} (hε : ε ≠ .NonPolarized)
  {m n : ℕ} (h_le : m ≤ n) (hm : 1 ≤ m) :
    (Gene.ofRankAlt m ε + Gene.ofRankAlt n (- ε)).signature =
    (Gene.ofRankAlt (m - 1) (- ε) + Gene.ofRankAlt (n + 1) ε).signature := by
  have := mutation_type3_iterate_signature_eq hε h_le hm 0 0 le_rfl
  rwa [Function.iterate_zero_apply, Function.iterate_zero_apply, add_zero, add_zero] at this

lemma mutation_type3_le {ε : GeneType} (hε : ε ≠ .NonPolarized)
  {m n : ℕ} (h_le : m ≤ n) (hm : 1 ≤ m) :
    (Gene.ofRankAlt m ε + Gene.ofRankAlt n (- ε)) ≤
    (Gene.ofRankAlt (m - 1) (- ε) + Gene.ofRankAlt (n + 1) ε) := by
  intro k
  simp only [iterate_map_add, map_add, prime_iterate_ofRank]
  by_cases hk1 : n < k
  · have eq1 : m - 1 - k = 0 := by omega
    simp [Nat.sub_eq_zero_iff_le.2 (h_le.trans hk1.le), eq1, Nat.sub_eq_zero_of_le hk1.le]
    exact signature_nonneg _
  by_cases hk2 : m ≤ k
  · have eq1 : m - 1 - k = 0 := by omega
    simp [eq1, Nat.sub_eq_zero_of_le hk2]
    rw [signature_ofRank_eq' (k := n + 1 - k) (by omega), Nat.succ_sub_sub_succ,
      Nat.sub_zero, le_add_iff_nonneg_right]
    · split_ifs <;> exact signature_nonneg _
    · exact GeneType.ne_nonPolarized_iff_one_pow_smul_ne.1 hε
  · have le1 : 1 ≤ m - k := by omega
    have le2 : 1 ≤ n + 1 - k := by omega
    rw [signature_ofRank_eq' le1, signature_ofRank_eq' le2, Nat.succ_sub_sub_succ,
      Nat.sub_zero, Nat.sub_right_comm, add_assoc, add_comm (signature (Gene.ofRank (n - k) _))]
    swap; · exact GeneType.ne_nonPolarized_iff_one_pow_smul_ne.1 hε
    swap; · exact GeneType.ne_nonPolarized_iff_one_pow_smul_ne.1 hε
    gcongr
    · simp only [hm, Nat.cast_sub, Nat.cast_one, GeneType.smul_neg, GeneType.neg_neg_one_pow_smul,
      sub_add_cancel, le_refl]
    · have eq1 : n + 1 - k = n - k + 1 := by omega
      simp_rw [Int.negOnePow_sub, Int.negOnePow_one, mul_neg_one, GeneType.neg_smul, neg_neg, eq1,
        Nat.even_add_one, Nat.even_sub (Nat.le_of_not_ge hk2), Nat.even_sub (Nat.le_of_not_lt hk1),
        GeneType.neg_one_pow_smul', Nat.even_add_one, iff_iff_and_or_not_and_not, ite_not, ite_or,
        ite_and]
      split_ifs <;> first | exact le_rfl | rw [neg_neg]
    · simp

end type3_isMutation
