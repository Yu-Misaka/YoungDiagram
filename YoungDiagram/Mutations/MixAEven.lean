import YoungDiagram

open Chromosome

variable {ε : GeneType} {m n : ℕ}

-- Φ = (Λ, Π): g ranks even, g^ε ranks odd.

local notation "type4X" =>
  Gene.ofRank (2 * m + 2) GeneType.NonPolarized +
  Gene.ofRank (2 * n + 2) GeneType.NonPolarized
local notation "type4Y" =>
  Gene.ofRank (2 * m + 1) ε +
  Gene.ofRank (2 * n + 3) (- ε)

local notation "type5X" =>
  Gene.ofRank (2 * m + 2) GeneType.NonPolarized +
  Gene.ofRank (2 * n + 3) ε
local notation "type5Y" =>
  Gene.ofRank (2 * m + 1) ε +
  Gene.ofRank (2 * n + 4) GeneType.NonPolarized

local notation "type6X" =>
  Gene.ofRank (2 * m + 1) ε +
  Gene.ofRank (2 * n + 2) GeneType.NonPolarized
local notation "type6Y" =>
  Gene.ofRank (2 * m) GeneType.NonPolarized +
  Gene.ofRank (2 * n + 3) ε

local notation "type7X" =>
  Gene.ofRank (2 * m + 1) ε +
  Gene.ofRank (2 * n + 1) (- ε)
local notation "type7Y" =>
  Gene.ofRank (2 * m) GeneType.NonPolarized +
  Gene.ofRank (2 * n + 2) GeneType.NonPolarized

local notation "type8X" =>
  Gene.ofRank (2 * m + 3) ε +
  Gene.ofRank (2 * n + 3) ε
local notation "type8Y" =>
  Gene.ofRank (2 * m + 1) ε +
  Gene.ofRank (2 * n + 5) ε

variable (h_le : m ≤ n)

include h_le

section Aux

section type4_isMutation

omit h_le in
lemma mutation_type4_ne : type4X ≠ type4Y := by
  intro h
  replace h := congr_arg (· ⟨2 * m + 2, .NonPolarized, by omega⟩) h
  have h_n : 2 * n + 2 ≠ 0 := by omega
  have h_m : 2 * m + 2 ≠ 0 := by omega
  simp only [Gene.ofRank_def, h_m, ↓reduceDIte, h_n, Finsupp.coe_add, Pi.add_apply,
    Finsupp.single_eq_same, Nat.add_eq_zero_iff, one_ne_zero, and_false] at h
  rw [dif_neg (by omega), Finsupp.single_apply] at h
  split_ifs at h <;> (simp [Finsupp.single_apply] at h; grind)

lemma mutation_type4_iterate_signature_eq (i k : ℕ) (hi : i ≤ k) :
    (prime^[i] (Gene.ofRank (2 * m + 2 + k) .NonPolarized +
      Gene.ofRank (2 * n + 2 + k) .NonPolarized)).signature =
    (prime^[i] (Gene.ofRank (2 * m + 1 + k) ε + Gene.ofRank (2 * n + 3 + k) (- ε))).signature := by
  have le1 : i ≤ 2 * n + 1 + k := by omega
  have le2 : i ≤ 2 * m + 1 + k := by omega
  have le3 : i ≤ 2 * m + 2 + k := by omega
  have eq1 : 2 * n + 3 + k - i - 2 = 2 * n + 1 + k - i := by omega
  have le4 : i ≤ 2 * n + 2 + k := by omega
  rw [iterate_map_add, iterate_map_add, prime_iterate_ofRank, prime_iterate_ofRank,
    prime_iterate_ofRank, prime_iterate_ofRank, map_add, map_add,
    signature_ofRank_nonPolarized, signature_ofRank_nonPolarized,
    signature_ofRank_eq₂ (k := 2 * n + 3 + k - i) (by omega), ← add_assoc,
    signature_ofRank_sum_even, Prod.mk_add_mk, ← add_div]
  · simp only [Nat.cast_add, Nat.cast_sub le3, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub le4, eq1,
    Nat.cast_sub le2, Nat.cast_one, Nat.cast_sub le1, Prod.mk_add_mk, Prod.mk.injEq, and_self]
    ring
  · grind only [= Nat.even_iff]

lemma mutation_type4_signature_eq :
    signature type4X = signature type4Y := by
  have := mutation_type4_iterate_signature_eq (ε := ε) h_le 0 0 le_rfl
  rwa [Function.iterate_zero_apply, Function.iterate_zero_apply, add_zero, add_zero] at this

lemma mutation_type4_le : type4X ≤ type4Y := by
  intro k
  simp only [iterate_map_add, map_add, prime_iterate_ofRank, signature_ofRank_nonPolarized]
  by_cases hle1 : k ≤ 2 * m + 1
  · have le1 : k ≤ 2 * m + 2 := by omega
    have le2 : k ≤ 2 * n + 2 := by omega
    have le3 : k ≤ 2 * n + 3 := by omega
    rw [signature_ofRank_sum_even, Prod.mk_add_mk, ← add_div, Nat.cast_sub le1,
      Nat.cast_sub le2, Nat.cast_sub hle1, Nat.cast_sub le3]
    · simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one,
        Prod.mk_le_mk, and_self, ge_iff_le]; linarith only []
    · grind only [= Nat.even_iff]
  · by_cases hle2 : k ≤ 2 * n + 3
    · have eq1 : 2 * m + 2 - k = 0 := by omega
      have eq2 : 2 * m + 1 - k = 0 := by omega
      rw [eq1, eq2, Nat.cast_zero, zero_div, Gene.ofRank_zero, map_zero,
        ← Prod.zero_eq_mk, zero_add, zero_add]
      by_cases heq1 : k = 2 * n + 3
      · simp only [heq1, add_le_add_iff_left, Nat.reduceLeDiff, Nat.sub_eq_zero_of_le,
        CharP.cast_eq_zero, zero_div, tsub_self, Gene.ofRank_zero, map_zero]
        rfl
      · have le1 : k ≤ 2 * n + 2 := by omega
        convert signature_ofRank_ge
        <;> (simp [Nat.cast_sub le1, Nat.cast_sub hle2]; grind)
    · have eq1 : 2 * m + 2 - k = 0 := by omega
      have eq2 : 2 * m + 1 - k = 0 := by omega
      have eq3 : 2 * n + 3 - k = 0 := by omega
      have eq4 : 2 * n + 2 - k = 0 := by omega
      rw [eq1, eq2, eq3, eq4, Gene.ofRank_zero, Gene.ofRank_zero, map_zero,
        Nat.cast_zero, zero_div]; rfl

end type4_isMutation

section type5_isMutation

lemma mutation_type5_ne : type5X ≠ type5Y := by
  intro h
  replace h := congr_arg (· ⟨2 * m + 2, .NonPolarized, by omega⟩) h
  have h_m : 2 * m + 2 ≠ 0 := by omega
  have h_n : 2 * n + 3 ≠ 0 := by omega
  have h_m' : 2 * m + 1 ≠ 0 := by omega
  have h_n' : 2 * n + 4 ≠ 0 := by omega
  simp only [Gene.ofRank_def, h_m, h_n, h_m', h_n', ↓reduceDIte, Finsupp.coe_add,
    Pi.add_apply, Finsupp.single_eq_same, Finsupp.single_apply, Gene.mk.injEq,
    Nat.reduceEqDiff, Nat.add_left_cancel_iff, false_and, and_true] at h
  split_ifs at h <;> omega

lemma mutation_type5_iterate_signature_eq (i k : ℕ) (hi : i ≤ k) :
    (prime^[i] (Gene.ofRank (2 * m + 2 + k) .NonPolarized +
      Gene.ofRank (2 * n + 3 + k) ε)).signature =
    (prime^[i] (Gene.ofRank (2 * m + 1 + k) ε +
      Gene.ofRank (2 * n + 4 + k) .NonPolarized)).signature := by
  have eq1 : 2 * m + 2 + k - i = 2 * m + 1 + k - i + 1 := by omega
  have eq2 : 2 * n + 4 + k - i = 2 * n + 3 + k - i + 1 := by omega
  rw [iterate_map_add, iterate_map_add, prime_iterate_ofRank, prime_iterate_ofRank,
    prime_iterate_ofRank, prime_iterate_ofRank, map_add, map_add, eq1, eq2,
    signature_ofRank_nonPolarized_succ_add]
  grind only [= Nat.even_iff]

lemma mutation_type5_signature_eq :
    signature type5X = signature type5Y := by
  have := mutation_type5_iterate_signature_eq (ε := ε) h_le 0 0 le_rfl
  rwa [Function.iterate_zero_apply, Function.iterate_zero_apply, add_zero, add_zero] at this

lemma mutation_type5_le : type5X ≤ type5Y := by
  intro k
  simp only [iterate_map_add, map_add, prime_iterate_ofRank]
  by_cases hle1 : k ≤ 2 * m + 1
  · have eq1 : 2 * m + 2 - k = 2 * m + 1 - k + 1 := by omega
    have eq2 : 2 * n + 4 - k = 2 * n + 3 - k + 1 := by omega
    rw [eq1, eq2, signature_ofRank_nonPolarized_succ_add]
    grind only [= Nat.even_iff]
  · by_cases hle2 : k ≤ 2 * n + 3
    · have eq1 : 2 * m + 2 - k = 0 := by omega
      have eq2 : 2 * m + 1 - k = 0 := by omega
      have le1 : k ≤ 2 * n + 4 := by omega
      rw [eq1, eq2, Gene.ofRank_zero, Gene.ofRank_zero, map_zero, zero_add,
        zero_add, signature_ofRank_nonPolarized]
      convert Chromosome.signature_ofRank_le
      <;> (rw [Nat.cast_sub le1, Nat.cast_sub hle2, Nat.cast_add, Nat.cast_add]; ring)
    · have eq1 : 2 * m + 2 - k = 0 := by omega
      have eq2 : 2 * m + 1 - k = 0 := by omega
      have eq3 : 2 * n + 3 - k = 0 := by omega
      have eq4 : 2 * n + 4 - k = 0 := by omega
      rw [eq1, eq2, eq3, eq4, Gene.ofRank_zero, Gene.ofRank_zero, map_zero]

end type5_isMutation

section type6_isMutation

lemma mutation_type6_ne : type6X ≠ type6Y := by
  intro h
  replace h := congr_arg (· ⟨2 * n + 3, ε, by omega⟩) h
  have h_m : 2 * m + 1 ≠ 0 := by omega
  have h_n : 2 * n + 2 ≠ 0 := by omega
  have h_n' : 2 * n + 3 ≠ 0 := by omega
  simp only [Gene.ofRank_def, h_m, h_n, h_n', ↓reduceDIte, Finsupp.coe_add,
    Pi.add_apply, Finsupp.single_eq_same, Finsupp.single_apply, Gene.mk.injEq,
    Nat.reduceEqDiff, Nat.add_left_cancel_iff, false_and, and_true] at h
  split_ifs at h <;> omega

lemma mutation_type6_iterate_signature_eq (i k : ℕ) (hi : i ≤ k) :
    (prime^[i] (Gene.ofRank (2 * m + 1 + k) ε +
      Gene.ofRank (2 * n + 2 + k) .NonPolarized)).signature =
    (prime^[i] (Gene.ofRank (2 * m + k) .NonPolarized +
      Gene.ofRank (2 * n + 3 + k) ε)).signature := by
  have eq1 : 2 * m + 1 + k - i = 2 * m + k - i + 1 := by omega
  have eq2 : 2 * n + 3 + k - i = 2 * n + 2 + k - i + 1 := by omega
  rw [iterate_map_add, iterate_map_add, prime_iterate_ofRank, prime_iterate_ofRank,
    prime_iterate_ofRank, prime_iterate_ofRank, map_add, map_add, eq1, eq2,
    signature_ofRank_succ_add_nonPolarized]
  grind only [= Nat.even_iff]

lemma mutation_type6_signature_eq :
    signature type6X = signature type6Y := by
  have := mutation_type6_iterate_signature_eq (ε := ε) h_le 0 0 le_rfl
  rwa [Function.iterate_zero_apply, Function.iterate_zero_apply, add_zero, add_zero] at this

lemma mutation_type6_le : type6X ≤ type6Y := by
  intro k
  simp only [iterate_map_add, map_add, prime_iterate_ofRank]
  by_cases hle1 : k ≤ 2 * m
  · have eq1 : 2 * m + 1 - k = 2 * m - k + 1 := by omega
    have eq2 : 2 * n + 3 - k = 2 * n + 2 - k + 1 := by omega
    rw [eq1, eq2, signature_ofRank_succ_add_nonPolarized]
    grind only [= Nat.even_iff]
  · by_cases hle2 : k ≤ 2 * n + 2
    · have eq1 : 2 * m + 1 - k = 0 := by omega
      have eq2 : 2 * m - k = 0 := by omega
      have le1 : k ≤ 2 * n + 3 := by omega
      rw [eq1, eq2, Gene.ofRank_zero, Gene.ofRank_zero, map_zero, zero_add,
        zero_add, signature_ofRank_nonPolarized]
      convert Chromosome.signature_ofRank_ge
      <;> (rw [Nat.cast_sub hle2, Nat.cast_sub le1, Nat.cast_add, Nat.cast_add]; ring)
    · have eq1 : 2 * m + 1 - k = 0 := by omega
      have eq2 : 2 * m - k = 0 := by omega
      have eq3 : 2 * n + 2 - k = 0 := by omega
      have eq4 : 2 * n + 3 - k = 0 := by omega
      rw [eq1, eq2, eq3, eq4, Gene.ofRank_zero, Gene.ofRank_zero, map_zero]

end type6_isMutation

section type7_isMutation

omit h_le in
lemma mutation_type7_ne : type7X ≠ type7Y := by
  intro h
  replace h := congr_arg (· ⟨2 * n + 2, .NonPolarized, by omega⟩) h
  have h_m : 2 * m + 1 ≠ 0 := by omega
  have h_n : 2 * n + 1 ≠ 0 := by omega
  have h_n' : 2 * n + 2 ≠ 0 := by omega
  simp only [Gene.ofRank_def, h_m, h_n, h_n', ↓reduceDIte, Finsupp.coe_add,
    Pi.add_apply, Finsupp.single_eq_same, Finsupp.single_apply, Gene.mk.injEq,
    Nat.reduceEqDiff, Nat.add_left_cancel_iff, false_and] at h
  split_ifs at h <;> omega

lemma mutation_type7_iterate_signature_eq (i k : ℕ) (hi : i ≤ k) :
    (prime^[i] (Gene.ofRank (2 * m + 1 + k) ε +
      Gene.ofRank (2 * n + 1 + k) (- ε))).signature =
    (prime^[i] (Gene.ofRank (2 * m + k) .NonPolarized +
      Gene.ofRank (2 * n + 2 + k) .NonPolarized)).signature := by
  have eq1 : 2 * m + 1 + k - i = 2 * m + k - i + 1 := by omega
  have eq2 : 2 * n + 1 + k - i = 2 * n + 2 + k - i - 1 := by omega
  have hn : 1 ≤ 2 * n + 2 + k - i := by omega
  rw [iterate_map_add, iterate_map_add, prime_iterate_ofRank, prime_iterate_ofRank,
    prime_iterate_ofRank, prime_iterate_ofRank, map_add, map_add, eq1, eq2,
    signature_ofRank_succ_add_pred_neg hn]
  grind only [= Nat.even_iff]

lemma mutation_type7_signature_eq :
    signature type7X = signature type7Y := by
  have := mutation_type7_iterate_signature_eq (ε := ε) h_le 0 0 le_rfl
  rwa [Function.iterate_zero_apply, Function.iterate_zero_apply, add_zero, add_zero] at this

lemma mutation_type7_le : type7X ≤ type7Y := by
  intro k
  simp only [iterate_map_add, map_add, prime_iterate_ofRank]
  by_cases hle1 : k ≤ 2 * m
  · have eq1 : 2 * m + 1 - k = 2 * m - k + 1 := by omega
    have eq2 : 2 * n + 1 - k = 2 * n + 2 - k - 1 := by omega
    have hn : 1 ≤ 2 * n + 2 - k := by omega
    rw [eq1, eq2, signature_ofRank_succ_add_pred_neg hn]
    grind only [= Nat.even_iff]
  · by_cases hle2 : k ≤ 2 * n + 1
    · have eq1 : 2 * m + 1 - k = 0 := by omega
      have eq2 : 2 * m - k = 0 := by omega
      have le1 : k ≤ 2 * n + 2 := by omega
      rw [eq1, eq2, Gene.ofRank_zero, Gene.ofRank_zero, map_zero, zero_add,
        zero_add, signature_ofRank_nonPolarized]
      convert Chromosome.signature_ofRank_le
      <;> (rw [Nat.cast_sub hle2, Nat.cast_sub le1, Nat.cast_add, Nat.cast_add]; ring)
    · have eq1 : 2 * m + 1 - k = 0 := by omega
      have eq2 : 2 * m - k = 0 := by omega
      have eq3 : 2 * n + 1 - k = 0 := by omega
      have eq4 : 2 * n + 2 - k = 0 := by omega
      simp [eq1, eq2, eq3, eq4, Gene.ofRank_zero]

end type7_isMutation

section type8_isMutation

lemma mutation_type8_ne : type8X ≠ type8Y := by
  intro h
  replace h := congr_arg (· ⟨2 * n + 5, ε, by omega⟩) h
  have h_m : 2 * m + 3 ≠ 0 := by omega
  have h_n : 2 * n + 3 ≠ 0 := by omega
  have h_m' : 2 * m + 1 ≠ 0 := by omega
  have h_n' : 2 * n + 5 ≠ 0 := by omega
  simp only [Gene.ofRank_def, h_m, h_n, h_m', h_n', ↓reduceDIte, Finsupp.coe_add,
    Pi.add_apply, Finsupp.single_eq_same, Finsupp.single_apply, Gene.mk.injEq,
    Nat.reduceEqDiff, Nat.add_left_cancel_iff, and_true] at h
  split_ifs at h <;> omega

lemma mutation_type8_iterate_signature_eq (i k : ℕ) (hi : i ≤ k) :
    (prime^[i] (Gene.ofRank (2 * m + 3 + k) ε +
      Gene.ofRank (2 * n + 3 + k) ε)).signature =
    (prime^[i] (Gene.ofRank (2 * m + 1 + k) ε +
      Gene.ofRank (2 * n + 5 + k) ε)).signature := by
  have eq1 : 2 * m + 3 + k - i = 2 * m + 1 + k - i + 2 := by omega
  have eq2 : 2 * n + 5 + k - i = 2 * n + 3 + k - i + 2 := by omega
  rw [iterate_map_add, iterate_map_add, prime_iterate_ofRank, prime_iterate_ofRank,
    prime_iterate_ofRank, prime_iterate_ofRank, map_add, map_add, eq1, eq2,
    signature_ofRank_add_two_add]

lemma mutation_type8_signature_eq :
    signature type8X = signature type8Y := by
  have := mutation_type8_iterate_signature_eq (ε := ε) h_le 0 0 le_rfl
  rwa [Function.iterate_zero_apply, Function.iterate_zero_apply, add_zero, add_zero] at this

lemma mutation_type8_le : type8X ≤ type8Y := by
  intro k
  simp only [iterate_map_add, map_add, prime_iterate_ofRank]
  by_cases hk1 : 2 * n + 3 < k
  · have eq1 : 2 * m + 3 - k = 0 := by omega
    have eq2 : 2 * m + 1 - k = 0 := by omega
    rw [eq1, eq2, Nat.sub_eq_zero_of_le hk1.le, Gene.ofRank_zero, map_zero,
      add_zero, zero_add]
    exact signature_nonneg _
  by_cases hk2 : 2 * m + 1 < k
  · have eq1 : 2 * n + 5 - k - 2 = 2 * n + 3 - k := by omega
    rw [Nat.sub_eq_zero_of_le hk2.le, Gene.ofRank_zero, map_zero, zero_add,
      signature_ofRank_eq₂ (k := 2 * n + 5 - k) (by omega), eq1, add_comm]
    gcongr
    have le1 : 2 * m + 3 - k < 2 := by omega
    match 2 * m + 3 - k, le1 with
    | 0, _ => rw [Gene.ofRank_zero, map_zero]; decide
    | 1, _ =>
      cases ε
      · simp [Gene.ofRank_def, Gene.signature]; norm_num
      · simp [Gene.ofRank_def, Gene.signature]
      · simp [Gene.ofRank_def, Gene.signature]
  · have eq1 : 2 * m + 3 - k = 2 * m + 1 - k + 2 := by omega
    have eq2 : 2 * n + 5 - k = 2 * n + 3 - k + 2 := by omega
    rw [eq1, eq2, signature_ofRank_add_two_add]

end type8_isMutation

end Aux
