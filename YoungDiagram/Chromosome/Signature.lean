import YoungDiagram.Chromosome.Basic

open Finsupp

namespace Chromosome

section signature

/--
The signature of a chromosome is the weighted sum of the signatures of its constituent genes.
-/
noncomputable def signature : Chromosome →+ ℚ × ℚ := weight Gene.signature

lemma signature_def {X : Chromosome} : X.signature =
  X.sum (fun g count ↦ (count : ℚ) • g.signature) := rfl

lemma signature_nonneg (X : Chromosome) : 0 ≤ X.signature := by
  dsimp [signature_def]
  exact sum_nonneg' fun g ↦
    smul_nonneg Rat.natCast_nonneg g.signature_pos.le

@[simp] lemma signature_ofRank_zero {ε : GeneType} :
    (Gene.ofRank 0 ε).signature = 0 := rfl

lemma signature_ofRank {n : ℕ} {ε : GeneType} :
  (Gene.ofRank n ε).signature =
    if h : n = 0 then 0
    else (⟨n, ε, Nat.pos_of_ne_zero h⟩ : Gene).signature := by
  dsimp [signature_def]
  split_ifs
  · rfl
  · rw [sum_single_index, Nat.cast_one, one_smul]
    · exact smul_eq_zero_of_left rfl _

@[simp] lemma signature_ofRank_one_positive :
    (Gene.ofRank 1 .Positive).signature = (1, 0) := by
  simp only [signature_ofRank, one_ne_zero, ↓reduceDIte, Gene.signature_of_positive,
    Nat.not_even_one, ↓reduceIte, Nat.cast_one, add_self_div_two, sub_self, zero_div]

@[simp] lemma signature_ofRank_one_negative :
    (Gene.ofRank 1 .Negative).signature = (0, 1) := by
  simp only [signature_ofRank, one_ne_zero, ↓reduceDIte, Gene.signature_of_negative,
    Nat.not_even_one, ↓reduceIte, Nat.cast_one, sub_self, zero_div, add_self_div_two]

@[simp] lemma signature_single {k : ℕ} {n : ℕ} (hk : 1 ≤ k) {ε : GeneType} :
    signature (single (⟨k, ε, hk⟩ : Gene) n) =
    n * (⟨k, ε, hk⟩ : Gene).signature :=
  sum_single_index <| smul_eq_zero_of_left rfl _

lemma signature_ofRank_nonPolarized {n : ℕ} :
    (Gene.ofRank n .NonPolarized).signature =
    ((n : ℚ) / 2, (n : ℚ) / 2) := by
  rw [signature_ofRank]
  split_ifs with h
  · rw [h, Nat.cast_zero, zero_div]; rfl
  · rw [Gene.signature_of_nonPolarized]; rfl

lemma signature_ofRank_nonPolarized_eq_swap {n : ℕ} :
    (Gene.ofRank n .NonPolarized).signature =
    (Gene.ofRank n .NonPolarized).signature.swap := by
  rw [signature_ofRank_nonPolarized]; rfl

lemma signature_ofRank_swap {n : ℕ} {ε : GeneType} :
    (Gene.ofRank n (- ε)).signature = (Gene.ofRank n ε).signature.swap := by
  cases ε
  · exact signature_ofRank_nonPolarized_eq_swap
  all_goals
    simp only [GeneType.neg_positive, signature_ofRank]; split_ifs
    · rfl
    · first | rw [Gene.signature_of_negative rfl, Gene.signature_of_positive rfl] |
        rw [Gene.signature_of_positive rfl, Gene.signature_of_negative rfl]
      simp only; split_ifs <;> rfl

lemma signature_neg {X : Chromosome} :
    (- X).signature = X.signature.swap := by
  induction X using induction' with
  | zero => rw [neg_zero, map_zero]; rfl
  | ofRank_add _ _ _ hY =>
    rw [map_add, Prod.swap_add, ← hY, neg_add, map_add, add_left_inj, neg_smul,
      map_nsmul, map_nsmul, Prod.smul_swap, neg_ofRank, signature_ofRank_swap]

lemma signature_sum_ofRank_neg_eq_rank {k : ℕ} {ε : GeneType} :
    (Gene.ofRank k ε).signature + (Gene.ofRank k (- ε)).signature = k := by
  rw [signature_ofRank, signature_ofRank]
  split_ifs with h
  · rw [h, Nat.cast_zero, zero_add]
  · exact Gene.signature_sum_neg_eq_rank (Nat.pos_of_ne_zero h)

lemma signature_ofRank_positive {k : ℕ} (hk : 1 ≤ k) :
    (Gene.ofRank k .Positive).signature =
    (Gene.ofRank (k - 1) .Negative).signature + (1, 0) := by
  have hk' : k ≠ 0 := by omega
  simp only [signature_ofRank, hk', ↓reduceDIte]
  split_ifs with h
  · replace hk : k = 1 := by omega
    simp [Gene.signature_of_positive, hk]
  · simp [Gene.signature_of_positive]
    split_ifs with h1
    · have : ¬ Even (k - 1) := (Nat.even_sub_one hk).1 h1
      simp [Gene.signature_of_negative, this, Nat.cast_pred hk]; ring
    · have : Even (k - 1) := (iff_not_comm.1 (Nat.even_sub_one hk)).2 h1
      simp [Gene.signature_of_negative, this, Nat.cast_pred hk]; ring

lemma signature_ofRank_negative {k : ℕ} (hk : 1 ≤ k) :
    (Gene.ofRank k .Negative).signature =
    (Gene.ofRank (k - 1) .Positive).signature + (0, 1) := by
  rw [← GeneType.neg_positive, signature_ofRank_swap,
    signature_ofRank_positive hk, Prod.swap_add, ← signature_ofRank_swap]; simp

lemma signature_ofRank_general {k : ℕ} {ε : GeneType} (hk : 1 ≤ k) (hε : ε ≠ .NonPolarized) :
    (Gene.ofRank k ε).signature =
    (Gene.ofRank (k - 1) (-ε)).signature + (Gene.ofRank 1 ε).signature := by
  match ε, hε with
  | .Positive, _ => simp only [signature_ofRank_positive hk, GeneType.neg_positive,
    signature_ofRank_one_positive]
  | .Negative, _ => simp only [signature_ofRank_negative hk, GeneType.neg_negative,
    signature_ofRank_one_negative]

lemma signature_ofRank_even_half {k : ℕ} {ε : GeneType} (hk : Even k) :
    (Gene.ofRank k ε).signature = ((k : ℚ) / 2, (k : ℚ) / 2) := by
  rw [signature_ofRank]
  split_ifs with h
  · rw [h, Nat.cast_zero, zero_div]; rfl
  · rwa [Gene.signature_even_half]

lemma signature_ofRank_even {k : ℕ} {ε : GeneType} (hk : Even k) :
    (Gene.ofRank k ε).signature = (Gene.ofRank k (- ε)).signature := by
  by_cases hk_zero : k = 0
  · rw [hk_zero, Gene.ofRank_zero, Gene.ofRank_zero]
  · simp only [signature_ofRank, hk_zero, ↓reduceDIte, Gene.signature, hk, ↓reduceIte]
    split <;> rfl

lemma signature_ofRankAlt_general {k : ℕ} {ε : GeneType} (hk : 1 ≤ k)
    (hε : ε ≠ .NonPolarized) :
    (Gene.ofRankAlt k ε).signature =
    (Gene.ofRankAlt (k - 1) (-ε)).signature + (Gene.ofRank 1 ε).signature := by
  rw [Gene.ofRankAlt_def, Gene.ofRankAlt_def, Nat.cast_sub hk,
    Nat.cast_one, ← sub_add_eq_sub_sub]
  obtain (h1 | h1) := Int.even_or_odd k
  · rw [Int.negOnePow_odd, Int.negOnePow_even, GeneType.neg_one_smul, one_smul,
      ← signature_ofRank_general hk hε, ← signature_ofRank_even]
    · exact (Int.even_coe_nat k).1 h1
    · exact Even.sub h1 <| Int.even_iff.2 rfl
    · exact odd_sub_one.2 h1
  · rw [Int.negOnePow_even, Int.negOnePow_odd, one_smul, GeneType.neg_one_smul,
      signature_ofRank_general hk hε, add_left_inj, signature_ofRank_even]
    · exact Odd.tsub_odd ((Int.odd_coe_nat k).1 h1) <| Nat.odd_iff.2 rfl
    · exact Odd.sub_even h1 <| Int.even_iff.2 rfl
    · exact even_sub_one.2 h1

lemma signature_ofRankAlt_general' {k : ℕ} {ε : GeneType} (hε : ε ≠ .NonPolarized) :
    (Gene.ofRankAlt (k + 1) ε).signature =
    (Gene.ofRankAlt k (- ε)).signature + (Gene.ofRank 1 ε).signature := by
  rw [signature_ofRankAlt_general (by omega) hε, Nat.add_sub_cancel]

lemma signature_ofRank_eq {k : ℕ} {ε : GeneType} (hk : 1 ≤ k) (hε : ε ≠ .NonPolarized) :
    (Gene.ofRank k ε).signature =
    (Gene.ofRank (k - 1) (- ε)).signature + (Gene.ofRank 1 ε).signature := by
  match ε, hε with
  | .Positive, _ => simp [signature_ofRank_positive hk]
  | .Negative, _ =>
    rw [← GeneType.neg_positive, signature_ofRank_swap,
      signature_ofRank_positive hk, Prod.swap_add, ← signature_ofRank_swap]; simp

lemma signature_ofRank_positive' {k : ℕ} (hk : 1 ≤ k) :
    (Gene.ofRank k .Positive).signature =
    (Gene.ofRank (k - 1) .Positive).signature + if Even k then (0, 1) else (1, 0) := by
  have hk' : k ≠ 0 := by omega
  by_cases hk'' : k = 1
  · subst hk''
    simp only [signature_ofRank_one_positive, tsub_self, Gene.ofRank_zero, map_zero,
      Nat.not_even_one, ↓reduceIte, zero_add]
  · simp only [signature_ofRank, hk', ↓reduceDIte]
    replace hk'' : k - 1 ≠ 0 := Nat.sub_ne_zero_of_lt <|
      Nat.lt_of_le_of_ne hk fun a ↦ hk'' a.symm
    simp only [Gene.signature_of_positive, Nat.even_sub_one hk, ite_not, hk'', ↓reduceDIte]
    split_ifs <;> (simp [hk]; ring)

lemma signature_ofRank_eq' {k : ℕ} {ε : GeneType} (hk : 1 ≤ k) (hε : ε ≠ .NonPolarized) :
    (Gene.ofRank k ε).signature = (Gene.ofRank (k - 1) ε).signature +
    if Even k then (Gene.ofRank 1 (- ε)).signature else (Gene.ofRank 1 ε).signature := by
  match ε, hε with
  | .Positive, _ => simp [signature_ofRank_positive' hk]
  | .Negative, _ =>
    rw [← GeneType.neg_positive, neg_neg, signature_ofRank_swap, signature_ofRank_swap,
      signature_ofRank_positive' hk, Prod.swap_add, add_right_inj]
    split_ifs <;> simp

lemma signature_ofRank_sum_even {ε : GeneType} {m n : ℕ} (h : Even (m + n)) :
    (Gene.ofRank m ε).signature + (Gene.ofRank n (- ε)).signature =
    ((m + n : ℚ) / 2, (m + n : ℚ) / 2) := by
  by_cases hm : Even m
  · have hn := (Nat.even_add.1 h).1 hm
    rw [signature_ofRank_even_half hm, signature_ofRank_even_half hn,
      Prod.mk_add_mk, add_div]
  · by_cases hε : ε = .NonPolarized
    · rw [hε, signature_ofRank_nonPolarized, GeneType.neg_nonPolarized,
        signature_ofRank_nonPolarized, Prod.mk_add_mk, add_div]
    · have hn : ¬ Even n := (iff_false_right hm).1 (Nat.even_add.1 h).symm
      obtain ⟨kn, h1⟩ := Odd.exists_bit1 <| Nat.not_even_iff_odd.1 hn
      obtain ⟨km, h2⟩ := Odd.exists_bit1 <| Nat.not_even_iff_odd.1 hm
      rw [h1, h2, signature_ofRank_eq (Nat.le_add_left ..) hε, signature_ofRank_eq
        (Nat.le_add_left ..) (GeneType.neg_ne_nonPolarized_iff.1 hε),
        Nat.add_sub_cancel, Nat.add_sub_cancel, signature_ofRank_even_half (even_two_mul km),
        signature_ofRank_even_half (even_two_mul kn)]
      match ε, hε with
      | .Positive, _ => simp; ring_nf; tauto
      | .Negative, _ => simp; ring_nf; tauto

lemma signature_ofRank_nonPolarized_succ_add {ε : GeneType} {m n : ℕ} (h : Even (m + n)) :
    (Gene.ofRank (m + 1) .NonPolarized).signature + (Gene.ofRank n ε).signature =
    (Gene.ofRank m ε).signature + (Gene.ofRank (n + 1) .NonPolarized).signature := by
  rw [signature_ofRank_nonPolarized, signature_ofRank_nonPolarized]
  by_cases hm : Even m
  · have hn : Even n := (Nat.even_add.1 h).1 hm
    rw [signature_ofRank_even_half hm, signature_ofRank_even_half hn,
      Prod.mk_add_mk, Prod.mk_add_mk, Nat.cast_add, Nat.cast_add, add_div, add_div]
    ring_nf
  · have hn : ¬ Even n := (iff_false_right hm).1 (Nat.even_add.1 h).symm
    obtain ⟨km, hkm⟩ := Odd.exists_bit1 <| Nat.not_even_iff_odd.1 hm
    obtain ⟨kn, hkn⟩ := Odd.exists_bit1 <| Nat.not_even_iff_odd.1 hn
    by_cases hε : ε = .NonPolarized
    · rw [hε, signature_ofRank_nonPolarized, signature_ofRank_nonPolarized,
        Prod.mk_add_mk, Prod.mk_add_mk, Nat.cast_add, Nat.cast_add]; ring_nf
    · rw [hkm, hkn, signature_ofRank_eq (Nat.le_add_left ..) hε,
        signature_ofRank_eq (Nat.le_add_left 1 (2 * km)) hε, Nat.add_sub_cancel,
        Nat.add_sub_cancel, signature_ofRank_even_half (even_two_mul kn),
        signature_ofRank_even_half (even_two_mul km), ← add_assoc,
        add_comm _ (Gene.ofRank 1 ε).signature, add_comm _ (Gene.ofRank 1 ε).signature,
        add_assoc, add_assoc, add_right_inj]; simp; ring

lemma signature_ofRank_positive₂ {k : ℕ} (hk : 2 ≤ k) :
    (Gene.ofRank k .Positive).signature =
    (Gene.ofRank (k - 2) .Positive).signature + (1, 1) := by
  change _ = (Gene.ofRank (k - 1 - 1) .Positive).signature + _
  rw [signature_ofRank_positive (Nat.one_le_of_lt hk),
    signature_ofRank_eq (Nat.le_sub_one_of_lt hk) (by decide), add_assoc]; simp

lemma signature_ofRank_eq₂ {k : ℕ} {ε : GeneType} (hk : 2 ≤ k) :
    (Gene.ofRank k ε).signature =
    (Gene.ofRank (k - 2) ε).signature + (1, 1) := by
  match ε with
  | .NonPolarized =>
    rw [signature_ofRank_nonPolarized, signature_ofRank_nonPolarized, Nat.cast_sub hk,
      Prod.mk_add_mk, sub_div, Nat.cast_ofNat, div_self (by decide), sub_add_cancel]
  | .Positive => exact signature_ofRank_positive₂ hk
  | .Negative =>
    rw [← GeneType.neg_positive, signature_ofRank_swap,
      signature_ofRank_positive₂ hk, Prod.swap_add, ← signature_ofRank_swap]
    rfl

lemma signature_ofRank_eq₂' (k : ℕ) {ε : GeneType} :
    signature (Gene.ofRank (k + 2) ε) = signature (Gene.ofRank k ε) + (1, 1) :=
  signature_ofRank_eq₂ (by omega)

lemma signature_ofRank_succ_add_nonPolarized {ε : GeneType} {m n : ℕ} (h : Even (m + n)) :
    (Gene.ofRank (m + 1) ε).signature + (Gene.ofRank n .NonPolarized).signature =
    (Gene.ofRank m .NonPolarized).signature + (Gene.ofRank (n + 1) ε).signature := by
  have eq1 : m + 1 + (n + 1) = (m + n) + 2 := by omega
  have even : Even (m + 1 + (n + 1)) := by
    rw [eq1, Nat.even_add]; exact (iff_true_right (Nat.even_iff.2 rfl)).2 h
  have : (Gene.ofRank (m + 1) ε).signature +
      (Gene.ofRank (n + 2) .NonPolarized).signature =
      (Gene.ofRank (m + 2) .NonPolarized).signature + (Gene.ofRank (n + 1) ε).signature :=
    (@signature_ofRank_nonPolarized_succ_add ε (m + 1) (n + 1) even).symm
  rwa [signature_ofRank_eq₂', signature_ofRank_eq₂', ← add_assoc,
    add_assoc _ (1, 1), add_comm (1, 1), ← add_assoc, add_left_inj] at this

lemma signature_fst {X : Chromosome} :
    X.signature.1 = X.sum (fun g n ↦ (n : ℚ) • g.signature.1) :=
  map_sum (AddMonoidHom.fst ..) ..

lemma signature_snd {X : Chromosome} :
    X.signature.2 = X.sum (fun g n ↦ (n : ℚ) • g.signature.2) :=
  map_sum (AddMonoidHom.snd ..) ..

lemma signature_ofRank_ge {ε : GeneType} {k : ℕ} :
    ((k - 1 : ℚ) / 2, (k - 1 : ℚ) / 2) ≤ (Gene.ofRank k ε).signature := by
  rw [signature_ofRank]
  split_ifs with h1
  · rw [h1, Nat.cast_zero, zero_sub]; decide +kernel
  · exact Gene.signature_ge ⟨k, ε, Nat.one_le_iff_ne_zero.2 h1⟩

lemma signature_ofRank_le {ε : GeneType} {k : ℕ} :
    (Gene.ofRank k ε).signature ≤ ((k + 1 : ℚ) / 2, (k + 1 : ℚ) / 2) := by
  rw [signature_ofRank]
  split_ifs with h1
  · rw [h1, Nat.cast_zero]; decide +kernel
  · exact Gene.signature_le ⟨k, ε, Nat.one_le_iff_ne_zero.2 h1⟩

end signature

end Chromosome
