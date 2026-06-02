import YoungDiagram.Variety
import YoungDiagram.Mutations.Basic

open Chromosome

variable {ε : GeneType} {m n : ℕ}

local notation "type1X" => Gene.ofRank m ε + Gene.ofRank n (- ε)
local notation "type1Y" => Gene.ofRank (m - 1) (- ε) + Gene.ofRank (n + 1) ε

local notation "type2X" => Gene.ofRank m ε + Gene.ofRank n ε
local notation "type2Y" => Gene.ofRank (m - 2) ε + Gene.ofRank (n + 2) ε

local notation "type3X" => Gene.ofRankAlt m ε + Gene.ofRankAlt n (- ε)
local notation "type3Y" => Gene.ofRankAlt (m - 1) (- ε) + Gene.ofRankAlt (n + 1) ε

section Aux

section type1_isMutation

lemma mutation_type1_ne (h_le : m ≤ n) (hm : 1 ≤ m) : type1X ≠ type1Y := by
  intro h
  replace h := congr_arg (· ⟨m, ε, hm⟩) h
  have h_n : n ≠ 0 := by omega
  have h_m : m ≠ 0 := by omega
  simp only [Gene.ofRank_def, h_m, ↓reduceDIte, h_n, Finsupp.coe_add, Pi.add_apply,
    Finsupp.single_eq_same, Nat.add_eq_zero_iff, one_ne_zero, and_self] at h
  split_ifs at h <;> (simp [Finsupp.single_apply] at h; grind)

lemma mutation_type1_iterate_signature_eq (hε : ε ≠ .NonPolarized)
  (h_le : m ≤ n) (hm : 1 ≤ m) (i k : ℕ) (hi : i ≤ k) :
    (prime^[i] (Gene.ofRank (m + k) ε + Gene.ofRank (n + k) (- ε))).signature =
    (prime^[i] (Gene.ofRank (m + k - 1) (- ε) + Gene.ofRank (n + k + 1) ε)).signature := by
  rw [iterate_map_add, iterate_map_add, prime_iterate_ofRank, prime_iterate_ofRank,
    prime_iterate_ofRank, prime_iterate_ofRank, map_add, map_add,
    signature_ofRank_eq (k := (m + k - i)) (by omega) hε,
    signature_ofRank_eq (k := (n + k + 1 - i)) (by omega) hε, Nat.sub_right_comm,
    show n + k + 1 - i - 1 = n + k - i by exact Nat.succ_sub_succ_eq_sub (n + k) i]
  ac_rfl

lemma mutation_type1_signature_eq (hε : ε ≠ .NonPolarized) (h_le : m ≤ n) (hm : 1 ≤ m) :
    signature type1X = signature type1Y := by
  have := mutation_type1_iterate_signature_eq hε h_le hm 0 0 le_rfl
  rwa [Function.iterate_zero_apply, Function.iterate_zero_apply, add_zero, add_zero] at this

lemma mutation_type1_le (hε : ε ≠ .NonPolarized) (h_le : m ≤ n) : type1X ≤ type1Y := by
  intro k
  simp only [iterate_map_add, map_add, prime_iterate_ofRank]
  by_cases hk1 : n < k
  · have eq1 : m - 1 - k = 0 := by omega
    simp only [Nat.sub_eq_zero_iff_le.2 (h_le.trans hk1.le), Gene.ofRank_zero, map_zero,
      Nat.sub_eq_zero_of_le hk1.le, add_zero, eq1, zero_add, ge_iff_le]
    exact signature_nonneg _
  by_cases hk2 : m ≤ k
  · have eq1 : m - 1 - k = 0 := by omega
    rw [signature_ofRank_eq (k := n + 1 - k) (by omega) hε, Nat.succ_sub_sub_succ]
    simp only [Nat.sub_eq_zero_of_le hk2, Gene.ofRank_zero, map_zero, zero_add, eq1, Nat.sub_zero,
      le_add_iff_nonneg_right, ge_iff_le]
    exact signature_nonneg _
  · have le1 : 1 ≤ m - k := by omega
    have le2 : 1 ≤ n + 1 - k := by omega
    rw [signature_ofRank_eq le1 hε, signature_ofRank_eq le2 hε,
      Nat.succ_sub_sub_succ, Nat.sub_zero, Nat.sub_right_comm]
    exact le_of_eq <| by ac_rfl

end type1_isMutation

section type2_isMutation

lemma mutation_type2_ne (h_le : m ≤ n) (hm : 1 < m) : type2X ≠ type2Y := by
  intro h
  replace h := congr_arg (· ⟨m, ε, le_of_lt hm⟩) h
  have h_n : n ≠ 0 := by omega
  have h_m : m ≠ 0 := by omega
  simp only [Gene.ofRank_def, h_m, ↓reduceDIte, h_n, Finsupp.coe_add, Pi.add_apply,
    Finsupp.single_eq_same, Nat.add_eq_zero_iff, OfNat.ofNat_ne_zero, and_self] at h
  split_ifs at h <;> (simp [Finsupp.single_apply] at h; grind)

lemma mutation_type2_iterate_signature_eq
  (h_le : m ≤ n) (hm : 1 < m) (i k : ℕ) (hi : i ≤ k) :
    (prime^[i] (Gene.ofRank (m + k) ε + Gene.ofRank (n + k) ε)).signature =
    (prime^[i] (Gene.ofRank (m + k - 2) ε + Gene.ofRank (n + k + 2) ε)).signature := by
  rw [iterate_map_add, iterate_map_add, prime_iterate_ofRank, prime_iterate_ofRank,
    prime_iterate_ofRank, prime_iterate_ofRank, map_add, map_add,
    signature_ofRank_eq₂ (k := (m + k - i)) (by omega),
    signature_ofRank_eq₂ (k := (n + k + 2 - i)) (by omega), Nat.sub_right_comm,
    show n + k + 2 - i - 2 = n + k - i by omega]
  ac_rfl

lemma mutation_type2_signature_eq (h_le : m ≤ n) (hm : 1 < m) :
    signature type2X = signature type2Y := by
  have := mutation_type2_iterate_signature_eq (ε := ε) h_le hm 0 0 le_rfl
  rwa [Function.iterate_zero_apply, Function.iterate_zero_apply, add_zero, add_zero] at this

lemma mutation_type2_le (hε : ε ≠ .NonPolarized) (h_le : m ≤ n) (hm : 1 < m) :
    type2X ≤ type2Y := by
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
      signature_ofRank_eq₂ (k := n + 2 - k) (by omega), eq1, add_comm]
    gcongr
    have le1 : m - k < 2 := by omega
    match (m - k), le1 with
    | 0, _ => rw [Gene.ofRank_zero, map_zero]; decide
    | 1, _ => match ε, hε with | .Positive, _ => simp | .Negative, _ => simp
  · have eq1 : n + 2 - k - 2 = n - k := by omega
    rw [signature_ofRank_eq₂ (k := n + 2 - k) (by omega), eq1,
      signature_ofRank_eq₂ (k := m - k) (by omega), Nat.sub_right_comm]
    exact le_of_eq <| by ac_rfl

end type2_isMutation

section type3_isMutation

lemma mutation_type3_ne (h_le : m ≤ n) (hm : 1 ≤ m) : type3X ≠ type3Y := by
  dsimp [Gene.ofRankAlt, Gene.ofRank]
  split_ifs <;> try omega
  · expose_names
    intro h
    have := congr_arg (· ⟨1, ε, le_rfl⟩) h
    simp [Finsupp.single_apply, Nat.le_antisymm (Nat.le_of_sub_eq_zero h_2) hm, h_1] at this
  · intro h
    have := congr_arg Finsupp.toMultiset h
    simp [Multiset.cons_eq_cons] at this
    omega

lemma mutation_type3_iterate_signature_eq (hε : ε ≠ .NonPolarized)
  (h_le : m ≤ n) (hm : 1 ≤ m) (i k : ℕ) (hi : i ≤ k) :
    (prime^[i] (Gene.ofRankAlt (m + k) (Int.negOnePow k • ε) +
      Gene.ofRankAlt (n + k) (Int.negOnePow k • - ε))).signature =
    (prime^[i] (Gene.ofRankAlt (m + k - 1) (Int.negOnePow k • - ε) +
      Gene.ofRankAlt (n + k + 1) (Int.negOnePow k • ε))).signature := by
  simp only [Gene.ofRankAlt_def, Nat.cast_add, GeneType.negOnePow_smul_smul,
    GeneType.negOnePow_smul_neg, sub_add_add_cancel, iterate_map_add, prime_iterate_ofRank, map_add,
    Nat.cast_one, add_sub_cancel_right]
  have le1 : 1 ≤ m + k - i := by omega
  have le2 : 1 ≤ n + k + 1 - i := by omega
  rw [signature_ofRank_eq' le1 (GeneType.smul_ne_nonPolarized_iff.1 hε),
    signature_ofRank_eq' le2 (GeneType.smul_ne_nonPolarized_iff.1 hε),
    Nat.sub_right_comm, Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_one, add_assoc,
    add_right_inj, Nat.succ_sub_sub_succ, Nat.sub_zero,
    add_comm (signature (Gene.ofRank (n + k - i) _)), add_left_inj]
  convert_to (if Even (m + k - i) then signature (Gene.ofRank 1 ((m + 2 * k : ℤ).negOnePow • ε))
    else signature (Gene.ofRank 1 ((m - 1 + 2 * k : ℤ).negOnePow • ε))) =
      if Even (n + k + 1 - i) then signature (Gene.ofRank 1 (-((n + 2 * k : ℤ).negOnePow • ε)))
    else signature (Gene.ofRank 1 ((n + 2 * k : ℤ).negOnePow • ε))
  · congr 5
    · rw [GeneType.neg_negOnePow_smul]
      congr 2; omega
    · omega
  · congr 5 <;> rw [two_mul (k : ℤ), add_assoc]
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

lemma mutation_type3_signature_eq (hε : ε ≠ .NonPolarized) (h_le : m ≤ n) (hm : 1 ≤ m) :
    signature type3X = signature type3Y := by
  have := mutation_type3_iterate_signature_eq hε h_le hm 0 0 le_rfl
  rwa [Function.iterate_zero_apply, Function.iterate_zero_apply, add_zero, add_zero] at this

lemma mutation_type3_le (hε : ε ≠ .NonPolarized) (h_le : m ≤ n) (hm : 1 ≤ m) :
    type3X ≤ type3Y := by
  intro k
  simp only [iterate_map_add, map_add, prime_iterate_ofRank]
  by_cases hk1 : n < k
  · have eq1 : m - 1 - k = 0 := by omega
    simp only [Nat.sub_eq_zero_iff_le.2 (h_le.trans hk1.le), Gene.ofRank_zero, map_zero,
      Nat.sub_eq_zero_of_le hk1.le, GeneType.negOnePow_smul_neg, sub_add_cancel, add_zero, eq1,
      Nat.cast_add, Nat.cast_one, add_sub_cancel_right, zero_add, ge_iff_le]
    exact signature_nonneg _
  by_cases hk2 : m ≤ k
  · have eq1 : m - 1 - k = 0 := by omega
    simp only [Nat.sub_eq_zero_of_le hk2, Gene.ofRank_zero, map_zero, GeneType.negOnePow_smul_neg,
      sub_add_cancel, zero_add, eq1, Nat.cast_add, Nat.cast_one, add_sub_cancel_right, ge_iff_le]
    rw [signature_ofRank_eq' (k := n + 1 - k) (by omega), Nat.succ_sub_sub_succ,
      Nat.sub_zero, le_add_iff_nonneg_right]
    · split_ifs <;> exact signature_nonneg _
    · exact GeneType.smul_ne_nonPolarized_iff.1 hε
  · have le1 : 1 ≤ m - k := by omega
    have le2 : 1 ≤ n + 1 - k := by omega
    rw [signature_ofRank_eq' le1, signature_ofRank_eq' le2, Nat.succ_sub_sub_succ,
      Nat.sub_zero, Nat.sub_right_comm, add_assoc, add_comm (signature (Gene.ofRank (n - k) _))]
    swap; · exact GeneType.smul_ne_nonPolarized_iff.1 hε
    swap; · exact GeneType.smul_ne_nonPolarized_iff.1 hε
    gcongr
    · simp only [hm, Nat.cast_sub, Nat.cast_one, GeneType.smul_neg, GeneType.neg_negOnePow_smul,
      sub_add_cancel, le_refl]
    · have eq1 : n + 1 - k = n - k + 1 := by omega
      simp_rw [Int.negOnePow_sub, Int.negOnePow_one, mul_neg_one, GeneType.neg_smul, neg_neg, eq1,
        Nat.even_add_one, Nat.even_sub (Nat.le_of_not_ge hk2), Nat.even_sub (Nat.le_of_not_lt hk1),
        GeneType.negOnePow_smul', Nat.even_add_one, iff_iff_and_or_not_and_not, ite_not, ite_or,
        ite_and]
      split_ifs <;> first | exact le_rfl | rw [neg_neg]
    · simp

end type3_isMutation

end Aux

open Variety

namespace Pi

variable (hε : ε ≠ .NonPolarized)

noncomputable section type1

variable (hle : m ≤ n) (hm : 1 ≤ m)

def X1 : Pi := by
  use type1X
  rw [mem_Pi_iff, IsPolarized_iff_add]
  exact ⟨by rwa [IsPolarized_ofRank hm],
    by rwa [IsPolarized_ofRank (hm.trans hle),
      ← GeneType.neg_ne_nonPolarized_iff]⟩

lemma X1_eq : X1 hε hle hm =
  Gene.ofRank m ε + Gene.ofRank n (- ε) := rfl

@[simp] lemma neg_X1 : - (X1 hε hle hm) =
    X1 (GeneType.neg_ne_nonPolarized_iff.1 hε) hle hm := by
  ext; rw [neg_val, X1_eq, X1_eq, Chromosome.neg_add, neg_ofRank, neg_ofRank]

def Y1 : Pi := by
  use type1Y
  rw [mem_Pi_iff, IsPolarized_iff_add]
  refine ⟨?_, by rwa [IsPolarized_ofRank (Nat.le_add_left 1 n)]⟩
  match m with
  | 1 =>
    rw [← mem_Pi_iff, Nat.sub_self, Gene.ofRank_zero]
    exact zero_mem _
  | m + 2 =>
    rwa [IsPolarized_ofRank (Nat.le_of_ble_eq_true rfl),
      ← GeneType.neg_ne_nonPolarized_iff]

lemma Y1_eq : Y1 hε hle hm =
  Gene.ofRank (m - 1) (- ε) + Gene.ofRank (n + 1) ε := rfl

@[simp] lemma neg_Y1 : - (Y1 hε hle hm) =
    Y1 (GeneType.neg_ne_nonPolarized_iff.1 hε) hle hm := by
  ext; rw [neg_val, Y1_eq, Y1_eq, Chromosome.neg_add, neg_ofRank, neg_ofRank]

end type1

noncomputable section type2

variable (hle : m ≤ n) (hm : 1 < m)

def X2 : Pi := by
  use type2X
  rw [mem_Pi_iff, IsPolarized_iff_add]
  exact ⟨by rwa [IsPolarized_ofRank (le_of_lt hm)],
    by rwa [IsPolarized_ofRank ((le_of_lt hm).trans hle)]⟩

lemma X2_eq : X2 hε hle hm =
  Gene.ofRank m ε + Gene.ofRank n ε := rfl

@[simp] lemma neg_X2 : - (X2 hε hle hm) =
    X2 (GeneType.neg_ne_nonPolarized_iff.1 hε) hle hm := by
  ext; rw [neg_val, X2_eq, X2_eq, Chromosome.neg_add, neg_ofRank, neg_ofRank]

def Y2 : Pi := by
  use type2Y
  rw [mem_Pi_iff, IsPolarized_iff_add]
  refine ⟨?_, by rwa [IsPolarized_ofRank (Nat.le_add_left 1 (n + 1))]⟩
  match m with
  | 2 =>
    rw [← mem_Pi_iff, Nat.sub_self, Gene.ofRank_zero]
    exact zero_mem _
  | m + 3 => rwa [IsPolarized_ofRank (by omega)]

lemma Y2_eq : Y2 hε hle hm =
  Gene.ofRank (m - 2) ε + Gene.ofRank (n + 2) ε := rfl

@[simp] lemma neg_Y2 : - (Y2 hε hle hm) =
    Y2 (GeneType.neg_ne_nonPolarized_iff.1 hε) hle hm := by
  ext; rw [neg_val, Y2_eq, Y2_eq, Chromosome.neg_add, neg_ofRank, neg_ofRank]


end type2

noncomputable section type3

variable (hle : m ≤ n) (hm : 1 ≤ m)

def X3 : Pi := by
  use type3X
  rw [mem_Pi_iff, IsPolarized_iff_add]
  exact ⟨by rwa [IsPolarized_ofRankAlt hm], by
    rwa [IsPolarized_ofRankAlt (hm.trans hle),
      ← GeneType.neg_ne_nonPolarized_iff]⟩

lemma X3_eq : X3 hε hle hm =
  Gene.ofRankAlt m ε + Gene.ofRankAlt n (- ε) := rfl

@[simp] lemma neg_X3 : - (X3 hε hle hm) =
    X3 (GeneType.neg_ne_nonPolarized_iff.1 hε) hle hm := by
  ext; rw [neg_val, X3_eq, X3_eq, Chromosome.neg_add, neg_ofRankAlt, neg_ofRankAlt]

def Y3 : Pi := by
  use type3Y
  rw [mem_Pi_iff, IsPolarized_iff_add]
  refine ⟨?_, by rwa [IsPolarized_ofRankAlt (by omega)]⟩
  match m with
  | 1 =>
    rw [Nat.sub_self, Gene.ofRankAlt_def, Gene.ofRank_zero, ← mem_Pi_iff]
    exact zero_mem _
  | m + 2 => rwa [IsPolarized_ofRankAlt (by omega),
    GeneType.neg_ne_nonPolarized_iff, neg_neg]

lemma Y3_eq : Y3 hε hle hm =
  Gene.ofRankAlt (m - 1) (- ε) + Gene.ofRankAlt (n + 1) ε := rfl

@[simp] lemma neg_Y3 : - (Y3 hε hle hm) =
    Y3 (GeneType.neg_ne_nonPolarized_iff.1 hε) hle hm := by
  ext; rw [neg_val, Y3_eq, Y3_eq, Chromosome.neg_add, neg_ofRankAlt, neg_ofRankAlt]

end type3

inductive Primitive : Pi → Pi → Prop
  | type1 (ε : GeneType) (hε : ε ≠ .NonPolarized)
    {m n : ℕ} (hle : m ≤ n) (hm : 1 ≤ m) :
      Primitive (X1 hε hle hm) (Y1 hε hle hm)
  | type2 (ε : GeneType) (hε : ε ≠ .NonPolarized)
    {m n : ℕ} (hle : m ≤ n) (hm : 1 < m) :
      Primitive (X2 hε hle hm) (Y2 hε hle hm)
  | type3 (ε : GeneType) (hε : ε ≠ .NonPolarized)
    {m n : ℕ} (hle : m ≤ n) (hm : 1 ≤ m) :
      Primitive (X3 hε hle hm) (Y3 hε hle hm)

inductive Step : Pi → Pi → Prop
  | mk (X Y Z : Pi) (h : Primitive X Y) :
      Step (X + Z) (Y + Z)

lemma Primitive.isMutation {X Y : Pi} (h : Primitive X Y) :
    IsMutation X Y := by
  cases h with
  | type1 ε hε hle hm =>
    exact ⟨mutation_type1_le hε hle,
      mutation_type1_ne hle hm, mutation_type1_signature_eq hε hle hm⟩
  | type2 ε hε hle hm =>
    exact ⟨mutation_type2_le hε hle hm,
      mutation_type2_ne hle hm, mutation_type2_signature_eq hle hm⟩
  | type3 ε hε hle hm =>
    exact ⟨mutation_type3_le hε hle hm,
      mutation_type3_ne hle hm, mutation_type3_signature_eq hε hle hm⟩

lemma Primitive.neg {X Y : Pi} (h : Primitive X Y) :
    Primitive (- X) (- Y) := by
  cases h with
  | type1 ε hε hle hm =>
    rw [neg_X1, neg_Y1]; exact Primitive.type1 ..
  | type2 ε hε hle hm =>
    rw [neg_X2, neg_Y2]; exact Primitive.type2 ..
  | type3 ε hε hle hm =>
    rw [neg_X3, neg_Y3]; exact Primitive.type3 ..

lemma Step.isMutation {X Y : Pi} (h : Pi.Step X Y) :
    IsMutation X Y := by
  cases h with
  | mk X Y Z h =>
    exact .add_right _ (Pi.Primitive.isMutation h)

lemma Step.neg {X Y : Pi} (h : Step X Y) : Step (- X) (- Y) := by
  cases h with
  | mk X Y Z hPrime =>
    rw [neg_add, neg_add]; exact Step.mk (- X) (- Y) (- Z) hPrime.neg

lemma Step.add_right (W : Variety.Pi) {A B : Variety.Pi}
    (h : Pi.Step A B) : Pi.Step (A + W) (B + W) := by
  cases h with
  | mk X Y Z hPrim =>
    rw [add_assoc, add_assoc]
    exact Pi.Step.mk X Y (Z + W) hPrim

lemma Step.of_neg {X Y : Pi} (h : Step (-X) (-Y)) : Step X Y := by
  rw [← neg_neg X, ← neg_neg Y]
  exact h.neg

end Pi
