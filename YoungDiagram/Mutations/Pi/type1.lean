import YoungDiagram.Variety

open Chromosome

variable {ε : GeneType} {m n : ℕ}

local notation "type1X" => Gene.ofRank m ε + Gene.ofRank n (- ε)
local notation "type1Y" => Gene.ofRank (m - 1) (- ε) + Gene.ofRank (n + 1) ε

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

end Pi
