import YoungDiagram.Variety

open Chromosome

variable {ε : GeneType} {m n : ℕ}

local notation "type2X" => Gene.ofRank m ε + Gene.ofRank n ε
local notation "type2Y" => Gene.ofRank (m - 2) ε + Gene.ofRank (n + 2) ε

section Aux

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

end Aux

open Variety

namespace Pi

variable (hε : ε ≠ .NonPolarized)

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

end Pi
