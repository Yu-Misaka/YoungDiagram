import YoungDiagram.Mutations.Pi

open Chromosome Finsupp

lemma cond_15_6_ofRank (k : ℕ) {ε : GeneType} (hε : ε ≠ .NonPolarized) :
    (Gene.ofRank k ε).prime.signature - (Gene.ofRank k ε).prime.prime.signature ≤
    ((Gene.ofRank k ε).signature - (Gene.ofRank k ε).prime.signature).swap := by
  rw [prime_ofRank, prime_ofRank]
  by_cases hk : 1 ≤ k - 1
  · rw [signature_ofRank_eq' hk hε, add_sub_cancel_left]
    replace hk : 2 ≤ k := by omega
    rw [signature_ofRank_eq₂ hk, show k - 1 - 1 = k - 2 by rfl, add_comm,
      add_sub_assoc, sub_add_cancel_left, Prod.swap_add, Prod.swap_prod_mk,
      Prod.swap_neg, le_add_neg_iff_add_le]
    split_ifs
    · rw [← signature_ofRank_swap, neg_neg, signature_ofRank, signature_ofRank,
        dif_neg Nat.one_ne_zero, dif_neg Nat.one_ne_zero, add_comm, Gene.signature_sum_neg_eq_rank]
      rfl
    · rw [← signature_ofRank_swap, signature_ofRank, signature_ofRank,
        dif_neg Nat.one_ne_zero, dif_neg Nat.one_ne_zero, Gene.signature_sum_neg_eq_rank]
      rfl
  · obtain (hk | hk) : k = 1 ∨ k = 0 := by omega
    all_goals subst hk
    · simp only [tsub_self, Gene.ofRank_zero, map_zero, zero_tsub, sub_self, sub_zero]
      exact Prod.mk_le_swap.2 (signature_nonneg _)
    · simp only [zero_le, Nat.sub_eq_zero_of_le, Gene.ofRank_zero, map_zero, sub_self,
        Prod.swap_zero, Std.le_refl]

open Variety in
lemma cond_15_6_Pi {Y : Chromosome} (hY : Y ∈ Pi) :
    Y.prime.signature - Y.prime.prime.signature ≤
    (Y.signature - Y.prime.signature).swap := by
  induction Y using Finsupp.induction with
  | zero => simp only [map_zero, sub_self, Prod.swap_zero, Std.le_refl]
  | single_add a b f ha hb hf => calc
    _ = (prime f).signature - (prime f).prime.signature +
        ((prime (single a b)).signature - (prime (single a b)).prime.signature) := by
      simp_rw [map_add, sub_add_eq_sub_sub]; ring
    _ ≤ (signature f - signature (prime f)).swap +
        ((prime (single a b)).signature - (prime (single a b)).prime.signature) :=
      add_le_add_left (hf (mem_Pi_iff_add.1 hY).2) _
    _ ≤ _ := by
      simp_rw [Prod.swap_sub, map_add, Prod.swap_add]
      rw [sub_eq_add_neg, add_comm (signature (single a b)).swap, add_sub_assoc, add_assoc]
      refine add_le_add_right ?_ (signature f).swap
      rw [sub_add_eq_sub_sub, sub_eq_add_neg _ (signature (prime f)).swap,
        add_comm]
      refine add_le_add_left ?_ (-(signature (prime f)).swap)
      simp_rw [← Gene.ofRank_eq_gene_smul, map_nsmul, Prod.smul_swap, ← smul_sub]
      have := (IsFiltered_single hb).1 <| mem_Pi_iff.1 (mem_Pi_iff_add.1 hY).1
      refine nsmul_le_nsmul_right ((cond_15_6_ofRank a.rank this).trans ?_) b
      rw [Prod.swap_sub]

namespace Sigma

variable (X : Chromosome) (k : ℕ)

/--
For `X ∈ Π`, `σ(X)` is the 2×∞ nonneg integral matrix whose k-th column is
`(aₖ, bₖ) = sig X^(k)`, as defined in [Djoković 1982, (15.1)].

Represented as a function `ℕ → ℚ × ℚ`, where the first component is `aₖ`
and the second is `bₖ`.
-/
noncomputable def sigma : ℕ → ℚ × ℚ :=
  fun k ↦ signature (prime^[k] X)

local notation "a" X:max k:max => Prod.fst (sigma X k)

local notation "b" X:max k:max => Prod.snd (sigma X k)

lemma sigma_linearity {X Y : Chromosome} {i : ℕ} :
    sigma (X + Y) i = (sigma X i) + (sigma Y i) := by
  simp [sigma]

/-- The componentwise drop from the `k`-th sigma column to the next one. -/
noncomputable def drop : ℚ × ℚ :=
  sigma X k - sigma X (k + 1)

@[simp] lemma drop_fst : (drop X k).1 = a X k - a X (k + 1) := rfl

@[simp] lemma drop_snd : (drop X k).2 = b X k - b X (k + 1) := rfl

lemma antitone : Antitone (sigma X) := by
  refine antitone_nat_of_succ_le (fun _ ↦ ?_)
  simp only [sigma, Function.iterate_succ_apply']
  exact (signature_prime_le _).trans inf_le_left

lemma eventually_zero : ∃ K, ∀ k ≥ K, sigma X k = 0 := by
  refine ⟨X.maxRank, fun k hk ↦ ?_⟩
  simp only [sigma]
  have hprime_zero : prime^[X.maxRank] X = 0 := by
    have h : prime^[X.maxRank] (X.below X.maxRank) = 0 := prime_below le_rfl
    rwa [below_maxRank] at h
  rw [← Nat.sub_add_cancel hk, Function.iterate_add_apply,
    hprime_zero, iterate_map_zero, map_zero]

lemma cond_15_2 : (∀ k, a X (k + 1) ≤ a X k) ∧ (∃ K, ∀ k ≥ K, a X k = 0) :=
  ⟨fun k ↦ (Prod.le_def.1 (antitone X (Nat.le_add_right k 1))).1,
    (eventually_zero X).imp fun _ h1 k h2 ↦ congr_arg Prod.fst (h1 k h2)⟩

lemma cond_15_3 : (∀ k, b X (k + 1) ≤ b X k) ∧ (∃ K, ∀ k ≥ K, b X k = 0) :=
  ⟨fun k ↦ (antitone X (Nat.le_add_right k 1)).2,
    (eventually_zero X).imp fun _ h1 k h2 ↦ congr_arg Prod.snd (h1 k h2)⟩

/-- (15.4) a₀ ≥ b₁ ≥ a₂ ≥ b₃ ≥ … -/
lemma cond_15_4 : if Even k then b X (k + 1) ≤ a X k
    else a X (k + 1) ≤ b X k := by
  split_ifs <;> simp only [sigma, Function.iterate_succ_apply']
  · exact ((signature_prime_le _).trans inf_le_right).2
  · exact ((signature_prime_le _).trans inf_le_right).1

/-- (15.5) b₀ ≥ a₁ ≥ b₂ ≥ a₃ ≥ … -/
lemma cond_15_5 : if Even k then a X (k + 1) ≤ b X k
    else b X (k + 1) ≤ a X k := by
  split_ifs <;> simp only [sigma, Function.iterate_succ_apply']
  · exact ((signature_prime_le _).trans inf_le_right).1
  · exact ((signature_prime_le _).trans inf_le_right).2

/-- (15.6) a₀ − a₁ ≥ b₁ − b₂ ≥ a₂ − a₃ ≥ b₃ − b₄ ≥ … -/
lemma cond_15_6 (hX : X ∈ Variety.Pi) :
    if Even k then b X (k + 1) - b X (k + 2) ≤ a X k - a X (k + 1)
              else a X (k + 1) - a X (k + 2) ≤ b X k - b X (k + 1) := by
  have h := cond_15_6_Pi (Variety.prime_mem_Pi_iterate hX (k := k))
  split_ifs with heven <;> simp only [sigma, Function.iterate_succ_apply']
  · exact (Prod.mk_le_swap.1 h).1
  · exact (Prod.mk_le_swap.1 h).2

/-- (15.7) b₀ − b₁ ≥ a₁ − a₂ ≥ b₂ − b₃ ≥ a₃ − a₄ ≥ … -/
lemma cond_15_7 (hX : X ∈ Variety.Pi) :
    if Even k then a X (k + 1) - a X (k + 2) ≤ b X k - b X (k + 1)
              else b X (k + 1) - b X (k + 2) ≤ a X k - a X (k + 1) := by
  have h := cond_15_6_Pi (Variety.prime_mem_Pi_iterate hX (k := k))
  split_ifs with heven <;> simp only [sigma, Function.iterate_succ_apply']
  · exact (Prod.mk_le_swap.1 h).2
  · exact (Prod.mk_le_swap.1 h).1

lemma cond_15_6_drop (hX : X ∈ Variety.Pi) :
    if Even k then (drop X (k + 1)).2 ≤ (drop X k).1
              else (drop X (k + 1)).1 ≤ (drop X k).2 := by
  simpa using cond_15_6 X k hX

lemma cond_15_7_drop (hX : X ∈ Variety.Pi) :
    if Even k then (drop X (k + 1)).1 ≤ (drop X k).2
              else (drop X (k + 1)).2 ≤ (drop X k).1 := by
  simpa using cond_15_7 X k hX

/-- (15.8) If `X < Y` in `Π` then `aₖ ≤ cₖ` and `bₖ ≤ dₖ` for all `k`,
where `(aₖ, bₖ) = σ(X)ₖ` and `(cₖ, dₖ) = σ(Y)ₖ`. -/
lemma cond_15_8 {X Y : Variety.Pi} (h : X < Y) (k : ℕ) :
    a X k ≤ a Y k ∧ b X k ≤ b Y k := le_iff_dominates.1 h.le k

/-- For `X ∈ Π`, both components of `σ(X)ₖ` are natural numbers (as elements of ℚ). -/
lemma sigma_isNat (hX : X ∈ Variety.Pi) : ∃ n : ℕ × ℕ, sigma X k = (↑n.1, ↑n.2) := by
  simp only [sigma]
  exact signature_pi_isNat (Variety.prime_mem_Pi_iterate hX)

end Sigma
