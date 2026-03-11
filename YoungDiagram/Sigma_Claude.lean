import YoungDiagram.Chromosome
import YoungDiagram.Variety
import YoungDiagram.Mutations
import YoungDiagram.SigmaAux_Claude

open Chromosome

namespace Sigma

/--
For `X ∈ Π`, `σ(X)` is the 2×∞ nonneg integral matrix whose k-th column is
`(aₖ, bₖ) = sig X^(k)`, as defined in [Djoković 1982, (15.1)].

Represented as a function `ℕ → ℚ × ℚ`, where the first component is `aₖ`
and the second is `bₖ`.
-/
noncomputable def sigma (X : Variety.Pi) : ℕ → ℚ × ℚ :=
  fun k => signature (prime^[k] X)

/-- The `aₖ` entry of σ(X): the first component of sig X^(k). -/
noncomputable def a (X : Variety.Pi) (k : ℕ) : ℚ := (sigma X k).1

/-- The `bₖ` entry of σ(X): the second component of sig X^(k). -/
noncomputable def b (X : Variety.Pi) (k : ℕ) : ℚ := (sigma X k).2

-- (15.2) a₀ ≥ a₁ ≥ a₂ ≥ …
-- Each step reduces to sig_prime_le_fst applied to prime^[k] X.
lemma cond_15_2_antitone (X : Variety.Pi) : ∀ k, a X (k + 1) ≤ a X k := fun k => by
  simp only [a]
  simp only [sigma]
  rw [prime_prime_other k X]
  exact sig_prime_le_fst ⟨prime^[k] X, prime_k_mem_pi X k⟩

-- (15.2) aₖ = 0 for large k.
lemma cond_15_2_eventually_zero (X : Variety.Pi) : ∃ K, ∀ k ≥ K, a X k = 0 := by
  use X.val.maxRank
  intro k hk
  simp only [a, sigma]
  -- Every gene in X has rank ≤ maxRank X, so X.below (maxRank X) = X
  have hbelow : X.val.below X.val.maxRank = X.val := by
    rw [below_def, ← IsFiltered_def]
    exact IsFiltered_def'.mpr fun g hg => by
      simp only [maxRank]; exact Finset.le_sup hg
  -- prime^[maxRank X] X = 0 by prime_below (with n = k = maxRank X)
  have hprime_zero : prime^[X.val.maxRank] X.val = 0 := by
    have h : prime^[X.val.maxRank] (X.val.below X.val.maxRank) = 0 := prime_below le_rfl
    rwa [hbelow] at h
  -- prime^[j] 0 = 0 for any j, since prime is an AddMonoidHom
  have hiter_zero : prime^[k - X.val.maxRank] (0 : Chromosome) = 0 :=
    Function.iterate_fixed (map_zero prime) _
  -- Split k = (k - maxRank X) + maxRank X so that prime^[maxRank] is innermost
  -- Function.iterate_add_apply: f^[m+n] x = f^[m] (f^[n] x)
  rw [show k = (k - X.val.maxRank) + X.val.maxRank from (Nat.sub_add_cancel hk).symm,
      Function.iterate_add_apply, hprime_zero, hiter_zero, map_zero]
  rfl

-- (15.2) a₀ ≥ a₁ ≥ a₂ ≥ …, and aₖ = 0 for large k.
lemma cond_15_2 (X : Variety.Pi) :
    (∀ k, a X (k + 1) ≤ a X k) ∧ (∃ K, ∀ k ≥ K, a X k = 0) :=
  ⟨cond_15_2_antitone X, cond_15_2_eventually_zero X⟩

-- (15.3) b₀ ≥ b₁ ≥ b₂ ≥ …
-- Each step reduces to sig_prime_le_snd applied to prime^[k] X.
lemma cond_15_3_antitone (X : Variety.Pi) : ∀ k, b X (k + 1) ≤ b X k := fun k => by
  simp only [b]
  simp only [sigma]
  rw [prime_prime_other k X]
  exact sig_prime_le_snd ⟨prime^[k] X, prime_k_mem_pi X k⟩

-- (15.3) bₖ = 0 for large k.
lemma cond_15_3_eventually_zero (X : Variety.Pi) : ∃ K, ∀ k ≥ K, b X k = 0 := by
  use X.val.maxRank
  intro k hk
  simp only [b, sigma]
  have hbelow : X.val.below X.val.maxRank = X.val := by
    rw [below_def, ← IsFiltered_def]
    exact IsFiltered_def'.mpr fun g hg => by
      simp only [maxRank]; exact Finset.le_sup hg
  have hprime_zero : prime^[X.val.maxRank] X.val = 0 := by
    have h : prime^[X.val.maxRank] (X.val.below X.val.maxRank) = 0 := prime_below le_rfl
    rwa [hbelow] at h
  have hiter_zero : prime^[k - X.val.maxRank] (0 : Chromosome) = 0 :=
    Function.iterate_fixed (map_zero prime) _
  rw [show k = (k - X.val.maxRank) + X.val.maxRank from (Nat.sub_add_cancel hk).symm,
      Function.iterate_add_apply, hprime_zero, hiter_zero, map_zero]
  rfl

-- (15.3) b₀ ≥ b₁ ≥ b₂ ≥ …, and bₖ = 0 for large k.
lemma cond_15_3 (X : Variety.Pi) :
    (∀ k, b X (k + 1) ≤ b X k) ∧ (∃ K, ∀ k ≥ K, b X k = 0) :=
  ⟨cond_15_3_antitone X, cond_15_3_eventually_zero X⟩

-- (15.4) a₀ ≥ b₁ ≥ a₂ ≥ b₃ ≥ …
-- At each step k: if k is even then aₖ ≥ b_{k+1}, else bₖ ≥ a_{k+1}.
lemma cond_15_4 (X : Variety.Pi) (k : ℕ) :
    if Even k then b X (k + 1) ≤ a X k
              else a X (k + 1) ≤ b X k := by
  sorry

-- (15.5) b₀ ≥ a₁ ≥ b₂ ≥ a₃ ≥ …
-- At each step k: if k is even then bₖ ≥ a_{k+1}, else aₖ ≥ b_{k+1}.
lemma cond_15_5 (X : Variety.Pi) (k : ℕ) :
    if Even k then a X (k + 1) ≤ b X k
              else b X (k + 1) ≤ a X k := by
  sorry

-- (15.6) a₀ − a₁ ≥ b₁ − b₂ ≥ a₂ − a₃ ≥ b₃ − b₄ ≥ …
-- The k-th term of the chain is (aₖ − a_{k+1}) when k is even,
-- and (bₖ − b_{k+1}) when k is odd; consecutive terms are non-increasing.
lemma cond_15_6 (X : Variety.Pi) (k : ℕ) :
    if Even k then b X (k + 1) - b X (k + 2) ≤ a X k - a X (k + 1)
              else a X (k + 1) - a X (k + 2) ≤ b X k - b X (k + 1) := by
  sorry

-- (15.7) b₀ − b₁ ≥ a₁ − a₂ ≥ b₂ − b₃ ≥ a₃ − a₄ ≥ …
-- The k-th term of the chain is (bₖ − b_{k+1}) when k is even,
-- and (aₖ − a_{k+1}) when k is odd; consecutive terms are non-increasing.
lemma cond_15_7 (X : Variety.Pi) (k : ℕ) :
    if Even k then a X (k + 1) - a X (k + 2) ≤ b X k - b X (k + 1)
              else b X (k + 1) - b X (k + 2) ≤ a X k - a X (k + 1) := by
  sorry

end Sigma
