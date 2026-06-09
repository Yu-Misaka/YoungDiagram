import YoungDiagram.Variety.Pi
import YoungDiagram.Variety.Lambda

open Chromosome Pointwise

namespace Variety

section Mix

def Mix (v : Variety × Variety) : Variety where
  carrier := {X : Chromosome | X.evenPart ∈ v.1 ∧ X.oddPart ∈ v.2}
  add_mem' ha hb := by
    simp only [Set.mem_setOf_eq, map_add]
    exact ⟨add_mem ha.1 hb.1, add_mem ha.2 hb.2⟩
  zero_mem' := by
    simp only [Set.mem_setOf_eq, map_zero, zero_mem, and_self]

lemma mem_Mix_iff {X : Chromosome} {v : Variety × Variety} :
  X ∈ Mix v ↔ X.evenPart ∈ v.1 ∧ X.oddPart ∈ v.2 := .rfl

lemma neg_mem_Mix_iff {X : Chromosome} {v : Variety × Variety}
  (h1 : ∀ {Y}, Y ∈ v.1 ↔ -Y ∈ v.1)
  (h2 : ∀ {Y}, Y ∈ v.2 ↔ -Y ∈ v.2) :
    - X ∈ Mix v ↔ X ∈ Mix v := by
  rw [mem_Mix_iff, mem_Mix_iff, neg_evenPart, neg_oddPart, ← h1, ← h2]

lemma prime_Mix_le {v : Variety × Variety} :
    (Mix v).prime ≤ Mix ⟨v.2.prime, v.1.prime⟩ := by
  intro x hx
  change x.evenPart ∈ v.2.prime ∧ x.oddPart ∈ v.1.prime
  obtain ⟨y, ⟨h1 : y.evenPart ∈ v.1 ∧ y.oddPart ∈ v.2, h2⟩⟩ := hx
  rw [← h2, evenPart_prime, oddPart_prime]
  exact ⟨⟨y.oddPart, ⟨h1.2, rfl⟩⟩, ⟨y.evenPart, ⟨h1.1, rfl⟩⟩⟩

lemma prime_Mix_eq {v : Variety × Variety}
    (hv1 : ∀ {x}, x ∈ v.1 → x.oddPart ∈ v.1 ∧ x.evenPart ∈ v.1)
    (hv2 : ∀ {x}, x ∈ v.2 → x.oddPart ∈ v.2 ∧ x.evenPart ∈ v.2) :
    (Mix v).prime = Mix ⟨v.2.prime, v.1.prime⟩ := by
  refine le_antisymm prime_Mix_le (fun x hx ↦ ?_)
  obtain ⟨⟨y₁, ⟨h11, h12⟩⟩, ⟨y₂, ⟨h21, h22⟩⟩⟩ := hx
  have eq1 : (oddPart y₁).prime = evenPart x := by
    apply_fun evenPart at h12
    rwa [y₁.parity_decomposition, map_add, map_add, ← oddPart_prime,
      ← evenPart_prime, evenPart_idempotent, evenPart_idempotent,
      evenPart_oddPart, add_zero, evenPart_prime] at h12
  have eq2 : (evenPart y₂).prime = oddPart x := by
    apply_fun oddPart at h22
    rwa [y₂.parity_decomposition, map_add, map_add, ← oddPart_prime,
      ← evenPart_prime, oddPart_idempotent, oddPart_idempotent, oddPart_evenPart,
      zero_add, oddPart_prime] at h22
  refine ⟨y₁.oddPart + y₂.evenPart, ⟨add_mem ⟨?_, ?_⟩ ⟨?_, ?_⟩, ?_⟩⟩
  · rw [evenPart_oddPart]; exact zero_mem _
  · rw [oddPart_idempotent]; exact (hv2 h11).1
  · rw [evenPart_idempotent]; exact (hv1 h21).2
  · rw [oddPart_evenPart]; exact zero_mem _
  · rw [map_add, eq1, eq2, add_comm]; exact x.parity_decomposition.symm

lemma prime_Mix_Pi_Lambda : (Mix (Pi, Lambda)).prime = Mix (Lambda, Pi) := by
  rw [prime_Mix_eq parityDecomp_mem_Pi parityDecomp_mem_Lambda, prime_Pi, prime_Lambda]

lemma prime_Mix_Lambda_Pi : (Mix (Lambda, Pi)).prime = Mix (Pi, Lambda) := by
  rw [prime_Mix_eq parityDecomp_mem_Lambda parityDecomp_mem_Pi, prime_Pi, prime_Lambda]

lemma prime_Mix_2Lambda_Pi :
    (Mix (2 • Lambda, Pi)).prime = Mix (Pi, 2 • Lambda) := by
  rw [prime_Mix_eq parityDecomp_mem_smul_Lambda parityDecomp_mem_Pi,
    prime_Pi, variety_prime_smul, prime_Lambda]

lemma prime_Mix_Pi_2Lambda :
    (Mix (Pi, 2 • Lambda)).prime = Mix (2 • Lambda, Pi) := by
  rw [prime_Mix_eq parityDecomp_mem_Pi parityDecomp_mem_smul_Lambda,
    prime_Pi, variety_prime_smul, prime_Lambda]

end Mix

end Variety

namespace Chromosome

/-- `lift` shifts ranks by 1, so the even part of `lift (single g n)` is
`single ⟨g.rank+1, g.type, _⟩ n` if `g.rank` is odd (so `g.rank+1` is even),
else `0`. -/
private lemma evenPart_lift_single (g : Gene) (n : ℕ) :
    evenPart (lift (Finsupp.single g n)) = lift (oddPart (Finsupp.single g n)) := by
  have hg_pos : g.rank ≠ 0 := Nat.ne_zero_of_lt g.rank_pos
  -- Reduce to the case n = 1 by linearity.
  rw [← Finsupp.smul_single_one g n, map_nsmul, map_nsmul, map_nsmul, map_nsmul]
  congr 1
  -- Now goal: evenPart (lift (single g 1)) = lift (oddPart (single g 1))
  have lift_eq : lift (Finsupp.single g 1) =
      Finsupp.single ⟨g.rank + 1, g.type, Nat.le_add_left 1 g.rank⟩ 1 := by
    rw [show (Finsupp.single g 1 : Chromosome) = Gene.ofRank g.rank g.type from
      Gene.ofRank_eq_gene.symm, lift_ofRank hg_pos,
      Gene.ofRank_def, dif_neg (Nat.succ_ne_zero _)]
  rw [lift_eq, evenPart_single, oddPart_single]
  by_cases hg_even : Even g.rank
  · rw [if_pos hg_even, if_neg (by rw [Nat.even_add_one]; exact not_not.2 hg_even),
      map_zero]
  · rw [if_neg hg_even, if_pos (by rw [Nat.even_add_one]; exact hg_even), lift_eq]

/-- `lift` shifts ranks by 1, so the even part of `lift X` is the lift of the
odd part of `X`. -/
lemma evenPart_lift (X : Chromosome) : (lift X).evenPart = lift X.oddPart := by
  induction X using Finsupp.induction with
  | zero => simp
  | single_add g n f hg hn hf =>
    rw [map_add, map_add, map_add, map_add, hf, evenPart_lift_single]

/-- `lift` shifts ranks by 1, so the odd part of `lift X` is the lift of the
even part of `X`. -/
lemma oddPart_lift (X : Chromosome) : (lift X).oddPart = lift X.evenPart := by
  have hpd : lift X = (lift X).oddPart + (lift X).evenPart :=
    (lift X).parity_decomposition
  have hpdX : lift X = lift X.evenPart + lift X.oddPart := by
    rw [← map_add, add_comm, ← X.parity_decomposition]
  rw [evenPart_lift] at hpd
  -- hpd: lift X = (lift X).oddPart + lift X.oddPart
  -- hpdX: lift X = lift X.evenPart + lift X.oddPart
  have : (lift X).oddPart + lift X.oddPart = lift X.evenPart + lift X.oddPart :=
    hpd.symm.trans hpdX
  exact add_right_cancel this

/-- Iterated lift: both parity parts of `lift^[k] X` shift according to parity of `k`. -/
lemma evenPart_oddPart_lift_iterate (X : Chromosome) (k : ℕ) :
    (lift^[k] X).evenPart =
      (if Even k then lift^[k] X.evenPart else lift^[k] X.oddPart) ∧
    (lift^[k] X).oddPart =
      (if Even k then lift^[k] X.oddPart else lift^[k] X.evenPart) := by
  induction k with
  | zero => simp
  | succ k hk =>
    have iter_succ : ∀ Y : Chromosome, lift^[k+1] Y = lift (lift^[k] Y) :=
      fun Y ↦ Function.iterate_succ_apply' lift k Y
    have hodd_succ : ¬ Even k → Even (k + 1) := by
      intro h; rw [Nat.even_add_one]; exact h
    have heven_succ : Even k → ¬ Even (k + 1) := by
      intro h; rw [Nat.even_add_one]; exact not_not.2 h
    refine ⟨?_, ?_⟩
    · rw [iter_succ, evenPart_lift, hk.2, iter_succ, iter_succ]
      by_cases h : Even k
      · rw [if_pos h, if_neg (heven_succ h)]
      · rw [if_neg h, if_pos (hodd_succ h)]
    · rw [iter_succ, oddPart_lift, hk.1, iter_succ, iter_succ]
      by_cases h : Even k
      · rw [if_pos h, if_neg (heven_succ h)]
      · rw [if_neg h, if_pos (hodd_succ h)]

/-- Iterated lift: parity of `lift^[k] X` shifts according to parity of `k`. -/
lemma evenPart_lift_iterate (X : Chromosome) (k : ℕ) :
    (lift^[k] X).evenPart =
      if Even k then lift^[k] X.evenPart else lift^[k] X.oddPart :=
  (evenPart_oddPart_lift_iterate X k).1

/-- Iterated lift: parity of `lift^[k] X` shifts according to parity of `k`. -/
lemma oddPart_lift_iterate (X : Chromosome) (k : ℕ) :
    (lift^[k] X).oddPart =
      if Even k then lift^[k] X.oddPart else lift^[k] X.evenPart :=
  (evenPart_oddPart_lift_iterate X k).2

/-- Two filters compose as a conjunction. -/
private lemma filter_filter_eq {X : Chromosome} (p q : Gene → Prop)
    [DecidablePred p] [DecidablePred q] :
    (X.filter p).filter q = X.filter (fun g ↦ p g ∧ q g) := by
  ext g
  simp only [Finsupp.filter_apply]
  split_ifs <;> tauto

/-- `evenPart` commutes with `filter` on any predicate. -/
lemma evenPart_filter (X : Chromosome) (q : Gene → Prop) [DecidablePred q] :
    evenPart (X.filter q) = (evenPart X).filter q := by
  rw [evenPart_eq, evenPart_eq, filter_filter_eq, filter_filter_eq]
  congr 1
  funext g
  exact propext and_comm

/-- `oddPart` commutes with `filter` on any predicate. -/
lemma oddPart_filter (X : Chromosome) (q : Gene → Prop) [DecidablePred q] :
    oddPart (X.filter q) = (oddPart X).filter q := by
  rw [oddPart_eq, oddPart_eq, filter_filter_eq, filter_filter_eq]
  congr 1
  funext g
  exact propext and_comm

/-- `evenPart` commutes with `below`. -/
lemma evenPart_below (X : Chromosome) (k : ℕ) :
    evenPart (X.below k) = (evenPart X).below k :=
  evenPart_filter X _

/-- `oddPart` commutes with `below`. -/
lemma oddPart_below (X : Chromosome) (k : ℕ) :
    oddPart (X.below k) = (oddPart X).below k :=
  oddPart_filter X _

end Chromosome

namespace Variety

section MixLifting

/-! ## Helper lemmas for `mutation_lifting` over `Mix` varieties.

These lemmas mirror `prime_mem_Pi_iterate`, `IsPolarized_iff_iterate_lift`, and
`IsPolarized_filter` from `Variety/Pi.lean`, but adapted for the four Mix
varieties whose `Step` mutations need to be lifted: `Mix (Lambda, Pi)`,
`Mix (Pi, Lambda)`, `Mix (2 • Lambda, Pi)`, `Mix (Pi, 2 • Lambda)`.
-/

variable {X : Chromosome}

/-! ### Filter / below stability of `Mix v` -/

/-- If both components of a Mix variety are closed under filtering, so is
`Mix v` itself. -/
lemma filter_mem_Mix {v : Variety × Variety}
    (h1 : ∀ {Y : Chromosome} {q : Gene → Prop} [DecidablePred q], Y ∈ v.1 → Y.filter q ∈ v.1)
    (h2 : ∀ {Y : Chromosome} {q : Gene → Prop} [DecidablePred q], Y ∈ v.2 → Y.filter q ∈ v.2)
    (q : Gene → Prop) [DecidablePred q] (hX : X ∈ Mix v) :
    X.filter q ∈ Mix v := by
  refine ⟨?_, ?_⟩
  · rw [evenPart_filter]; exact h1 hX.1
  · rw [oddPart_filter]; exact h2 hX.2

/-! ### Membership of `Mix (Lambda, Pi)` and `Mix (Pi, Lambda)` -/

private lemma filter_mem_Lambda {Y : Chromosome} {q : Gene → Prop} [DecidablePred q]
    (hY : Y ∈ Lambda) : Y.filter q ∈ Lambda :=
  mem_Lambda_iff.mpr (Chromosome.IsNonPolarized_filter (mem_Lambda_iff.mp hY))

private lemma filter_mem_Pi {Y : Chromosome} {q : Gene → Prop} [DecidablePred q]
    (hY : Y ∈ Pi) : Y.filter q ∈ Pi :=
  mem_Pi_iff.mpr (Chromosome.IsPolarized_filter (mem_Pi_iff.mp hY))

/-- `Mix (Lambda, Pi)` is closed under filtering. -/
lemma filter_mem_Mix_Lambda_Pi {q : Gene → Prop} [DecidablePred q]
    (hX : X ∈ Mix (Lambda, Pi)) : X.filter q ∈ Mix (Lambda, Pi) :=
  filter_mem_Mix (fun h ↦ filter_mem_Lambda h)
    (fun h ↦ filter_mem_Pi h) q hX

/-- `Mix (Pi, Lambda)` is closed under filtering. -/
lemma filter_mem_Mix_Pi_Lambda {q : Gene → Prop} [DecidablePred q]
    (hX : X ∈ Mix (Pi, Lambda)) : X.filter q ∈ Mix (Pi, Lambda) :=
  filter_mem_Mix (fun h ↦ filter_mem_Pi h)
    (fun h ↦ filter_mem_Lambda h) q hX

/-- `Mix (2 • Lambda, Pi)` is closed under filtering. -/
lemma filter_mem_Mix_2Lambda_Pi {q : Gene → Prop} [DecidablePred q]
    (hX : X ∈ Mix (2 • Lambda, Pi)) : X.filter q ∈ Mix (2 • Lambda, Pi) :=
  filter_mem_Mix (fun h ↦ Chromosome.filter_mem_smul_varietyOfFilter _ h)
    (fun h ↦ filter_mem_Pi h) q hX

/-- `Mix (Pi, 2 • Lambda)` is closed under filtering. -/
lemma filter_mem_Mix_Pi_2Lambda {q : Gene → Prop} [DecidablePred q]
    (hX : X ∈ Mix (Pi, 2 • Lambda)) : X.filter q ∈ Mix (Pi, 2 • Lambda) :=
  filter_mem_Mix (fun h ↦ filter_mem_Pi h)
    (fun h ↦ Chromosome.filter_mem_smul_varietyOfFilter _ h) q hX

/-- `X.below k` lies in `Mix (Lambda, Pi)` whenever `X` does. -/
lemma below_mem_Mix_Lambda_Pi (hX : X ∈ Mix (Lambda, Pi)) (k : ℕ) :
    X.below k ∈ Mix (Lambda, Pi) := filter_mem_Mix_Lambda_Pi hX

/-- `X.below k` lies in `Mix (Pi, Lambda)` whenever `X` does. -/
lemma below_mem_Mix_Pi_Lambda (hX : X ∈ Mix (Pi, Lambda)) (k : ℕ) :
    X.below k ∈ Mix (Pi, Lambda) := filter_mem_Mix_Pi_Lambda hX

/-- `X.below k` lies in `Mix (2 • Lambda, Pi)` whenever `X` does. -/
lemma below_mem_Mix_2Lambda_Pi (hX : X ∈ Mix (2 • Lambda, Pi)) (k : ℕ) :
    X.below k ∈ Mix (2 • Lambda, Pi) := filter_mem_Mix_2Lambda_Pi hX

/-- `X.below k` lies in `Mix (Pi, 2 • Lambda)` whenever `X` does. -/
lemma below_mem_Mix_Pi_2Lambda (hX : X ∈ Mix (Pi, 2 • Lambda)) (k : ℕ) :
    X.below k ∈ Mix (Pi, 2 • Lambda) := filter_mem_Mix_Pi_2Lambda hX

/-! ### `prime^[k]` membership of `Mix v` -/

/-- Auxiliary lemma combining `Mix (Lambda, Pi)` and `Mix (Pi, Lambda)`. After
`prime^[k]`, an element of `Mix (Lambda, Pi)` lives in `Mix (Lambda, Pi)` when
`k` is even and in `Mix (Pi, Lambda)` when `k` is odd, and vice versa. -/
lemma prime_iterate_mem_Mix_Lambda_Pi_pair (X : Chromosome) (k : ℕ) :
    (X ∈ Mix (Lambda, Pi) →
      if Even k then Chromosome.prime^[k] X ∈ Mix (Lambda, Pi)
      else Chromosome.prime^[k] X ∈ Mix (Pi, Lambda)) ∧
    (X ∈ Mix (Pi, Lambda) →
      if Even k then Chromosome.prime^[k] X ∈ Mix (Pi, Lambda)
      else Chromosome.prime^[k] X ∈ Mix (Lambda, Pi)) := by
  induction k generalizing X with
  | zero => exact ⟨fun h ↦ by simpa using h, fun h ↦ by simpa using h⟩
  | succ k ih =>
    refine ⟨fun hX ↦ ?_, fun hX ↦ ?_⟩
    · rw [Function.iterate_succ_apply]
      have hXp : X.prime ∈ Mix (Pi, Lambda) := by
        have : X.prime ∈ (Mix (Lambda, Pi)).prime := ⟨X, hX, rfl⟩
        rwa [prime_Mix_Lambda_Pi] at this
      have h2 := (ih X.prime).2 hXp
      by_cases h : Even k
      · rw [if_neg (by rw [Nat.even_add_one]; exact not_not.2 h)]
        rw [if_pos h] at h2; exact h2
      · rw [if_pos (by rw [Nat.even_add_one]; exact h)]
        rw [if_neg h] at h2; exact h2
    · rw [Function.iterate_succ_apply]
      have hXp : X.prime ∈ Mix (Lambda, Pi) := by
        have : X.prime ∈ (Mix (Pi, Lambda)).prime := ⟨X, hX, rfl⟩
        rwa [prime_Mix_Pi_Lambda] at this
      have h1 := (ih X.prime).1 hXp
      by_cases h : Even k
      · rw [if_neg (by rw [Nat.even_add_one]; exact not_not.2 h)]
        rw [if_pos h] at h1; exact h1
      · rw [if_pos (by rw [Nat.even_add_one]; exact h)]
        rw [if_neg h] at h1; exact h1

/-- `prime^[k] X ∈ Mix (Lambda, Pi)` (for even `k`) or `∈ Mix (Pi, Lambda)`
(for odd `k`) whenever `X ∈ Mix (Lambda, Pi)`. -/
lemma prime_mem_Mix_Lambda_Pi_iterate (hX : X ∈ Mix (Lambda, Pi)) (k : ℕ) :
    if Even k then Chromosome.prime^[k] X ∈ Mix (Lambda, Pi)
    else Chromosome.prime^[k] X ∈ Mix (Pi, Lambda) :=
  (prime_iterate_mem_Mix_Lambda_Pi_pair X k).1 hX

/-- `prime^[k] X ∈ Mix (Pi, Lambda)` (for even `k`) or `∈ Mix (Lambda, Pi)`
(for odd `k`) whenever `X ∈ Mix (Pi, Lambda)`. -/
lemma prime_mem_Mix_Pi_Lambda_iterate (hX : X ∈ Mix (Pi, Lambda)) (k : ℕ) :
    if Even k then Chromosome.prime^[k] X ∈ Mix (Pi, Lambda)
    else Chromosome.prime^[k] X ∈ Mix (Lambda, Pi) :=
  (prime_iterate_mem_Mix_Lambda_Pi_pair X k).2 hX

/-- Auxiliary lemma for `Mix (2 • Lambda, Pi)` / `Mix (Pi, 2 • Lambda)`. -/
lemma prime_iterate_mem_Mix_2Lambda_Pi_pair (X : Chromosome) (k : ℕ) :
    (X ∈ Mix (2 • Lambda, Pi) →
      if Even k then Chromosome.prime^[k] X ∈ Mix (2 • Lambda, Pi)
      else Chromosome.prime^[k] X ∈ Mix (Pi, 2 • Lambda)) ∧
    (X ∈ Mix (Pi, 2 • Lambda) →
      if Even k then Chromosome.prime^[k] X ∈ Mix (Pi, 2 • Lambda)
      else Chromosome.prime^[k] X ∈ Mix (2 • Lambda, Pi)) := by
  induction k generalizing X with
  | zero => exact ⟨fun h ↦ by simpa using h, fun h ↦ by simpa using h⟩
  | succ k ih =>
    refine ⟨fun hX ↦ ?_, fun hX ↦ ?_⟩
    · rw [Function.iterate_succ_apply]
      have hXp : X.prime ∈ Mix (Pi, 2 • Lambda) := by
        have : X.prime ∈ (Mix (2 • Lambda, Pi)).prime := ⟨X, hX, rfl⟩
        rwa [prime_Mix_2Lambda_Pi] at this
      have h2 := (ih X.prime).2 hXp
      by_cases h : Even k
      · rw [if_neg (by rw [Nat.even_add_one]; exact not_not.2 h)]
        rw [if_pos h] at h2; exact h2
      · rw [if_pos (by rw [Nat.even_add_one]; exact h)]
        rw [if_neg h] at h2; exact h2
    · rw [Function.iterate_succ_apply]
      have hXp : X.prime ∈ Mix (2 • Lambda, Pi) := by
        have : X.prime ∈ (Mix (Pi, 2 • Lambda)).prime := ⟨X, hX, rfl⟩
        rwa [prime_Mix_Pi_2Lambda] at this
      have h1 := (ih X.prime).1 hXp
      by_cases h : Even k
      · rw [if_neg (by rw [Nat.even_add_one]; exact not_not.2 h)]
        rw [if_pos h] at h1; exact h1
      · rw [if_pos (by rw [Nat.even_add_one]; exact h)]
        rw [if_neg h] at h1; exact h1

/-- `prime^[k] X ∈ Mix (2 • Lambda, Pi)` (for even `k`) or `∈ Mix (Pi, 2 • Lambda)`
(for odd `k`) whenever `X ∈ Mix (2 • Lambda, Pi)`. -/
lemma prime_mem_Mix_2Lambda_Pi_iterate (hX : X ∈ Mix (2 • Lambda, Pi)) (k : ℕ) :
    if Even k then Chromosome.prime^[k] X ∈ Mix (2 • Lambda, Pi)
    else Chromosome.prime^[k] X ∈ Mix (Pi, 2 • Lambda) :=
  (prime_iterate_mem_Mix_2Lambda_Pi_pair X k).1 hX

/-- `prime^[k] X ∈ Mix (Pi, 2 • Lambda)` (for even `k`) or `∈ Mix (2 • Lambda, Pi)`
(for odd `k`) whenever `X ∈ Mix (Pi, 2 • Lambda)`. -/
lemma prime_mem_Mix_Pi_2Lambda_iterate (hX : X ∈ Mix (Pi, 2 • Lambda)) (k : ℕ) :
    if Even k then Chromosome.prime^[k] X ∈ Mix (Pi, 2 • Lambda)
    else Chromosome.prime^[k] X ∈ Mix (2 • Lambda, Pi) :=
  (prime_iterate_mem_Mix_2Lambda_Pi_pair X k).2 hX

/-! ### `lift^[k]` membership of `Mix v` -/

/-- If `v.1` and `v.2` are closed under `lift`, then so is `Mix (v.1, v.2)`
when accounting for the parity swap. -/
lemma lift_iterate_mem_Mix_of_swap {v1 v2 : Variety}
    (h1_lift : ∀ {Y : Chromosome} {k : ℕ}, Y ∈ v1 → Chromosome.lift^[k] Y ∈ v1)
    (h2_lift : ∀ {Y : Chromosome} {k : ℕ}, Y ∈ v2 → Chromosome.lift^[k] Y ∈ v2)
    {γ : Chromosome} {k : ℕ}
    (hγ : if Even k then γ ∈ Mix (v1, v2) else γ ∈ Mix (v2, v1)) :
    Chromosome.lift^[k] γ ∈ Mix (v1, v2) := by
  refine ⟨?_, ?_⟩
  · rw [Chromosome.evenPart_lift_iterate]
    by_cases h : Even k
    · rw [if_pos h] at hγ ⊢
      exact h1_lift hγ.1
    · rw [if_neg h] at hγ ⊢
      exact h1_lift hγ.2
  · rw [Chromosome.oddPart_lift_iterate]
    by_cases h : Even k
    · rw [if_pos h] at hγ ⊢
      exact h2_lift hγ.2
    · rw [if_neg h] at hγ ⊢
      exact h2_lift hγ.1

private lemma lift_iterate_mem_Pi {Y : Chromosome} {k : ℕ} (hY : Y ∈ Pi) :
    Chromosome.lift^[k] Y ∈ Pi :=
  mem_Pi_iff.mpr (Chromosome.IsPolarized_iff_iterate_lift.mpr (mem_Pi_iff.mp hY))

private lemma lift_iterate_mem_Lambda {Y : Chromosome} {k : ℕ} (hY : Y ∈ Lambda) :
    Chromosome.lift^[k] Y ∈ Lambda :=
  mem_Lambda_iff.mpr (Chromosome.IsNonPolarized_iff_iterate_lift.mpr
    (mem_Lambda_iff.mp hY))

private lemma lift_iterate_mem_smul_Lambda {Y : Chromosome} {k n : ℕ}
    (hY : Y ∈ n • Lambda) : Chromosome.lift^[k] Y ∈ n • Lambda := by
  obtain ⟨Z, hZ, hZY : n • Z = Y⟩ := hY
  refine ⟨Chromosome.lift^[k] Z, lift_iterate_mem_Lambda hZ, ?_⟩
  rw [← hZY]
  change n • Chromosome.lift^[k] Z = Chromosome.lift^[k] (n • Z)
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih, map_nsmul]

/-- `lift^[k] γ ∈ Mix (Lambda, Pi)` whenever γ ∈ Mix of the `prime^[k]`-swapped
variety pair. -/
lemma lift_iterate_mem_Mix_Lambda_Pi {γ : Chromosome} {k : ℕ}
    (hγ : if Even k then γ ∈ Mix (Lambda, Pi) else γ ∈ Mix (Pi, Lambda)) :
    Chromosome.lift^[k] γ ∈ Mix (Lambda, Pi) :=
  lift_iterate_mem_Mix_of_swap (@lift_iterate_mem_Lambda) (@lift_iterate_mem_Pi) hγ

/-- `lift^[k] γ ∈ Mix (Pi, Lambda)` whenever γ ∈ Mix of the `prime^[k]`-swapped
variety pair. -/
lemma lift_iterate_mem_Mix_Pi_Lambda {γ : Chromosome} {k : ℕ}
    (hγ : if Even k then γ ∈ Mix (Pi, Lambda) else γ ∈ Mix (Lambda, Pi)) :
    Chromosome.lift^[k] γ ∈ Mix (Pi, Lambda) :=
  lift_iterate_mem_Mix_of_swap (@lift_iterate_mem_Pi) (@lift_iterate_mem_Lambda) hγ

/-- `lift^[k] γ ∈ Mix (2 • Lambda, Pi)` whenever γ ∈ Mix of the swapped pair. -/
lemma lift_iterate_mem_Mix_2Lambda_Pi {γ : Chromosome} {k : ℕ}
    (hγ : if Even k then γ ∈ Mix (2 • Lambda, Pi) else γ ∈ Mix (Pi, 2 • Lambda)) :
    Chromosome.lift^[k] γ ∈ Mix (2 • Lambda, Pi) :=
  lift_iterate_mem_Mix_of_swap
    (fun {Y k} (hY : Y ∈ 2 • Lambda) ↦ @lift_iterate_mem_smul_Lambda Y k 2 hY)
    (@lift_iterate_mem_Pi) hγ

/-- `lift^[k] γ ∈ Mix (Pi, 2 • Lambda)` whenever γ ∈ Mix of the swapped pair. -/
lemma lift_iterate_mem_Mix_Pi_2Lambda {γ : Chromosome} {k : ℕ}
    (hγ : if Even k then γ ∈ Mix (Pi, 2 • Lambda) else γ ∈ Mix (2 • Lambda, Pi)) :
    Chromosome.lift^[k] γ ∈ Mix (Pi, 2 • Lambda) :=
  lift_iterate_mem_Mix_of_swap (@lift_iterate_mem_Pi)
    (fun {Y k} (hY : Y ∈ 2 • Lambda) ↦ @lift_iterate_mem_smul_Lambda Y k 2 hY) hγ

end MixLifting

end Variety

open Variety

section order

lemma evenPart_below_one (X : Chromosome) : X.evenPart.below 1 = 0 := by
  ext g
  rw [Finsupp.zero_apply, below_def, Finsupp.filter_apply]
  split_ifs with hg
  · simp only [evenPart, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Finsupp.filter_apply]
    exact if_neg ((Nat.le_antisymm hg g.rank_pos) ▸ Nat.not_even_one)
  · rfl

lemma below_one_eq_oddPart_below_one (X : Chromosome) :
    X.below 1 = X.oddPart.below 1 := by
  nth_rw 1 [parity_decomposition X, map_add, evenPart_below_one, add_zero]

/-- The rank-1 part of `X ∈ Mix (v₁, v₂)` lives entirely in `X.oddPart ∈ v₂`,
so rank-one signature injectivity of `Mix (v₁, v₂)` follows from that of `v₂`. -/
lemma rankOneSigInj_Mix_of_snd {v₁ v₂ : Variety} (h : RankOneSigInj v₂) :
    RankOneSigInj (Mix (v₁, v₂)) := by
  intro X Y hX hY hsig
  rw [below_one_eq_oddPart_below_one X, below_one_eq_oddPart_below_one Y] at hsig ⊢
  exact h (mem_Mix_iff.1 hX).2 (mem_Mix_iff.1 hY).2 hsig

/-- The dominance order makes `Mix (Pi, Lambda)` and `Mix (Lambda, Pi)` a
sigma-pair: `prime` swaps them and each is rank-one signature injective. -/
lemma sigmaPair_Mix_Pi_Lambda :
    SigmaPair (Mix (Pi, Lambda)) (Mix (Lambda, Pi)) where
  prime_left := prime_Mix_Pi_Lambda.le
  prime_right := prime_Mix_Lambda_Pi.le
  rankOne_left := rankOneSigInj_Mix_of_snd rankOneSigInj_Lambda
  rankOne_right := rankOneSigInj_Mix_of_snd rankOneSigInj_Pi

/-- The dominance order makes `Mix (2 • Lambda, Pi)` and `Mix (Pi, 2 • Lambda)`
a sigma-pair. -/
lemma sigmaPair_Mix_2Lambda_Pi :
    SigmaPair (Mix (2 • Lambda, Pi)) (Mix (Pi, 2 • Lambda)) where
  prime_left := prime_Mix_2Lambda_Pi.le
  prime_right := prime_Mix_Pi_2Lambda.le
  rankOne_left := rankOneSigInj_Mix_of_snd rankOneSigInj_Pi
  rankOne_right := rankOneSigInj_Mix_of_snd
    (RankOneSigInj.mono smul_Lambda_le_Lambda rankOneSigInj_Lambda)

instance : PartialOrder (Variety.Mix (.Pi, .Lambda)) :=
  Variety.SigmaUnique.partialOrder sigmaPair_Mix_Pi_Lambda.sigmaUnique_left

instance : PartialOrder (Variety.Mix (.Lambda, .Pi)) :=
  Variety.SigmaUnique.partialOrder sigmaPair_Mix_Pi_Lambda.sigmaUnique_right

noncomputable instance : PartialOrder (Variety.Mix (2 • .Lambda, .Pi)) :=
  Variety.SigmaUnique.partialOrder sigmaPair_Mix_2Lambda_Pi.sigmaUnique_left

noncomputable instance : PartialOrder (Variety.Mix (.Pi, 2 • .Lambda)) :=
  Variety.SigmaUnique.partialOrder sigmaPair_Mix_2Lambda_Pi.sigmaUnique_right

end order

noncomputable section neg

namespace Mix

lemma Pi_Lambda_neg_mem_iff {X : Chromosome} :
    X ∈ (Mix (.Pi, .Lambda)) ↔ - X ∈ (Mix (.Pi, .Lambda)) :=
  (neg_mem_Mix_iff Pi.neg_mem_iff Lambda.neg_mem_iff).symm

instance : InvolutiveNeg (Mix (.Pi, .Lambda)) where
  neg X := ⟨- X, Pi_Lambda_neg_mem_iff.1 X.2⟩
  neg_neg X := Subtype.val_injective (neg_neg X.1)

lemma Pi_Lambda_neg_val {X : Mix (.Pi, .Lambda)} : (- X).1 = - X.1 := rfl

@[simp] lemma Pi_Lambda_neg_add {X Y : Mix (.Pi, .Lambda)} :
    - (X + Y) = - X + - Y :=
  Subtype.val_injective Chromosome.neg_add

lemma Lambda_Pi_neg_mem_iff {X : Chromosome} :
    X ∈ (Mix (.Lambda, .Pi)) ↔ - X ∈ (Mix (.Lambda, .Pi)) :=
  (neg_mem_Mix_iff Lambda.neg_mem_iff Pi.neg_mem_iff).symm

instance : InvolutiveNeg (Mix (.Lambda, .Pi)) where
  neg X := ⟨-X, Lambda_Pi_neg_mem_iff.1 X.2⟩
  neg_neg X := Subtype.val_injective (neg_neg X.1)

lemma Lambda_Pi_neg_val {X : Mix (.Lambda, .Pi)} : (- X).1 = - X.1 := rfl

@[simp] lemma Lambda_Pi_neg_add {X Y : Mix (.Lambda, .Pi)} :
    - (X + Y) = - X + - Y :=
  Subtype.val_injective Chromosome.neg_add

lemma tLambda_Pi_neg_mem_iff {X : Chromosome} :
    X ∈ (Mix (2 • Lambda, Pi)) ↔ - X ∈ (Mix (2 • Lambda, Pi)) :=
  (neg_mem_Mix_iff (Variety.neg_mem_smul_iff
    Lambda.neg_mem_iff) Pi.neg_mem_iff).symm

instance : InvolutiveNeg (Mix (2 • Lambda, Pi)) where
  neg X := ⟨-X, tLambda_Pi_neg_mem_iff.1 X.2⟩
  neg_neg X := Subtype.val_injective (neg_neg X.1)

lemma tLambda_Pi_neg_val {X : Mix (2 • Lambda, Pi)} : (- X).1 = - X.1 := rfl

@[simp] lemma tLambda_Pi_neg_add {X Y : Mix (2 • Lambda, Pi)} :
    - (X + Y) = - X + - Y :=
  Subtype.val_injective Chromosome.neg_add

lemma Pi_2Lambda_neg_mem_iff {X : Chromosome} :
    X ∈ (Mix (Pi, 2 • Lambda)) ↔ - X ∈ (Mix (Pi, 2 • Lambda)) :=
  (neg_mem_Mix_iff Pi.neg_mem_iff (Variety.neg_mem_smul_iff
    Lambda.neg_mem_iff)).symm

instance : InvolutiveNeg (Mix (Pi, 2 • Lambda)) where
  neg X := ⟨-X, Pi_2Lambda_neg_mem_iff.1 X.2⟩
  neg_neg X := Subtype.val_injective (neg_neg X.1)

lemma Pi_2Lambda_neg_val {X : Mix (Pi, 2 • Lambda)} : (- X).1 = - X.1 := rfl

@[simp] lemma Pi_2Lambda_neg_add {X Y : Mix (Pi, 2 • Lambda)} :
    - (X + Y) = - X + - Y :=
  Subtype.val_injective Chromosome.neg_add

end Mix

end neg
