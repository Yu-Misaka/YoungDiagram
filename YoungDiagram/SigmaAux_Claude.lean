import YoungDiagram.Chromosome
import YoungDiagram.Variety
import YoungDiagram.Mutations
import Mathlib.Algebra.GroupWithZero.Submonoid.Pointwise

open Chromosome
open Variety

open Finsupp Pointwise

lemma prime_mem_pi (X : Pi) : prime X ∈ Pi := by
  have := Variety.prime_Pi
  simp [Variety.prime] at this
  have h : prime ↑X ∈ AddSubmonoid.map Chromosome.prime Variety.Pi :=
  ⟨↑X, X.property, rfl⟩
  simpa [this] using h

lemma prime_k_mem_pi (X : Pi) (k : ℕ) : Chromosome.prime^[k] X ∈ Pi := by
  induction k with
  | zero => simp
  | succ n ih =>
    have h : prime ((Chromosome.prime^[n]) ↑X) ∈ Pi :=
      prime_mem_pi ⟨(Chromosome.prime^[n]) ↑X, ih⟩
    rw [Function.iterate_succ']
    exact h

noncomputable def Pi_prime (X : Pi) : Pi := ⟨prime X, prime_mem_pi X⟩

lemma Pi_prime_a_b : (X : Pi) → (a b : ℕ) →
  Pi_prime^[a] (Pi_prime^[b] X) = Pi_prime^[a + b] X := by
  intro X a b
  simp [Function.iterate_add]


lemma Pi_prime_prime : (X : Pi) → (k : ℕ) →
  Pi_prime^[k + 1] X = Pi_prime^[k] (Pi_prime X) := by
  intro X k
  induction k with
  | zero => rfl
  | succ n ih => simp

lemma Pi_prime_prime_other : (k : ℕ) → (X : Pi) →
  Pi_prime^[k + 1] X = Pi_prime (Pi_prime^[k] X) := by
  intro k
  induction k with
  | zero =>
    intro X
    rfl
  | succ n ih =>
    intro X
    simp only [Function.iterate_succ, Function.comp_apply]
    rw [← ih (Pi_prime X)]
    simp

lemma prime_a_b : (X : Pi) → (a b : ℕ) →
  Chromosome.prime^[a] (Chromosome.prime^[b] X) = Chromosome.prime^[a + b] X := by
  intro X a b
  simp [Function.iterate_add]


lemma prime_prime : (X : Pi) → (k : ℕ) →
  Chromosome.prime^[k + 1] X = Chromosome.prime^[k] (Chromosome.prime X) := by
  intro X k
  induction k with
  | zero => rfl
  | succ n ih => simp

lemma prime_prime_other : (k : ℕ) → (X : Pi) →
  Chromosome.prime^[k + 1] X = Chromosome.prime (Chromosome.prime^[k] X) := by
  intro k
  induction k with
  | zero =>
    intro X
    rfl
  | succ n ih =>
    intro X
    simp only [Function.iterate_succ, Function.comp_apply]
    rw [← ih ⟨(Chromosome.prime X), prime_mem_pi X⟩]
    simp

-- The first component of a chromosome's signature equals the Finsupp.sum of
-- the first components of each gene's signature, weighted by multiplicity.
-- Proof: .1 is an AddMonoidHom (AddMonoidHom.fst), so it commutes with Finset.sum.
lemma signature_fst (X : Variety.Pi) :
    (Chromosome.signature X).1 = X.val.sum (fun g n ↦ (n : ℚ) • g.signature.1) := by
  simp only [Chromosome.signature, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Finsupp.sum]
  -- (AddMonoidHom.fst ℚ ℚ) p = p.1 definitionally, and (c • p).1 = c • p.1 definitionally,
  -- so the goal is definitionally equal to what map_sum gives.
  exact map_sum (AddMonoidHom.fst ℚ ℚ) _ _

-- The first component of signature(prime X) equals the Finsupp.sum of
-- the first components of each primeGene's signature, weighted by multiplicity.
-- Proof: push signature through the sum (map_finsupp_sum + map_nsmul),
-- convert ℕ-smul to ℚ-smul (Nat.cast_smul_eq_nsmul), then extract .1 via map_sum of fst.
lemma signature_prime_fst (X : Chromosome) :
    (signature (Chromosome.prime X)).1 =
    X.sum (fun g m ↦ (m : ℚ) • (primeGene g).signature.1) := by
  -- Step 1: For each gene g, signature(X g • primeGene g) = (X g : ℚ) • (primeGene g).signature.
  rw [Chromosome.prime]
  simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, smul_eq_mul]
  have hg : ∀ g : Gene, signature (X g • primeGene g) = (X g : ℚ) • (primeGene g).signature := by
    intro g
    rw [map_nsmul]
    exact (Nat.cast_smul_eq_nsmul (R := ℚ) (X g) _).symm
  -- Step 2: Unfold Finsupp.sum, push signature through Finset.sum, apply hg, then extract .1.
  simp only [Finsupp.sum]
  rw [map_sum signature]
  simp_rw [hg]
  exact map_sum (AddMonoidHom.fst ℚ ℚ) _ _

-- Key lemma: the first component of the signature can only decrease under prime.
lemma sig_prime_le_fst (Y : Variety.Pi) : (signature (prime Y)).1 ≤ (signature Y).1 := by
  -- Step 1: Gene-level auxiliary.
  -- For a polarized gene g (type ≠ NonPolarized), lowering the rank by 1 does not
  -- increase the first component of the signature.
  -- Proved by splitting on g.type (Positive / Negative) and parity of g.rank,
  -- using Gene.signature_of_positive and Gene.signature_of_negative.
  have aux : ∀ g : Gene, g.type ≠ .NonPolarized →
      (primeGene g).signature.1 ≤ g.signature.1 := by
    intro g hg
    match hg' : g.type with
    | .NonPolarized => exact absurd hg' hg
    | .Positive =>
      -- primeGene g = Gene.ofRank (g.rank - 1) .Positive
      -- If g.rank even:   g.sig.1 = g.rank/2  and  (primeGene g).sig.1 = g.rank/2   (equal)
      -- If g.rank odd:    g.sig.1 = (g.rank+1)/2  and  (primeGene g).sig.1 = (g.rank-1)/2 ≤ it
      by_cases heven : Even g.rank
      · -- g.rank is even, so g.rank - 1 is odd
        -- g.sig.1 = ↑g.rank/2,  (primeGene g).sig.1 = (↑(g.rank-1)+1)/2 = ↑g.rank/2  (equal)
        have hne : g.rank - 1 ≠ 0 := by
          obtain ⟨k, hk⟩ := heven; have := g.rank_pos; omega
        have hodd : ¬ Even (g.rank - 1) := (Nat.even_sub_one g.rank_pos).mp heven
        simp only [primeGene, hg', Chromosome.signature_ofRank, hne, ↓reduceDIte]
        rw [Gene.signature_of_positive rfl, if_neg hodd,
            Gene.signature_of_positive hg', if_pos heven]
        simp only [Nat.cast_pred g.rank_pos]
        linarith
      · -- g.rank is odd, so g.rank - 1 is even
        -- g.sig.1 = (↑g.rank+1)/2, (primeGene g).sig.1 = ↑(g.rank-1)/2 ≤ (↑g.rank+1)/2
        have heven' : Even (g.rank - 1) := by
          by_contra h
          exact heven ((Nat.even_sub_one g.rank_pos).mpr h)
        by_cases hne : g.rank - 1 = 0
        · -- g.rank = 1, primeGene g = 0, so (primeGene g).signature.1 = 0 ≤ g.signature.1
          simp only [primeGene, hne, Gene.ofRank_zero, map_zero]
          exact (Gene.signature_pos g).le.1
        · -- g.rank ≥ 3: (primeGene g).sig.1 = (↑g.rank-1)/2 ≤ (↑g.rank+1)/2
          simp only [primeGene, hg', Chromosome.signature_ofRank, hne, ↓reduceDIte]
          rw [Gene.signature_of_positive rfl, if_pos heven',
              Gene.signature_of_positive hg', if_neg heven]
          simp only [Nat.cast_pred g.rank_pos]
          linarith
    | .Negative =>
      -- primeGene g = Gene.ofRank (g.rank - 1) .Negative
      -- If g.rank even:   g.sig.1 = ↑g.rank/2  and  (primeGene g).sig.1 = (↑g.rank-2)/2 ≤ it
      -- If g.rank odd:    g.sig.1 = (↑g.rank-1)/2  and  (primeGene g).sig.1 = (↑g.rank-1)/2 (equal)
      by_cases heven : Even g.rank
      · -- g.rank is even, so g.rank - 1 is odd
        -- g.sig.1 = ↑g.rank/2, (primeGene g).sig.1 = (↑(g.rank-1)-1)/2 = (↑g.rank-2)/2 ≤ it
        have hne : g.rank - 1 ≠ 0 := by
          obtain ⟨k, hk⟩ := heven; have := g.rank_pos; omega
        have hodd : ¬ Even (g.rank - 1) := (Nat.even_sub_one g.rank_pos).mp heven
        simp only [primeGene, hg', Chromosome.signature_ofRank, hne, ↓reduceDIte]
        rw [Gene.signature_of_negative rfl, if_neg hodd,
            Gene.signature_of_negative hg', if_pos heven]
        simp only [Nat.cast_pred g.rank_pos]
        linarith
      · -- g.rank is odd, so g.rank - 1 is even
        -- g.sig.1 = (↑g.rank-1)/2, (primeGene g).sig.1 = ↑(g.rank-1)/2 = (↑g.rank-1)/2 (equal)
        have heven' : Even (g.rank - 1) := by
          by_contra h
          exact heven ((Nat.even_sub_one g.rank_pos).mpr h)
        by_cases hne : g.rank - 1 = 0
        · -- g.rank = 1, primeGene g = 0, so (primeGene g).signature.1 = 0 ≤ g.signature.1
          simp only [primeGene, hne, Gene.ofRank_zero, map_zero]
          exact (Gene.signature_pos g).le.1
        · -- g.rank ≥ 3: (primeGene g).sig.1 = (↑g.rank-1)/2 = g.sig.1
          simp only [primeGene, hg', Chromosome.signature_ofRank, hne, ↓reduceDIte]
          rw [Gene.signature_of_negative rfl, if_pos heven',
              Gene.signature_of_negative hg', if_neg heven]
          simp only [Nat.cast_pred g.rank_pos]
          linarith
  -- Step 2: All genes in Y's support are polarized (since Y ∈ Pi).
  have hpol : ∀ g ∈ (↑Y : Chromosome).support, g.type ≠ .NonPolarized :=
    IsPolarized_def'.mp (Variety.mem_Pi_iff.mp Y.property)
  simp only [signature_fst]
  simp only [signature_prime_fst]
  -- Step 3: Pointwise comparison: each gene's contribution to prime is ≤ the original,
  -- since aux gives (primeGene g).signature.1 ≤ g.signature.1 for polarized g,
  -- and the scalar (Y.val g : ℚ) is non-negative.
  apply Finsupp.sum_le_sum
  intro g hg
  have : ∀ g ∈ Y.val.support, (0 : ℚ) ≤ (Y.val g) := by
    intro g _
    exact Nat.cast_nonneg _
  apply mul_le_mul_of_nonneg_left (aux g (hpol g hg)) (this g hg)

-- same as signature_fst
lemma signature_snd (X : Variety.Pi) :
    (Chromosome.signature X).2 = X.val.sum (fun g n ↦ (n : ℚ) • g.signature.2) := by
  simp only [Chromosome.signature, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Finsupp.sum]
  exact map_sum (AddMonoidHom.snd ℚ ℚ) _ _

-- same as signature_prime_fst
lemma signature_prime_snd (X : Chromosome) :
    (signature (Chromosome.prime X)).2 =
    X.sum (fun g m ↦ (m : ℚ) • (primeGene g).signature.2) := by
  rw [Chromosome.prime]
  simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, smul_eq_mul]
  have hg : ∀ g : Gene, signature (X g • primeGene g) = (X g : ℚ) • (primeGene g).signature := by
    intro g
    rw [map_nsmul]
    exact (Nat.cast_smul_eq_nsmul (R := ℚ) (X g) _).symm
  simp only [Finsupp.sum]
  rw [map_sum signature]
  simp_rw [hg]
  exact map_sum (AddMonoidHom.snd ℚ ℚ) _ _

-- same as sig_prime_le_fst
lemma sig_prime_le_snd (Y : Variety.Pi) : (signature (prime Y)).2 ≤ (signature Y).2 := by
  have aux : ∀ g : Gene, g.type ≠ .NonPolarized →
      (primeGene g).signature.2 ≤ g.signature.2 := by
    intro g hg
    match hg' : g.type with
    | .NonPolarized => exact absurd hg' hg
    | .Positive =>
      by_cases heven : Even g.rank
      · have hne : g.rank - 1 ≠ 0 := by
          obtain ⟨k, hk⟩ := heven; have := g.rank_pos; omega
        have hodd : ¬ Even (g.rank - 1) := (Nat.even_sub_one g.rank_pos).mp heven
        simp only [primeGene, hg', Chromosome.signature_ofRank, hne, ↓reduceDIte]
        rw [Gene.signature_of_positive rfl, if_neg hodd,
            Gene.signature_of_positive hg', if_pos heven]
        simp only [Nat.cast_pred g.rank_pos]
        linarith
      · have heven' : Even (g.rank - 1) := by
          by_contra h
          exact heven ((Nat.even_sub_one g.rank_pos).mpr h)
        by_cases hne : g.rank - 1 = 0
        · simp only [primeGene, hne, Gene.ofRank_zero, map_zero]
          exact (Gene.signature_pos g).le.2
        · simp only [primeGene, hg', Chromosome.signature_ofRank, hne, ↓reduceDIte]
          rw [Gene.signature_of_positive rfl, if_pos heven',
              Gene.signature_of_positive hg', if_neg heven]
          simp only [Nat.cast_pred g.rank_pos]
          linarith
    | .Negative =>
      by_cases heven : Even g.rank
      · have hne : g.rank - 1 ≠ 0 := by
          obtain ⟨k, hk⟩ := heven; have := g.rank_pos; omega
        have hodd : ¬ Even (g.rank - 1) := (Nat.even_sub_one g.rank_pos).mp heven
        simp only [primeGene, hg', Chromosome.signature_ofRank, hne, ↓reduceDIte]
        rw [Gene.signature_of_negative rfl, if_neg hodd,
            Gene.signature_of_negative hg', if_pos heven]
        simp only [Nat.cast_pred g.rank_pos]
        linarith
      · have heven' : Even (g.rank - 1) := by
          by_contra h
          exact heven ((Nat.even_sub_one g.rank_pos).mpr h)
        by_cases hne : g.rank - 1 = 0
        · simp only [primeGene, hne, Gene.ofRank_zero, map_zero]
          exact (Gene.signature_pos g).le.2
        · simp only [primeGene, hg', Chromosome.signature_ofRank, hne, ↓reduceDIte]
          rw [Gene.signature_of_negative rfl, if_pos heven',
              Gene.signature_of_negative hg', if_neg heven]
          simp only [Nat.cast_pred g.rank_pos]
          linarith
  have hpol : ∀ g ∈ (↑Y : Chromosome).support, g.type ≠ .NonPolarized :=
    IsPolarized_def'.mp (Variety.mem_Pi_iff.mp Y.property)
  simp only [signature_snd]
  simp only [signature_prime_snd]
  apply Finsupp.sum_le_sum
  intro g hg
  have : ∀ g ∈ Y.val.support, (0 : ℚ) ≤ (Y.val g) := by
    intro g _
    exact Nat.cast_nonneg _
  apply mul_le_mul_of_nonneg_left (aux g (hpol g hg)) (this g hg)
