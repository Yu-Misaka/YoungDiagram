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

-- Key lemma: the first component of the signature can only decrease under prime.
lemma sig_prime_le_fst (Y : Variety.Pi) : (signature (prime Y)).1 ≤ (signature Y).1 := by
  simp [signature, Chromosome.prime]
  sorry
