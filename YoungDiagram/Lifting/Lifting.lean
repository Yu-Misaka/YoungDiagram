import YoungDiagram.Mutations
import YoungDiagram.Lifting.Pi
import YoungDiagram.Lifting.MixLambdaPi
import YoungDiagram.Lifting.MixPiLambda
import YoungDiagram.Lifting.Mix2LambdaPi
import YoungDiagram.Lifting.MixPi2Lambda

open Variety hiding prime
open Chromosome Mutation Pointwise

namespace Variety

/-- `Label.prime` is an involution on `Fin 5`. -/
private lemma Label.prime_prime (i : Fin 5) :
    Label.prime (Label.prime i) = i := by
  fin_cases i <;> rfl

private lemma Label.prime_iterate_two (i : Fin 5) :
    Label.prime^[2] i = i := Label.prime_prime i

/-- For even `k`, `Label.prime^[k]` is the identity on `Fin 5`. -/
private lemma Label.prime_iterate_even {k : ℕ} (hk : Even k) (i : Fin 5) :
    Label.prime^[k] i = i := by
  obtain ⟨j, hj⟩ : ∃ j, k = 2 * j := ⟨k / 2, by have := Nat.even_iff.mp hk; omega⟩
  subst hj
  clear hk
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [show 2 * (j + 1) = 2 * j + 2 from by ring, Function.iterate_add_apply,
      Label.prime_iterate_two, ih]

/-- For odd `k`, `Label.prime^[k]` equals one application of `Label.prime`. -/
private lemma Label.prime_iterate_odd {k : ℕ} (hk : ¬ Even k) (i : Fin 5) :
    Label.prime^[k] i = Label.prime i := by
  obtain ⟨j, hj⟩ : ∃ j, k = 2 * j + 1 :=
    ⟨k / 2, by have := Nat.odd_iff.mp (Nat.not_even_iff_odd.mp hk); omega⟩
  subst hj
  rw [Function.iterate_add_apply, Function.iterate_one,
    Label.prime_iterate_even ⟨j, by ring⟩ (Label.prime i)]

end Variety

namespace Mutation

/-- Transport a `Step` across an equality of variety indices. -/
private lemma Step.cast_idx {i j : Fin 5} (h : i = j) {X U : Chromosome}
    (hX_i : X ∈ Label i) (hU_i : U ∈ Label i)
    (hStep : Step i ⟨X, hX_i⟩ ⟨U, hU_i⟩) :
    ∃ (hX_j : X ∈ Label j) (hU_j : U ∈ Label j),
      Step j ⟨X, hX_j⟩ ⟨U, hU_j⟩ := by
  subst h
  exact ⟨hX_i, hU_i, hStep⟩

end Mutation

noncomputable section

variable (idx : Fin 5) (k : ℕ)

private abbrev φ := Label idx
private abbrev ψ := Label (Label.prime^[k] idx)

variable {X U : Chromosome} (hX : X ∈ φ idx) (hU : U ∈ ψ idx k)

variable (hMu : Step (Label.prime^[k] idx) (Label.of_mem_prime_iterate hX) ⟨U, hU⟩)

include hU hMu in
lemma mutation_lifting : ∃ (Z : Chromosome) (hZ : Z ∈ φ idx),
    Step idx ⟨X, hX⟩ ⟨Z, hZ⟩ ∧
    prime^[k] Z = U ∧
    ∀ i ≤ k, signature (prime^[i] X) = signature (prime^[i] Z) := by
  match idx with
  | 0 =>
    refine Pi.mutation_lifting hX ?_ ?_
    · exact congrArg (U ∈ ·)
        (congrArg Label Label.prime_iterate_zero).symm |>.mpr hU
    · change Step 0 ⟨prime^[k] X, prime_mem_Pi_iterate hX⟩ ⟨U, _⟩
      convert hMu
      · exact Label.prime_iterate_zero.symm
      · rfl
  | 1 =>
    by_cases hk : Even k
    · -- Even: `Label.prime^[k] 1 = 1`, hMu is a `MixLambdaPi.Step`.
      have hidx : Label.prime^[k] (1 : Fin 5) = 1 := Label.prime_iterate_even hk 1
      obtain ⟨hpX, hU', hMu'⟩ := Mutation.Step.cast_idx hidx _ hU hMu
      exact MixLambdaPi.mutation_lifting_even hX hU' hk hMu'
    · -- Odd: `Label.prime^[k] 1 = 2`, hMu is a `MixPiLambda.Step`.
      have hidx : Label.prime^[k] (1 : Fin 5) = 2 := Label.prime_iterate_odd hk 1
      obtain ⟨hpX, hU', hMu'⟩ := Mutation.Step.cast_idx hidx _ hU hMu
      exact MixLambdaPi.mutation_lifting_odd hX hU' hk hMu'
  | 2 =>
    by_cases hk : Even k
    · have hidx : Label.prime^[k] (2 : Fin 5) = 2 := Label.prime_iterate_even hk 2
      obtain ⟨hpX, hU', hMu'⟩ := Mutation.Step.cast_idx hidx _ hU hMu
      exact MixPiLambda.mutation_lifting_even hX hU' hk hMu'
    · have hidx : Label.prime^[k] (2 : Fin 5) = 1 := Label.prime_iterate_odd hk 2
      obtain ⟨hpX, hU', hMu'⟩ := Mutation.Step.cast_idx hidx _ hU hMu
      exact MixPiLambda.mutation_lifting_odd hX hU' hk hMu'
  | 3 =>
    by_cases hk : Even k
    · have hidx : Label.prime^[k] (3 : Fin 5) = 3 := Label.prime_iterate_even hk 3
      obtain ⟨hpX, hU', hMu'⟩ := Mutation.Step.cast_idx hidx _ hU hMu
      exact Mix2LambdaPi.mutation_lifting_even hX hU' hk hMu'
    · have hidx : Label.prime^[k] (3 : Fin 5) = 4 := Label.prime_iterate_odd hk 3
      obtain ⟨hpX, hU', hMu'⟩ := Mutation.Step.cast_idx hidx _ hU hMu
      exact Mix2LambdaPi.mutation_lifting_odd hX hU' hk hMu'
  | 4 =>
    by_cases hk : Even k
    · have hidx : Label.prime^[k] (4 : Fin 5) = 4 := Label.prime_iterate_even hk 4
      obtain ⟨hpX, hU', hMu'⟩ := Mutation.Step.cast_idx hidx _ hU hMu
      exact MixPi2Lambda.mutation_lifting_even hX hU' hk hMu'
    · have hidx : Label.prime^[k] (4 : Fin 5) = 3 := Label.prime_iterate_odd hk 4
      obtain ⟨hpX, hU', hMu'⟩ := Mutation.Step.cast_idx hidx _ hU hMu
      exact MixPi2Lambda.mutation_lifting_odd hX hU' hk hMu'

end
