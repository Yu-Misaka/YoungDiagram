import YoungDiagram.Variety.Mix

open Pointwise

namespace Variety

noncomputable def Label : Fin 5 → Variety
  | 0 => Pi
  | 1 => Mix (Lambda, Pi)
  | 2 => Mix (Pi, Lambda)
  | 3 => Mix (2 • Lambda, Pi)
  | 4 => Mix (Pi, 2 • Lambda)

def Label.prime : Fin 5 → Fin 5
  | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3

lemma Label.prime_eq {i : Fin 5} :
    Variety.prime (Label i) = Label (Label.prime i) :=
  match i with
  | 0 => prime_Pi
  | 1 => prime_Mix_Lambda_Pi
  | 2 => prime_Mix_Pi_Lambda
  | 3 => prime_Mix_2Lambda_Pi
  | 4 => prime_Mix_Pi_2Lambda

lemma Label.prime_eq_iterate {i : Fin 5} {k : ℕ} :
    Label (prime^[k] i) = Variety.prime^[k] (Label i) := by
  induction k
  · rw [Function.iterate_zero, Function.iterate_zero]; rfl
  · expose_names
    nth_rw 1 [add_comm, Function.iterate_add_apply, Function.iterate_one,
      ← Label.prime_eq, h, Function.iterate_add_apply, Function.iterate_one]
    exact (Function.iterate_succ_apply' ..).symm

lemma prime_iterate_mem {k : ℕ} {X : Chromosome} {V : Variety} (hX : X ∈ V) :
    Chromosome.prime^[k] X ∈ Variety.prime^[k] V := by
  induction k generalizing V X
  · rwa [Function.iterate_zero, Function.iterate_zero]
  · expose_names
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
    exact @h X.prime V.prime ⟨X, hX, rfl⟩

noncomputable def Label.of_mem_prime_iterate {i : Fin 5} {k : ℕ} {X : Chromosome}
    (hX : X ∈ Label i) : Label (Label.prime^[k] i) := by
  use Chromosome.prime^[k] X
  rw [Label.prime_eq_iterate]
  exact prime_iterate_mem hX

lemma Label.prime_iterate_zero {k : ℕ} : Label.prime^[k] 0 = 0 :=
  Function.iterate_fixed rfl k

end Variety
