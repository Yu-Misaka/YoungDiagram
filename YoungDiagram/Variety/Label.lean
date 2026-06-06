import YoungDiagram.Variety.Mix

open Pointwise

namespace Variety

lemma variety_prime_smul {v : Variety} {n : ℕ} :
    (n • v).prime = n • v.prime := by
  ext x; constructor <;> intro hx
  · obtain ⟨y, ⟨⟨z, ⟨hz, hyz : n • z = y⟩⟩, heq⟩⟩ := hx
    refine ⟨z.prime, ⟨?_, (?_ : n • z.prime = x)⟩⟩
    · use z
    · rw [← map_nsmul, hyz, heq]
  · obtain ⟨y, ⟨⟨z, ⟨hz, hyz⟩⟩, heq : n • y = x⟩⟩ := hx
    refine ⟨n • z, ⟨?_, ?_⟩⟩
    · use z, hz; rfl
    · rw [map_nsmul, hyz, heq]

noncomputable def Label : Fin 5 → Variety
  | 0 => Pi
  | 1 => Mix (Lambda, Pi)
  | 2 => Mix (Pi, Lambda)
  | 3 => Mix (2 • Lambda, Pi)
  | 4 => Mix (Pi, 2 • Lambda)

def Label.prime : Fin 5 → Fin 5
  | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3

lemma Label.prime_eq {i : Fin 5} :
    Variety.prime (Label i) = Label (Label.prime i) := by
  match i with
  | 0 => exact prime_Pi
  | 1 =>
    change (Mix (Lambda, Pi)).prime = Mix (Pi, Lambda)
    rw [prime_Mix_eq parityDecomp_mem_Lambda
      parityDecomp_mem_Pi, prime_Pi, prime_Lambda]
  | 2 =>
    change (Mix (Pi, Lambda)).prime = Mix (Lambda, Pi)
    rw [prime_Mix_eq parityDecomp_mem_Pi
      parityDecomp_mem_Lambda, prime_Pi, prime_Lambda]
  | 3 =>
    change (Mix (2 • Lambda, Pi)).prime = Mix (Pi, 2 • Lambda)
    rw [prime_Mix_eq parityDecomp_mem_smul_Lambda
      parityDecomp_mem_Pi, prime_Pi, variety_prime_smul, prime_Lambda]
  | 4 =>
    change (Mix (Pi, 2 • Lambda)).prime = Mix (2 • Lambda, Pi)
    rw [prime_Mix_eq parityDecomp_mem_Pi
      parityDecomp_mem_smul_Lambda, prime_Pi, variety_prime_smul, prime_Lambda]

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

section MixOrder

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

end MixOrder

end Variety

instance : PartialOrder (Variety.Mix (Variety.Pi, Variety.Lambda)) :=
  Variety.SigmaUnique.partialOrder Variety.sigmaPair_Mix_Pi_Lambda.sigmaUnique_left

instance : PartialOrder (Variety.Mix (Variety.Lambda, Variety.Pi)) :=
  Variety.SigmaUnique.partialOrder Variety.sigmaPair_Mix_Pi_Lambda.sigmaUnique_right

noncomputable instance : PartialOrder (Variety.Mix (2 • Variety.Lambda, Variety.Pi)) :=
  Variety.SigmaUnique.partialOrder Variety.sigmaPair_Mix_2Lambda_Pi.sigmaUnique_left

noncomputable instance : PartialOrder (Variety.Mix (Variety.Pi, 2 • Variety.Lambda)) :=
  Variety.SigmaUnique.partialOrder Variety.sigmaPair_Mix_2Lambda_Pi.sigmaUnique_right
