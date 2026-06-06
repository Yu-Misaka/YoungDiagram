import YoungDiagram.Variety.Pi
import YoungDiagram.Variety.Lambda

open Chromosome

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

end Mix

end Variety
