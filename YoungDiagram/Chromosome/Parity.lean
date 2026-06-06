import YoungDiagram.Chromosome.Prime

open Finsupp

namespace Chromosome

lemma neg_filtered {X : Chromosome} {P : ℕ → Prop} [DecidablePred P] :
    (- X).filter (P ·.rank) = - (X.filter (P ·.rank)) := by
  ext g
  rw [filter_apply, neg_apply, neg_apply, filter_apply, Gene.neg_rank]

section parity

def oddPart : Chromosome →+ Chromosome where
  toFun c := c.filter (Odd ·.rank)
  map_zero' := filter_zero _
  map_add' _ _ := filter_add

def evenPart : Chromosome →+ Chromosome where
  toFun c := c.filter (Even ·.rank)
  map_zero' := filter_zero _
  map_add' _ _ := filter_add

lemma oddPart_eq {X : Chromosome} : X.oddPart = X.filter (Odd ·.rank) := rfl

lemma evenPart_eq {X : Chromosome} : X.evenPart = X.filter (Even ·.rank) := rfl

lemma evenPart_idempotent {X : Chromosome} : evenPart (evenPart X) = evenPart X := by
  refine (filter_eq_self_iff (Even ·.rank) (filter (Even ·.rank) X)).2 ?_
  intro _ hx
  by_contra!
  exact hx (filter_apply_neg _ X this)

lemma oddPart_idempotent {X : Chromosome} : oddPart (oddPart X) = oddPart X := by
  refine (filter_eq_self_iff (Odd ·.rank) (filter (Odd ·.rank) X)).2 ?_
  intro _ hx
  by_contra!
  exact hx (filter_apply_neg _ X this)

lemma parity_decomposition (X : Chromosome) : X = X.oddPart + X.evenPart := by
  simp only [oddPart, AddMonoidHom.coe_mk, ZeroHom.coe_mk, evenPart]
  conv =>
    enter [2, 2, 1, a]
    rw [← Nat.not_odd_iff_even]
  rw [filter_add_filter_not]

lemma evenPart_single {g : Gene} : evenPart (single g 1) =
    if Even g.rank then single g 1 else 0 := by
  split_ifs with h
  · exact filter_single_of_pos _ h
  · exact filter_single_of_neg _ h

lemma oddPart_single {g : Gene} : oddPart (single g 1) =
    if Even g.rank then 0 else single g 1 := by
  split_ifs with h
  · exact filter_single_of_neg _ <| Nat.not_odd_iff_even.2 h
  · exact filter_single_of_pos _ <| Nat.not_even_iff_odd.1 h

lemma evenPart_prime {X : Chromosome} : X.prime.evenPart = X.oddPart.prime := by
  induction X using Finsupp.induction
  · repeat rw [map_zero]
  · expose_names
    repeat rw [map_add]
    rw [h_2, add_left_inj, ← smul_single_one, map_nsmul, map_nsmul,
      map_nsmul, map_nsmul, nsmul_right_inj h_1, oddPart_single]
    split_ifs with ha
    · simp only [prime_def, primeGene, smul_dite, nsmul_zero, smul_single, smul_eq_mul, mul_one,
      single_zero, dite_eq_ite, ite_self, sum_single_index, sum_zero_index]
      split_ifs
      · exact map_zero _
      · simp [evenPart_single, Nat.even_add_one.1 ((Nat.sub_add_cancel a.rank_pos) ▸ ha)]
    · simp only [prime_def, primeGene, smul_dite, nsmul_zero, smul_single, smul_eq_mul, mul_one,
      single_zero, dite_eq_ite, ite_self, sum_single_index]
      split_ifs
      · exact map_zero _
      · simp [evenPart_single, (Nat.even_sub a.rank_pos).2 <|
          (iff_false_right Nat.not_even_one).2 ha]

lemma oddPart_prime {X : Chromosome} : X.prime.oddPart = X.evenPart.prime := by
  have := X.prime.parity_decomposition
  nth_rw 1 [X.parity_decomposition, map_add, evenPart_prime, add_comm,
    add_left_inj] at this
  exact this.symm

lemma oddPart_evenPart {X : Chromosome} : oddPart (evenPart X) = 0 := by
  simp only [oddPart, evenPart, AddMonoidHom.coe_mk, ZeroHom.coe_mk, filter_eq_zero_iff,
    filter_apply, ite_eq_right_iff]
  intro _ ho he
  rw [Nat.odd_iff] at ho
  rw [Nat.even_iff, ho] at he
  tauto

lemma evenPart_oddPart {X : Chromosome} : evenPart (oddPart X) = 0 := by
  simp only [evenPart, oddPart, AddMonoidHom.coe_mk, ZeroHom.coe_mk, filter_eq_zero_iff,
    filter_apply, ite_eq_right_iff]
  intro _ he ho
  rw [Nat.odd_iff] at ho
  rw [Nat.even_iff, ho] at he
  tauto

lemma neg_oddPart {X : Chromosome} : (- X).oddPart = - X.oddPart :=
  neg_filtered

lemma neg_evenPart {X : Chromosome} : (- X).evenPart = - X.evenPart :=
  neg_filtered

end parity

end Chromosome
