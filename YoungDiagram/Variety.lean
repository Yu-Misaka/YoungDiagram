import Mathlib.Algebra.GroupWithZero.Submonoid.Pointwise
import YoungDiagram.Chromosome

noncomputable def liftGene (g : Gene) : Chromosome :=
  Gene.ofRank (g.rank + 1) g.type

abbrev Variety := AddSubmonoid Chromosome

noncomputable def Variety.prime (v : Variety) : Variety :=
  v.map Chromosome.prime

lemma Variety.prime_def (v : Variety) :
  v.prime = v.map Chromosome.prime := rfl

open Finsupp Pointwise

namespace Chromosome

/- Comment: tons of Mathlib lemmas rely on partial order for no reason.
For example `Finsupp.sum_le_sum`, which is obviously still true under pre-order.
These lemmas could make proving a lot less painful. A pull request in mathlib
is already opened to address the issue. For the time being we'll just use induction here.-/
lemma signature_filter_le (X : Chromosome) (p : Gene → Prop) [DecidablePred p] :
    signature (X.filter p) ≤ X.signature := by
  induction X using Finsupp.induction
  · rw [filter_zero]
  · expose_names
    rw [filter_add, map_add, map_add]
    refine add_le_add ?_ h_2
    by_cases ha : p a
    · rwa [filter_single_of_pos]
    · rw [filter_single_of_neg, map_zero]
      · exact signature_nonneg _
      exact ha

section lift

noncomputable def lift : Chromosome →+ Chromosome where
  toFun c := c.sum (fun g count ↦ count • liftGene g)
  map_zero' := sum_zero_index
  map_add' _ _ := sum_add_index' (fun _ ↦ zero_nsmul _)
    fun _ _ _ ↦ add_nsmul ..

lemma lift_ofRank {n : ℕ} {ε : GeneType} (hn : n ≠ 0) :
    (Gene.ofRank n ε).lift = Gene.ofRank (n + 1) ε := by
  rw [lift, Gene.ofRank_def]
  simp [hn]; rfl

lemma lift_iterate_ofRank {k n : ℕ} {ε : GeneType} (hn : n ≠ 0) :
    lift^[k] (Gene.ofRank n ε) = Gene.ofRank (n + k) ε := by
  induction k with
  | zero => rfl
  | succ k hk => rw [Function.iterate_succ_apply', hk,
    lift_ofRank (by omega), add_assoc]

lemma lift_prime_iterate_ofRank {k n : ℕ} {ε : GeneType} (h : k < n) :
    lift^[k] (prime^[k] (Gene.ofRank n ε)) = Gene.ofRank n ε := by
  rw [prime_iterate_ofRank, lift_iterate_ofRank (Nat.sub_ne_zero_iff_lt.2 h),
    Nat.sub_add_cancel h.le]

def below (k : ℕ) : Chromosome →+ Chromosome where
  toFun c := c.filter (·.rank ≤ k)
  map_zero' := filter_zero _
  map_add' _ _ := filter_add

lemma below_def {k : ℕ} {X : Chromosome} :
  X.below k = X.filter (·.rank ≤ k) := rfl

def above (k : ℕ) : Chromosome →+ Chromosome where
  toFun c := c.filter (k < ·.rank)
  map_zero' := filter_zero _
  map_add' _ _ := filter_add

lemma above_def {k : ℕ} {X : Chromosome} :
  X.above k = X.filter (k < ·.rank) := rfl

lemma rank_decomposition (X : Chromosome) (k : ℕ) :
    X = X.below k + X.above k := by
  simp [below, above]
  conv =>
    enter [2, 2, 1, a]
    rw [lt_iff_not_ge]
  rw [filter_pos_add_filter_neg]

lemma prime_elim (X : Chromosome) (k : ℕ) :
    prime^[k] X = prime^[k] (X.above k) := by
  nth_rw 1 [rank_decomposition X k]
  simp only [iterate_map_add, add_eq_right]
  induction X using Finsupp.induction with
  | zero => simp [below, filter_zero]
  | single_add g n f hg hn hf =>
    simp [below]
    by_cases hg_rank : g.rank ≤ k
    · rw [filter_single_of_pos, ← Gene.ofRank_eq_gene_smul, iterate_map_nsmul]
      · refine ⟨?_, hf⟩
        rw [IsAddTorsionFree.nsmul_eq_zero_iff, prime_iterate_ofRank,
          Nat.sub_eq_zero_of_le hg_rank, Gene.ofRank_zero]
        exact Or.inl rfl
      exact hg_rank
    · rw [filter_single_of_neg, iterate_map_zero]
      · exact ⟨rfl, hf⟩
      exact hg_rank

lemma prime_lift_leftInverse : Function.LeftInverse prime lift := by
  intro x
  induction x using Finsupp.induction with
  | zero => simp only [map_zero]
  | single_add a m f ha hm hf =>
    rw [map_add, map_add, hf, add_left_inj, ← Gene.ofRank_eq_gene_smul,
      map_nsmul, map_nsmul]
    by_cases ha : a.rank = 0
    · rw [ha, Gene.ofRank_zero, map_zero, map_zero]
    · rw [lift_ofRank ha, prime_ofRank, Nat.succ_sub_one]

lemma prime_lift_leftInverse_iterate (k : ℕ) :
    Function.LeftInverse prime^[k] lift^[k] :=
  Function.LeftInverse.iterate prime_lift_leftInverse k

lemma prime_below {k n : ℕ} {X : Chromosome} (h : n ≤ k) :
    prime^[k] (X.below n) = 0 := by
  induction X using Finsupp.induction with
  | zero => rw [map_zero, iterate_map_zero]
  | single_add a m f ha hm hf =>
    rw [map_add, iterate_map_add, hf, add_zero, below_def]
    by_cases ha : a.rank ≤ n
    · have eq : a.rank - k = 0 := by omega
      rwa [filter_single_of_pos, ← Gene.ofRank_eq_gene_smul, iterate_map_nsmul,
        prime_iterate_ofRank, IsAddTorsionFree.nsmul_eq_zero_iff_right hm, eq,
        Gene.ofRank_zero]
    · rwa [filter_single_of_neg, iterate_map_zero]

lemma lift_prime {k : ℕ} {X Y : Chromosome} :
    prime^[k] X = Y ↔ X = lift^[k] Y + X.below k := by
  constructor <;> intro h
  · induction X using Finsupp.induction generalizing Y
    · rw [iterate_map_zero] at h
      rw [← h, iterate_map_zero, map_zero, add_zero]
    · expose_names
      rw [iterate_map_add] at h
      nth_rw 1 [@h_3 (prime^[k] f) rfl, ← h, add_comm, add_comm _ (prime^[k] f),
        iterate_map_add, add_assoc, add_assoc, add_right_inj, map_add,
        ← add_assoc, add_comm _ ((below k) f), add_right_inj, below_def]
      by_cases ha : a.rank ≤ k
      · have eq : a.rank - k = 0 := by omega
        rwa [filter_single_of_pos, ← Gene.ofRank_eq_gene_smul,
          iterate_map_nsmul, iterate_map_nsmul, prime_iterate_ofRank, eq,
          Gene.ofRank_zero, iterate_map_zero, nsmul_zero, zero_add]
      · rwa [filter_single_of_neg, add_zero, ← Gene.ofRank_eq_gene_smul,
          iterate_map_nsmul, iterate_map_nsmul, prime_iterate_ofRank,
          lift_iterate_ofRank (Nat.sub_ne_zero_of_lt <| Nat.lt_of_not_le ha),
          Nat.sub_add_cancel (Nat.le_of_not_ge ha)]
  · rw [h, iterate_map_add, prime_lift_leftInverse_iterate k,
      prime_below le_rfl, add_zero]

end lift

section IsFiltered

variable {p : Gene → Prop} [DecidablePred p] {X : Chromosome}

variable (p X) in
def IsFiltered : Prop := X.filter p = X

lemma IsFiltered_def : X.IsFiltered p ↔ X.filter p = X := .rfl

lemma IsFiltered_def' : X.IsFiltered p ↔ ∀ g ∈ X.support, p g := by
  simp [IsFiltered_def, filter_eq_self_iff]

lemma IsFiltered_zero : IsFiltered p 0 := by
  simp only [IsFiltered, filter_zero]

lemma IsFiltered_single {g : Gene} : IsFiltered p (single g 1) ↔ p g := by
  rw [IsFiltered_def', support_single_ne_zero _ Nat.one_ne_zero]
  exact List.forall_mem_singleton

lemma IsFiltered_filter {q : Gene → Prop} [DecidablePred q]
    (h : X.IsFiltered p) : IsFiltered p (X.filter q) := by
  rw [IsFiltered_def'] at h ⊢
  exact fun _ hg ↦ h _ ((Finset.filter_subset ..) hg)

lemma IsFiltered_add_single {g : Gene} {n : ℕ} (hn : 1 ≤ n) :
    IsFiltered p (X + single g n) ↔ X.IsFiltered p ∧ p g := by
  constructor <;> intro h
  · by_cases hg : p g
    · simp [IsFiltered, hg] at h
      exact ⟨h, hg⟩
    · simp [IsFiltered, hg] at h
      apply_fun signature at h
      have := h ▸ (signature_filter_le X p)
      rw [map_add, signature_single g.rank_pos,
        add_le_iff_nonpos_right, Prod.le_def] at this
      change n * g.signature.1 ≤ 0 ∧ n * g.signature.2 ≤ 0 at this
      exact absurd ⟨nonpos_of_mul_nonpos_right this.1 (Rat.natCast_pos.2 hn),
        nonpos_of_mul_nonpos_right this.2 (Rat.natCast_pos.2 hn)⟩
        (not_le_of_gt g.signature_pos)
  · simp [IsFiltered, h, IsFiltered_def.1 h.1]

lemma IsFiltered_iff_add {X Y : Chromosome} :
    (X + Y).IsFiltered p ↔ X.IsFiltered p ∧ Y.IsFiltered p := by
  induction Y using Finsupp.induction with
  | zero =>
    rw [add_zero]
    exact (and_iff_left_of_imp fun _ ↦ IsFiltered_zero).symm
  | single_add g' n f hg' hn hf =>
    rw [add_comm _ f, ← add_assoc, IsFiltered_add_single
      (Nat.one_le_iff_ne_zero.2 hn), hf, IsFiltered_add_single
      (Nat.one_le_iff_ne_zero.2 hn)]
    tauto

lemma IsFiltered_iff_nsmul {n : ℕ} (hn : n ≠ 0) :
    (n • X).IsFiltered p ↔ X.IsFiltered p := by
  induction n using Nat.twoStepInduction with
  | zero => tauto
  | one => rw [one_nsmul]
  | more m _ hm =>
    specialize hm (by omega)
    change ((m + 1 + 1) • X).IsFiltered p ↔ _
    rw [add_nsmul, one_nsmul, IsFiltered_iff_add, hm]
    tauto

variable (p) in
def LiftStable : Prop :=
  ∀ g : Gene, p g ↔ p ⟨g.rank + 1, g.type, Nat.le_add_left 1 g.rank⟩

lemma IsFiltered_iff_lift (hp : LiftStable p) :
    X.lift.IsFiltered p ↔ X.IsFiltered p := by
  constructor <;> intro h
  · induction X using Finsupp.induction
    · exact IsFiltered_zero
    · expose_names
      rw [map_add, IsFiltered_iff_add] at h
      specialize h_3 h.2
      refine IsFiltered_iff_add.2 ⟨?_, h_3⟩
      replace h := h.1
      simp [lift, liftGene] at h
      rw [← smul_single_one, IsFiltered_iff_nsmul h_2, IsFiltered_single] at h ⊢
      exact (hp _).2 h
  · induction X using Finsupp.induction
    · exact IsFiltered_zero
    · expose_names
      rw [map_add, IsFiltered_iff_add]
      rw [IsFiltered_iff_add] at h
      refine ⟨?_, h_3 h.2⟩
      replace h := h.1
      simp [lift, liftGene]
      rw [← smul_single_one, IsFiltered_iff_nsmul h_2, IsFiltered_single] at h ⊢
      exact (hp _).1 h

lemma IsFiltered_iff_iterate_lift {k : ℕ} (hp : LiftStable p) :
    (lift^[k] X).IsFiltered p ↔ X.IsFiltered p := by
  induction k with
  | zero => rfl
  | succ n hn => rwa [Function.iterate_succ_apply', IsFiltered_iff_lift hp]

variable (p) in
def varietyOfFilter : Variety where
  carrier := {X : Chromosome | X.IsFiltered p}
  add_mem' ha hb := IsFiltered_iff_add.2 ⟨ha, hb⟩
  zero_mem' := IsFiltered_zero

lemma mem_varietyOfFilter_iff :
  X ∈ varietyOfFilter p ↔ X.IsFiltered p := .rfl

lemma prime_varietyOfFilter (hp : LiftStable p) :
    (varietyOfFilter p).prime = varietyOfFilter p := by
  refine le_antisymm ?_ ?_ <;> intro x hx
  · rw [Variety.prime_def, AddSubmonoid.mem_map] at hx
    rcases hx with ⟨y, ⟨h1, h2⟩⟩
    rw [mem_varietyOfFilter_iff, ← h2]
    induction y using Finsupp.induction generalizing x
    · exact IsFiltered_zero
    · expose_names
      rw [mem_varietyOfFilter_iff, IsFiltered_iff_add] at h1
      rw [map_add, IsFiltered_iff_add]
      refine ⟨?_, h_2 h1.2 rfl⟩
      simp [prime, primeGene]
      split_ifs with h
      · exact IsFiltered_zero
      · rw [← smul_single_one, IsFiltered_iff_nsmul h_1, IsFiltered_single] at h1 ⊢
        rw [hp]
        convert h1.1
        refine Nat.sub_add_cancel a.rank_pos
  · rw [Variety.prime_def, AddSubmonoid.mem_map]
    use x.lift
    refine ⟨?_, prime_lift_leftInverse x⟩
    exact (IsFiltered_iff_lift hp).2 hx

lemma varietyOfFilter_closed_under_filter (q : Gene → Prop) [DecidablePred q]
  {n : ℕ} (h : X ∈ n • (varietyOfFilter p)) :
    X.filter q ∈ n • (varietyOfFilter p) := by
  obtain ⟨Y, ⟨h1, h2 : n • Y = X⟩⟩ := h
  refine ⟨Y.filter q, IsFiltered_filter h1, (?_ : n • (Y.filter q) = X.filter q)⟩
  rw [← h2, filter_smul]

end IsFiltered

section parity

def oddPart : Chromosome →+ Chromosome where
  toFun c := c.filter (Odd ·.rank)
  map_zero' := filter_zero _
  map_add' _ _ := filter_add

def evenPart : Chromosome →+ Chromosome where
  toFun c := c.filter (Even ·.rank)
  map_zero' := filter_zero _
  map_add' _ _ := filter_add

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
  simp [oddPart, evenPart]
  conv =>
    enter [2, 2, 1, a]
    rw [← Nat.not_odd_iff_even]
  rw [filter_pos_add_filter_neg]

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
    · simp [prime, primeGene]
      split_ifs
      · exact map_zero _
      · simp [evenPart_single, Nat.even_add_one.1 ((Nat.sub_add_cancel a.rank_pos) ▸ ha)]
    · simp [prime, primeGene]
      split_ifs
      · exact map_zero _
      · simp [evenPart_single, (Nat.even_sub a.rank_pos).2 <|
          (iff_false_right Nat.not_even_one).2 ha]

lemma oddPart_prime {X : Chromosome} : X.prime.oddPart = X.evenPart.prime := by
  have := X.prime.parity_decomposition
  nth_rw 1 [X.parity_decomposition, map_add, evenPart_prime, add_comm,
    add_left_inj] at this
  exact this.symm

lemma oddPart_evenPart_eq_zero {X : Chromosome} : oddPart (evenPart X) = 0 := by
  simp [oddPart, evenPart, filter_eq_zero_iff, filter_apply]
  intro _ ho he
  rw [Nat.odd_iff] at ho
  rw [Nat.even_iff, ho] at he
  tauto

lemma evenPart_oddPart_eq_zero {X : Chromosome} : evenPart (oddPart X) = 0 := by
  simp [oddPart, evenPart, filter_eq_zero_iff, filter_apply]
  intro _ he ho
  rw [Nat.odd_iff] at ho
  rw [Nat.even_iff, ho] at he
  tauto

end parity

section polarized

def IsPolarized (X : Chromosome) : Prop := X.IsFiltered (·.type ≠ .NonPolarized)

lemma IsPolarized_def {X : Chromosome} :
  X.IsPolarized ↔ X.filter (·.type ≠ .NonPolarized) = X := IsFiltered_def

lemma IsPolarized_def' {X : Chromosome} :
  X.IsPolarized ↔ ∀ g ∈ X.support, g.type ≠ .NonPolarized := IsFiltered_def'

lemma IsPolarized_zero : IsPolarized 0 := IsFiltered_zero

lemma IsPolarized_single {g : Gene} :
  IsPolarized (single g 1) ↔ g.type ≠ .NonPolarized := IsFiltered_single

lemma IsPolarized_filter {X : Chromosome} {q : Gene → Prop} [DecidablePred q]
  (h : X.IsPolarized) : IsPolarized (X.filter q) := IsFiltered_filter h

lemma IsPolarized_ofRank {k : ℕ} {ε : GeneType} (hk : 1 ≤ k) :
    (Gene.ofRank k ε).IsPolarized ↔ ε ≠ .NonPolarized := by
  rw [Gene.ofRank_def]
  split_ifs
  · omega
  · exact IsPolarized_single

lemma IsPolarized_ofRank' {k : ℕ} {ε : GeneType} (hε : ε ≠ .NonPolarized) :
    (Gene.ofRank k ε).IsPolarized :=
  match k with
  | 0 => IsPolarized_zero
  | n + 1 => (IsPolarized_ofRank (Nat.le_add_left 1 n)).2 hε

lemma IsPolarized_ofRankAlt {k : ℕ} {ε : GeneType} (hk : 1 ≤ k) :
    (Gene.ofRankAlt k ε).IsPolarized ↔ ε ≠ .NonPolarized := by
  rw [Gene.ofRankAlt_def, IsPolarized_ofRank hk,
    GeneType.neg_one_pow_smul]
  split_ifs
  · rfl
  · exact GeneType.ne_nonPolarized_iff_neg_ne.symm

lemma IsPolarized_ofRankAlt' {k : ℕ} {ε : GeneType} (hε : ε ≠ .NonPolarized) :
    (Gene.ofRankAlt k ε).IsPolarized :=
  match k with
  | 0 => IsPolarized_zero
  | n + 1 => (IsPolarized_ofRankAlt (Nat.le_add_left 1 n)).2 hε

lemma IsPolarized_iff_add {X Y : Chromosome} :
  (X + Y).IsPolarized ↔ X.IsPolarized ∧ Y.IsPolarized := IsFiltered_iff_add

lemma IsPolarized_iff_nsmul {X : Chromosome} {n : ℕ} (hn : n ≠ 0) :
  (n • X).IsPolarized ↔ X.IsPolarized := IsFiltered_iff_nsmul hn

lemma IsPolarized_iff_lift {X : Chromosome} :
  X.lift.IsPolarized ↔ X.IsPolarized := IsFiltered_iff_lift (fun _ ↦ .rfl)

lemma IsPolarized_iff_iterate_lift {X : Chromosome} {k : ℕ} :
  (lift^[k] X).IsPolarized ↔ X.IsPolarized :=
    IsFiltered_iff_iterate_lift (fun _ ↦ .rfl)

end polarized

section nonpolarized

def IsNonPolarized (X : Chromosome) : Prop := X.IsFiltered (·.type = .NonPolarized)

lemma IsNonPolarized_def {X : Chromosome} :
  X.IsNonPolarized ↔ X.filter (·.type = .NonPolarized) = X := IsFiltered_def

lemma IsNonPolarized_def' {X : Chromosome} :
  X.IsNonPolarized ↔ ∀ g ∈ X.support, g.type = .NonPolarized := IsFiltered_def'

lemma IsNonPolarized_zero : IsNonPolarized 0 := IsFiltered_zero

lemma IsNonPolarized_single {g : Gene} :
  IsNonPolarized (single g 1) ↔ g.type = .NonPolarized := IsFiltered_single

lemma IsNonPolarized_filter {X : Chromosome} {q : Gene → Prop} [DecidablePred q]
  (h : X.IsNonPolarized) : IsNonPolarized (X.filter q) := IsFiltered_filter h

lemma IsNonPolarized_ofRank {k : ℕ} {ε : GeneType} (hk : 1 ≤ k) :
    (Gene.ofRank k ε).IsNonPolarized ↔ ε = .NonPolarized := by
  rw [Gene.ofRank_def]
  split_ifs
  · omega
  · exact IsNonPolarized_single

lemma IsNonPolarized_iff_add {X Y : Chromosome} :
  (X + Y).IsNonPolarized ↔ X.IsNonPolarized ∧ Y.IsNonPolarized := IsFiltered_iff_add

lemma IsNonPolarized_iff_nsmul {X : Chromosome} {n : ℕ} (hn : n ≠ 0) :
  (n • X).IsNonPolarized ↔ X.IsNonPolarized := IsFiltered_iff_nsmul hn

lemma IsNonPolarized_iff_lift {X : Chromosome} :
  X.lift.IsNonPolarized ↔ X.IsNonPolarized := IsFiltered_iff_lift (fun _ ↦ .rfl)

lemma IsNonPolarized_iff_iterate_lift {X : Chromosome} {k : ℕ} :
  (lift^[k] X).IsNonPolarized ↔ X.IsNonPolarized :=
    IsFiltered_iff_iterate_lift (fun _ ↦ .rfl)

end nonpolarized

end Chromosome

namespace Variety

open Chromosome

section Pi

def Pi : Variety := varietyOfFilter (·.type ≠ .NonPolarized)

lemma mem_Pi_iff {X : Chromosome} :
  X ∈ Pi ↔ IsPolarized X := mem_varietyOfFilter_iff

lemma prime_Pi : Pi.prime = Pi := prime_varietyOfFilter (fun _ ↦ .rfl)

lemma Pi_closed_under_parityDecomp {X : Chromosome} {n : ℕ} (h : X ∈ n • Pi) :
  oddPart X ∈ n • Pi ∧ evenPart X ∈ n • Pi :=
  ⟨varietyOfFilter_closed_under_filter (Odd ·.rank) h,
    varietyOfFilter_closed_under_filter (Even ·.rank) h⟩

lemma Pi_closed_under_parityDecomp₁ {X : Chromosome} (h : X ∈ Pi) :
    oddPart X ∈ Pi ∧ evenPart X ∈ Pi :=
  ⟨IsFiltered_filter h, IsFiltered_filter h⟩

end Pi

section Lambda

def Lambda : Variety := varietyOfFilter (·.type = .NonPolarized)

lemma mem_Lambda_iff {X : Chromosome} :
  X ∈ Lambda ↔ IsNonPolarized X := mem_varietyOfFilter_iff

lemma prime_Lambda : Lambda.prime = Lambda := prime_varietyOfFilter (fun _ ↦ .rfl)

lemma Lambda_closed_under_parityDecomp {X : Chromosome} {n : ℕ} (h : X ∈ n • Lambda) :
  oddPart X ∈ n • Lambda ∧ evenPart X ∈ n • Lambda :=
  ⟨varietyOfFilter_closed_under_filter (Odd ·.rank) h,
    varietyOfFilter_closed_under_filter (Even ·.rank) h⟩

lemma Lambda_closed_under_parityDecomp₁ {X : Chromosome} (h : X ∈ Lambda) :
    oddPart X ∈ Lambda ∧ evenPart X ∈ Lambda :=
  ⟨IsFiltered_filter h, IsFiltered_filter h⟩

end Lambda

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
      evenPart_oddPart_eq_zero, add_zero, evenPart_prime] at h12
  have eq2 : (evenPart y₂).prime = oddPart x := by
    apply_fun oddPart at h22
    rwa [y₂.parity_decomposition, map_add, map_add, ← oddPart_prime,
      ← evenPart_prime, oddPart_idempotent, oddPart_idempotent, oddPart_evenPart_eq_zero,
      zero_add, oddPart_prime] at h22
  refine ⟨y₁.oddPart + y₂.evenPart, ⟨add_mem ⟨?_, ?_⟩ ⟨?_, ?_⟩, ?_⟩⟩
  · rw [evenPart_oddPart_eq_zero]; exact zero_mem _
  · rw [oddPart_idempotent]; exact (hv2 h11).1
  · rw [evenPart_idempotent]; exact (hv1 h21).2
  · rw [oddPart_evenPart_eq_zero]; exact zero_mem _
  · rw [map_add, eq1, eq2, add_comm]; exact x.parity_decomposition.symm

end Mix

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
    rw [prime_Mix_eq Lambda_closed_under_parityDecomp₁
      Pi_closed_under_parityDecomp₁, prime_Pi, prime_Lambda]
  | 2 =>
    change (Mix (Pi, Lambda)).prime = Mix (Lambda, Pi)
    rw [prime_Mix_eq Pi_closed_under_parityDecomp₁
      Lambda_closed_under_parityDecomp₁, prime_Pi, prime_Lambda]
  | 3 =>
    change (Mix (2 • Lambda, Pi)).prime = Mix (Pi, 2 • Lambda)
    rw [prime_Mix_eq Lambda_closed_under_parityDecomp
      Pi_closed_under_parityDecomp₁, prime_Pi, variety_prime_smul, prime_Lambda]
  | 4 =>
    change (Mix (Pi, 2 • Lambda)).prime = Mix (2 • Lambda, Pi)
    rw [prime_Mix_eq Pi_closed_under_parityDecomp₁
      Lambda_closed_under_parityDecomp, prime_Pi, variety_prime_smul, prime_Lambda]

lemma Label.prime_eq_iterate {i : Fin 5} {k : ℕ} :
    Label (prime^[k] i) = Variety.prime^[k] (Label i) := by
  induction k
  · rw [Function.iterate_zero, Function.iterate_zero]; rfl
  · expose_names
    nth_rw 1 [add_comm, Function.iterate_add_apply, Function.iterate_one,
      ← Label.prime_eq, h, Function.iterate_add_apply, Function.iterate_one]
    exact (Function.iterate_succ_apply' ..).symm

lemma mem_prime_iterate {k : ℕ} {X : Chromosome} {V : Variety} (hX : X ∈ V) :
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
  exact mem_prime_iterate hX

lemma Label.prime_iterate_zero {k : ℕ} : Label.prime^[k] 0 = 0 :=
  Function.iterate_fixed rfl k

end Variety
