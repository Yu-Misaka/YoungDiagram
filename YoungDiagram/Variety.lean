import Mathlib.Algebra.GroupWithZero.Submonoid.Pointwise
import YoungDiagram.Chromosome

noncomputable def liftGene (g : Gene) : Chromosome :=
  Gene.ofRank (g.rank + 1) g.type

abbrev variety := AddSubmonoid Chromosome

noncomputable def variety.prime (v : variety) : variety :=
  v.map Chromosome.prime

lemma variety.prime_def (v : variety) :
  v.prime = v.map Chromosome.prime := rfl

open Finsupp

namespace Chromosome

/- Comment: tons of Mathlib lemmas rely on partial order for no reason.
For example `Finsupp.sum_le_sum`, which is obviously still true under pre-order.
These lemmas could make proving a lot less painful. A pull request in mathlib
is already opened to address the issue. For the time being we'll just leave a
sorry here.-/
lemma filtered_sig_leq (X : Chromosome) (p : Gene → Prop) [DecidablePred p] :
    signature (X.filter p) ≤ X.signature := by
  sorry

section lift

noncomputable def lift : Chromosome →+ Chromosome where
  toFun c := c.sum (fun g count ↦ count • liftGene g)
  map_zero' := sum_zero_index
  map_add' _ _ := sum_add_index' (fun _ ↦ zero_nsmul _)
    fun _ _ _ ↦ add_nsmul ..

abbrev below (X : Chromosome) (k : ℕ) : Chromosome := X.filter (·.rank ≤ k)

abbrev above (X : Chromosome) (k : ℕ) : Chromosome := X.filter (k < ·.rank)

lemma rankDecomposition (X : Chromosome) (k : ℕ) :
    X = X.below k + X.above k := by
  simp [below, above]
  conv =>
    enter [2, 2, 1, a]
    rw [lt_iff_not_ge]
  rw [filter_pos_add_filter_neg]

lemma prime_elim (X : Chromosome) (k : ℕ) :
    prime^[k] X = prime^[k] (X.above k) := by
  nth_rw 1 [rankDecomposition X k]
  simp only [iterate_map_add, add_eq_right]
  induction X using Finsupp.induction with
  | zero => simp [below, filter_zero]
  | single_add g n f hg hn hf =>
    simp [below]
    by_cases hg_rank : g.rank ≤ k
    · rw [filter_single_of_pos, ← Gene.ofRank_eq_gene', iterate_map_nsmul]
      · refine ⟨?_, hf⟩
        rw [IsAddTorsionFree.nsmul_eq_zero_iff, prime_ofRank_it,
          Nat.sub_eq_zero_of_le hg_rank, Gene.ofRank_zero]
        exact Or.inl rfl
      exact hg_rank
    · rw [filter_single_of_neg, iterate_map_zero]
      · exact ⟨rfl, hf⟩
      exact hg_rank

lemma prime_lift_LeftInverse : Function.LeftInverse prime lift := by
  intro x
  induction x using Finsupp.induction with
  | zero => simp only [map_zero]
  | single_add a m f ha hm hf =>
    rw [map_add, map_add, hf, add_left_inj]
    simp [prime, lift, liftGene, primeGene]
    split_ifs with h
    · rw [← Gene.ofRank_eq_gene', h, Gene.ofRank_zero, smul_zero]
    · rfl

lemma prime_lift_LeftInverse_it (k : ℕ) :
    Function.LeftInverse prime^[k] lift^[k] :=
  Function.LeftInverse.iterate prime_lift_LeftInverse k

end lift

section IsFiltered

variable {p : Gene → Prop} [DecidablePred p] {X : Chromosome}

variable (p X) in
def IsFiltered : Prop := X.filter p = X

lemma IsFiltered_def : X.IsFiltered p ↔ X.filter p = X := .rfl

lemma IsFiltered_zero : IsFiltered p 0 := by
  simp only [IsFiltered, filter_zero]

lemma IsFiltered_single {g : Gene} : IsFiltered p (single g 1) ↔ p g := by
  simp [IsFiltered]
  by_cases hg : p g
  · exact ⟨fun _ ↦ hg, fun _ ↦ filter_single_of_pos _ hg⟩
  · constructor <;> intro h
    · symm at h
      rw [filter_single_of_neg, single_eq_zero] at h <;> tauto
    · tauto

lemma IsFiltered_add_single {g : Gene} {n : ℕ} (hn : 1 ≤ n) :
    IsFiltered p (X + single g n) ↔ X.IsFiltered p ∧ p g := by
  constructor <;> intro h
  · by_cases hg : p g
    · simp [IsFiltered, hg] at h
      exact ⟨h, hg⟩
    · simp [IsFiltered, hg] at h
      apply_fun signature at h
      have := h ▸ (filtered_sig_leq X p)
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

variable (p) in
def varietyOfFilter : variety where
  carrier := {X : Chromosome | X.IsFiltered p}
  add_mem' ha hb := IsFiltered_iff_add.2 ⟨ha, hb⟩
  zero_mem' := IsFiltered_zero

lemma mem_varietyOfFilter_iff {X : Chromosome} :
  X ∈ varietyOfFilter p ↔ X.IsFiltered p := .rfl

lemma prime_varietyOfFilter (hp : LiftStable p) :
    (varietyOfFilter p).prime = varietyOfFilter p := by
  refine le_antisymm ?_ ?_ <;> intro x hx
  · rw [variety.prime_def, AddSubmonoid.mem_map] at hx
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
  · rw [variety.prime_def, AddSubmonoid.mem_map]
    use x.lift
    refine ⟨?_, prime_lift_LeftInverse x⟩
    exact (IsFiltered_iff_lift hp).2 hx

end IsFiltered

section parity

abbrev o (X : Chromosome) : Chromosome := X.filter (Odd  ·.rank)
abbrev e (X : Chromosome) : Chromosome := X.filter (Even ·.rank)

def IsOdd (X : Chromosome) : Prop  := X.o = X

lemma IsOdd_def {X : Chromosome} :
  X.IsOdd ↔ X.filter (Odd  ·.rank) = X := .rfl

def IsEven (X : Chromosome) : Prop := X.e = X

lemma IsEven_def {X : Chromosome} :
  X.IsEven ↔ X.filter (Even ·.rank) = X := .rfl

lemma parityDecomposition (X : Chromosome) : X = X.o + X.e := by
  simp [o, e]
  conv =>
    enter [2, 2, 1, a]
    rw [← Nat.not_odd_iff_even]
  rw [filter_pos_add_filter_neg]

end parity

section polarized

def IsPolarized (X : Chromosome) : Prop := X.IsFiltered (·.type ≠ .NonPolarized)

lemma IsPolarized_def {X : Chromosome} :
  X.IsPolarized ↔ X.filter (·.type ≠ .NonPolarized) = X := IsFiltered_def

lemma IsPolarized_zero : IsPolarized 0 := IsFiltered_zero

lemma IsPolarized_single {g : Gene} :
  IsPolarized (single g 1) ↔ g.type ≠ .NonPolarized := IsFiltered_single

lemma IsPolarized_ofRank {k : ℕ} {ε : GeneType} (hk : 1 ≤ k) :
    (Gene.ofRank k ε).IsPolarized ↔ ε ≠ .NonPolarized := by
  rw [Gene.ofRank_def]
  split_ifs
  · omega
  · exact IsPolarized_single

lemma IsPolarized_ofRank' {k : ℕ} {ε : GeneType} (hk : 1 ≤ k) :
    (Gene.ofRank' k ε).IsPolarized ↔ ε ≠ .NonPolarized := by
  rw [Gene.ofRank'_def, IsPolarized_ofRank hk,
    GeneType.neg_one_pow_smul]
  split_ifs
  · rfl
  · exact GeneType.nonpolarized_iff_neg_non.symm

lemma IsPolarized_iff_add {X Y : Chromosome} :
  (X + Y).IsPolarized ↔ X.IsPolarized ∧ Y.IsPolarized := IsFiltered_iff_add

lemma IsPolarized_iff_nsmul {X : Chromosome} {n : ℕ} (hn : n ≠ 0) :
  (n • X).IsPolarized ↔ X.IsPolarized := IsFiltered_iff_nsmul hn

lemma IsPolarized_iff_lift {X : Chromosome} :
  X.lift.IsPolarized ↔ X.IsPolarized := IsFiltered_iff_lift (fun _ ↦ .rfl)

end polarized

section nonpolarized

def IsNonPolarized (X : Chromosome) : Prop := X.IsFiltered (·.type = .NonPolarized)

lemma IsNonPolarized_def {X : Chromosome} :
  X.IsNonPolarized ↔ X.filter (·.type = .NonPolarized) = X := IsFiltered_def

lemma IsNonPolarized_zero : IsNonPolarized 0 := IsFiltered_zero

lemma IsNonPolarized_single {g : Gene} :
  IsNonPolarized (single g 1) ↔ g.type = .NonPolarized := IsFiltered_single

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

end nonpolarized

section Pi

def Pi : variety := varietyOfFilter (·.type ≠ .NonPolarized)

lemma mem_Pi_iff {X : Chromosome} :
  X ∈ Pi ↔ X.IsPolarized := mem_varietyOfFilter_iff

lemma prime_Pi : Pi.prime = Pi := prime_varietyOfFilter (fun _ ↦ .rfl)

end Pi

section Lambda

def Lambda : variety := varietyOfFilter (·.type = .NonPolarized)

lemma mem_Lambda_iff {X : Chromosome} :
  X ∈ Lambda ↔ X.IsNonPolarized := mem_varietyOfFilter_iff

lemma prime_Lambda : Lambda.prime = Lambda := prime_varietyOfFilter (fun _ ↦ .rfl)

end Lambda

section Mix

def Mix (v : variety × variety) : variety where
  carrier := {X : Chromosome | X.e ∈ v.1 ∧ X.o ∈ v.2}
  add_mem' ha hb := by
    simp at *
    exact ⟨add_mem ha.1 hb.1, add_mem ha.2 hb.2⟩
  zero_mem' := by simp [filter_zero]

lemma mem_Mix_iff {X : Chromosome} {v : variety × variety} :
  X ∈ Mix v ↔ X.e ∈ v.1 ∧ X.o ∈ v.2 := .rfl

lemma prime_Mix {v : variety × variety} :
    (Mix v).prime = Mix ⟨v.2.prime, v.1.prime⟩ := by
  sorry

end Mix

end Chromosome

open Chromosome Pointwise

noncomputable def VarietyLabel : Fin 5 → variety
  | 0 => Pi
  | 1 => Mix (Lambda, Pi)
  | 2 => Mix (Pi, Lambda)
  | 3 => Mix (2 • Lambda, Pi)
  | 4 => Mix (Pi, 2 • Lambda)
