import YoungDiagram.Variety.Basic
import YoungDiagram.Chromosome.Parity

open Finsupp Chromosome Pointwise

namespace Chromosome

section nonpolarized

def IsNonPolarized (X : Chromosome) : Prop := X.IsFiltered (·.type = .NonPolarized)

lemma IsNonPolarized_def {X : Chromosome} :
  X.IsNonPolarized ↔ X.filter (·.type = .NonPolarized) = X := IsFiltered_def

lemma IsNonPolarized_def' {X : Chromosome} :
  X.IsNonPolarized ↔ ∀ g ∈ X.support, g.type = .NonPolarized := IsFiltered_def'

lemma IsNonPolarized_zero : IsNonPolarized 0 := IsFiltered_zero

lemma IsNonPolarized_single {g : Gene} {n : ℕ} (hn : n ≠ 0) :
  IsNonPolarized (single g n) ↔ g.type = .NonPolarized := IsFiltered_single hn

lemma IsNonPolarized_filter {X : Chromosome} {q : Gene → Prop} [DecidablePred q]
  (h : X.IsNonPolarized) : IsNonPolarized (X.filter q) := IsFiltered_filter h

lemma IsNonPolarized_ofRank {k : ℕ} {ε : GeneType} (hk : 1 ≤ k) :
    (Gene.ofRank k ε).IsNonPolarized ↔ ε = .NonPolarized := by
  rw [Gene.ofRank_def, dif_neg (by omega)]
  exact IsNonPolarized_single Nat.one_ne_zero

lemma IsNonPolarized_iff_add {X Y : Chromosome} :
  (X + Y).IsNonPolarized ↔ X.IsNonPolarized ∧ Y.IsNonPolarized := IsFiltered_iff_add

lemma IsNonPolarized_iff_nsmul {X : Chromosome} {n : ℕ} (hn : n ≠ 0) :
  (n • X).IsNonPolarized ↔ X.IsNonPolarized := IsFiltered_iff_nsmul hn

lemma IsNonPolarized_iff_neg_polarized {X : Chromosome} :
    X.IsNonPolarized ↔ (- X).IsNonPolarized := by
  rw [IsNonPolarized_def', IsNonPolarized_def']
  constructor <;> (intro h g hg; specialize h (- g))
  · rw [GeneType.neg_eq_nonPolarized_iff, ← Gene.neg_type]
    exact h (neg_neg X ▸ (mem_neg_support.1 hg))
  · rw [GeneType.neg_eq_nonPolarized_iff, ← Gene.neg_type]
    exact h (mem_neg_support.1 hg)

lemma IsNonPolarized_iff_lift {X : Chromosome} :
  X.lift.IsNonPolarized ↔ X.IsNonPolarized := IsFiltered_iff_lift (fun _ ↦ .rfl)

lemma IsNonPolarized_iff_iterate_lift {X : Chromosome} {k : ℕ} :
  (lift^[k] X).IsNonPolarized ↔ X.IsNonPolarized :=
    IsFiltered_iff_iterate_lift (fun _ ↦ .rfl)

lemma IsNonPolarized_support_of_below_one {X : Chromosome} (hX : X.IsNonPolarized) :
    (X.below 1).support ⊆ {⟨1, .NonPolarized, le_rfl⟩} := by
  intro g hg
  simp only [Finset.mem_singleton]
  have htype : g.type = .NonPolarized :=
    IsNonPolarized_def'.1 (IsNonPolarized_filter hX) g hg
  simp_rw [← htype, ← support_of_below_one hg]

lemma IsNonPolarized_signature {X : Chromosome} (hX : X.IsNonPolarized) :
    (X.below 1).signature =
    ((X ⟨1, .NonPolarized, le_rfl⟩ : ℚ) / 2, (X ⟨1, .NonPolarized, le_rfl⟩ : ℚ) / 2) := by
  simp only [signature_def, sum]
  rw [Finset.sum_subset (IsNonPolarized_support_of_below_one hX),
    Finset.sum_singleton, below_def, filter_apply_pos _ X NeZero.one_le,
    Gene.signature_of_nonPolarized rfl]
  · ext <;> simp [Prod.smul_def, smul_eq_mul] <;> ring
  · intro x _ h2
    rw [Finsupp.notMem_support_iff.1 h2, Nat.cast_zero, zero_smul]

end nonpolarized

end Chromosome

namespace Variety

open Chromosome Pointwise

section Lambda

def Lambda : Variety := varietyOfFilter (·.type = .NonPolarized)

lemma mem_Lambda_iff {X : Chromosome} :
  X ∈ Lambda ↔ IsNonPolarized X := mem_varietyOfFilter_iff

lemma mem_Lambda_iff_add {X Y : Chromosome} :
  (X + Y) ∈ Lambda ↔ X ∈ Lambda ∧ Y ∈ Lambda := IsNonPolarized_iff_add

lemma prime_Lambda : Lambda.prime = Lambda := prime_varietyOfFilter (fun _ ↦ .rfl)

lemma parityDecomp_mem_smul_Lambda {X : Chromosome} {n : ℕ} (h : X ∈ n • Lambda) :
  oddPart X ∈ n • Lambda ∧ evenPart X ∈ n • Lambda :=
  ⟨filter_mem_smul_varietyOfFilter (Odd ·.rank) h,
    filter_mem_smul_varietyOfFilter (Even ·.rank) h⟩

lemma parityDecomp_mem_Lambda {X : Chromosome} (h : X ∈ Lambda) :
    oddPart X ∈ Lambda ∧ evenPart X ∈ Lambda :=
  ⟨IsFiltered_filter h, IsFiltered_filter h⟩

lemma prime_mem_Lambda {X : Chromosome} (hX : X ∈ Lambda) : X.prime ∈ Lambda :=
  prime_mem_varietyOfFilter (fun _ ↦ .rfl) hX

noncomputable def prime_on_Lambda (X : Lambda) : Lambda := ⟨X.1.prime, prime_mem_Lambda X.2⟩

lemma prime_on_Lambda_iterate (X : Lambda) (k : ℕ) :
    (prime_on_Lambda^[k] X).1 = Chromosome.prime^[k] X :=
  prime_on_varietyOfFilter_iterate (fun _ ↦ .rfl) X k

lemma prime_mem_Lambda_iterate {X : Chromosome} (hX : X ∈ Lambda) {k : ℕ} :
    Chromosome.prime^[k] X ∈ Lambda :=
  prime_mem_varietyOfFilter_iterate (fun _ ↦ .rfl) hX

lemma smul_Lambda_le_Lambda {n : ℕ} : n • Lambda ≤ Lambda := by
  intro x hx
  obtain ⟨y, hy, hyx : n • y = x⟩ := hx
  rw [mem_Lambda_iff, ← hyx]
  by_cases hn : n = 0
  · subst hn; rw [zero_smul]; exact IsNonPolarized_zero
  · exact (IsNonPolarized_iff_nsmul hn).2 <| mem_Lambda_iff.1 hy

end Lambda

end Variety

section order

open Chromosome

/-- The rank-1 part of an element of `Variety.Lambda` is determined by its signature. -/
lemma rankOneSigInj_Lambda : Variety.RankOneSigInj .Lambda := by
  intro X Y hX hY h
  ext g
  by_cases hg : ¬ g.rank ≤ 1
  · rw [below_def, below_def, filter_apply_neg _ X hg, filter_apply_neg _ Y hg]
  · replace hg : g.rank = 1 := Nat.le_antisymm (by tauto) g.rank_pos
    rw [below_def, below_def, filter_apply_pos _ X (Nat.le_of_eq hg),
      filter_apply_pos _ Y (Nat.le_of_eq hg)]
    rw [IsNonPolarized_signature hX, IsNonPolarized_signature hY] at h
    by_cases htype : g.type = .NonPolarized
    · have hxy : X ⟨1, .NonPolarized, le_rfl⟩ = Y ⟨1, .NonPolarized, le_rfl⟩ := by
        simpa only [Prod.mk.injEq, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, div_left_inj',
          Nat.cast_inj, and_self] using h
      convert hxy
    · rw [Finsupp.notMem_support_iff.1 (fun h ↦ htype <| IsNonPolarized_def'.1 hX g h),
        Finsupp.notMem_support_iff.1 (fun h ↦ htype <| IsNonPolarized_def'.1 hY g h)]

/-- `(Lambda, Lambda)` is a sigma-pair: `prime` preserves `Lambda` and `Lambda`
is rank-one signature injective. -/
lemma sigmaPair_Lambda : Variety.SigmaPair Variety.Lambda Variety.Lambda where
  prime_left := Variety.prime_Lambda.le
  prime_right := Variety.prime_Lambda.le
  rankOne_left := rankOneSigInj_Lambda
  rankOne_right := rankOneSigInj_Lambda

/-- Elements of `Variety.Lambda` are determined by their sigma sequence. -/
lemma sigmaUnique_Lambda : Variety.SigmaUnique Variety.Lambda :=
  sigmaPair_Lambda.sigmaUnique_left

instance : PartialOrder Variety.Lambda :=
  Variety.SigmaUnique.partialOrder sigmaUnique_Lambda

end order

noncomputable section neg

namespace Lambda

open Variety

lemma neg_mem_iff {X : Chromosome} : X ∈ Lambda ↔ - X ∈ Lambda :=
  IsNonPolarized_iff_neg_polarized

instance : InvolutiveNeg Lambda where
  neg X := ⟨- X, neg_mem_iff.1 X.2⟩
  neg_neg X := Subtype.val_injective (neg_neg X.1)

lemma neg_val {X : Lambda} : (- X).1 = - X.1 := rfl

@[simp] lemma neg_add {X Y : Lambda} : - (X + Y) = - X + - Y :=
  Subtype.val_injective Chromosome.neg_add

lemma neg_le_neg_iff {X Y : Lambda} : - X ≤ - Y ↔ X ≤ Y :=
  Chromosome.neg_le_neg_iff

lemma neg_lt_neg_iff {X Y : Lambda} : - X < - Y ↔ X < Y :=
  Chromosome.neg_lt_neg_iff

end Lambda

end neg
