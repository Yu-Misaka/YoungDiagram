import YoungDiagram.Variety.Basic
import YoungDiagram.Chromosome.Order
import YoungDiagram.Chromosome.Parity

open Finsupp Chromosome Pointwise

namespace Chromosome

section polarized

def IsPolarized (X : Chromosome) : Prop := X.IsFiltered (·.type ≠ .NonPolarized)

lemma IsPolarized_def {X : Chromosome} :
  X.IsPolarized ↔ X.filter (·.type ≠ .NonPolarized) = X := IsFiltered_def

lemma IsPolarized_def' {X : Chromosome} :
  X.IsPolarized ↔ ∀ g ∈ X.support, g.type ≠ .NonPolarized := IsFiltered_def'

lemma IsPolarized_zero : IsPolarized 0 := IsFiltered_zero

lemma IsPolarized_single {g : Gene} {n : ℕ} (hn : n ≠ 0) :
  IsPolarized (single g n) ↔ g.type ≠ .NonPolarized := IsFiltered_single hn

lemma IsPolarized_filter {X : Chromosome} {q : Gene → Prop} [DecidablePred q]
  (h : X.IsPolarized) : IsPolarized (X.filter q) := IsFiltered_filter h

lemma IsPolarized_ofRank {k : ℕ} {ε : GeneType} (hk : 1 ≤ k) :
    (Gene.ofRank k ε).IsPolarized ↔ ε ≠ .NonPolarized := by
  rw [Gene.ofRank_def, dif_neg (by omega)]
  exact IsPolarized_single Nat.one_ne_zero

lemma IsPolarized_ofRank' {k : ℕ} {ε : GeneType} (hε : ε ≠ .NonPolarized) :
    (Gene.ofRank k ε).IsPolarized :=
  match k with
  | 0 => IsPolarized_zero
  | n + 1 => (IsPolarized_ofRank (Nat.le_add_left 1 n)).2 hε

lemma IsPolarized_ofRankAlt {k : ℕ} {ε : GeneType} (hk : 1 ≤ k) :
    (Gene.ofRankAlt k ε).IsPolarized ↔ ε ≠ .NonPolarized := by
  rw [Gene.ofRankAlt_def, IsPolarized_ofRank hk,
    GeneType.negOnePow_smul]
  split_ifs
  · rfl
  · exact GeneType.neg_ne_nonPolarized_iff.symm

lemma IsPolarized_ofRankAlt' {k : ℕ} {ε : GeneType} (hε : ε ≠ .NonPolarized) :
    (Gene.ofRankAlt k ε).IsPolarized :=
  match k with
  | 0 => IsPolarized_zero
  | n + 1 => (IsPolarized_ofRankAlt (Nat.le_add_left 1 n)).2 hε

lemma IsPolarized_iff_add {X Y : Chromosome} :
  (X + Y).IsPolarized ↔ X.IsPolarized ∧ Y.IsPolarized := IsFiltered_iff_add

lemma IsPolarized_iff_nsmul {X : Chromosome} {n : ℕ} (hn : n ≠ 0) :
  (n • X).IsPolarized ↔ X.IsPolarized := IsFiltered_iff_nsmul hn

lemma IsPolarized_iff_neg_polarized {X : Chromosome} : X.IsPolarized ↔ (- X).IsPolarized := by
  rw [IsPolarized_def', IsPolarized_def']
  constructor <;> (intro h g hg; specialize h (- g))
  · rw [GeneType.neg_ne_nonPolarized_iff, ← Gene.neg_type]
    exact h (neg_neg X ▸ (mem_neg_support.1 hg))
  · rw [GeneType.neg_ne_nonPolarized_iff, ← Gene.neg_type]
    exact h (mem_neg_support.1 hg)

lemma IsPolarized_sub {X : Chromosome} (Y : Chromosome) (hX : X.IsPolarized) :
  (X - Y).IsPolarized := IsFiltered_sub Y hX

lemma IsPolarized_iff_lift {X : Chromosome} :
  X.lift.IsPolarized ↔ X.IsPolarized := IsFiltered_iff_lift (fun _ ↦ .rfl)

lemma IsPolarized_iff_iterate_lift {X : Chromosome} {k : ℕ} :
  (lift^[k] X).IsPolarized ↔ X.IsPolarized :=
    IsFiltered_iff_iterate_lift (fun _ ↦ .rfl)

lemma IsPolarized_support_of_below_one {X : Chromosome} (hX : X.IsPolarized) :
    (X.below 1).support ⊆ {⟨1, .Positive, le_rfl⟩, ⟨1, .Negative, le_rfl⟩} := by
  intro g hg
  cases htype : g.type <;> simp only [Finset.mem_insert, Finset.mem_singleton]
  · exact False.elim <| (IsPolarized_def'.1 (IsPolarized_filter hX) g hg) htype
  · refine Or.inl ?_; simp_rw [← htype, ← support_of_below_one hg]
  · refine Or.inr ?_; simp_rw [← htype, ← support_of_below_one hg]

lemma IsPolarized_signature {X : Chromosome} (hX : X.IsPolarized) :
    (X.below 1).signature =
    ((X ⟨1, .Positive, le_rfl⟩, X ⟨1, .Negative, le_rfl⟩) : ℚ × ℚ) := by
  simp only [signature_def, sum]
  rw [Finset.sum_subset (IsPolarized_support_of_below_one hX), Finset.sum_pair (by decide),
    below_def, filter_apply_pos _ X NeZero.one_le, filter_apply_pos _ X NeZero.one_le,
    Gene.signature_of_positive rfl, Gene.signature_of_negative rfl]
  · simp
  · rintro x (h1 | h1) h2 <;> rw [Finsupp.notMem_support_iff.1 h2, Nat.cast_zero, zero_smul]

end polarized

end Chromosome

namespace Variety

section Pi

def Pi : Variety := varietyOfFilter (·.type ≠ .NonPolarized)

lemma mem_Pi_iff {X : Chromosome} :
  X ∈ Pi ↔ IsPolarized X := mem_varietyOfFilter_iff

lemma mem_Pi_iff_add {X Y : Chromosome} :
  (X + Y) ∈ Pi ↔ X ∈ Pi ∧ Y ∈ Pi := IsPolarized_iff_add

lemma prime_Pi : Pi.prime = Pi := prime_varietyOfFilter (fun _ ↦ .rfl)

lemma parityDecomp_mem_smul_Pi {X : Chromosome} {n : ℕ} (h : X ∈ n • Pi) :
  oddPart X ∈ n • Pi ∧ evenPart X ∈ n • Pi :=
  ⟨filter_mem_smul_varietyOfFilter (Odd ·.rank) h,
    filter_mem_smul_varietyOfFilter (Even ·.rank) h⟩

lemma parityDecomp_mem_Pi {X : Chromosome} (h : X ∈ Pi) :
    oddPart X ∈ Pi ∧ evenPart X ∈ Pi :=
  ⟨IsFiltered_filter h, IsFiltered_filter h⟩

lemma prime_mem_Pi {X : Chromosome} (hX : X ∈ Pi) : X.prime ∈ Pi :=
  prime_mem_varietyOfFilter (fun _ ↦ .rfl) hX

noncomputable def primePi (X : Pi) : Pi := ⟨X.1.prime, prime_mem_Pi X.2⟩

lemma primePi_iterate (X : Pi) (k : ℕ) :
    (primePi^[k] X).1 = Chromosome.prime^[k] X :=
  prime_on_varietyOfFilter_iterate (fun _ ↦ .rfl) X k

lemma prime_mem_Pi_iterate {X : Chromosome} (hX : X ∈ Pi) {k : ℕ} :
    Chromosome.prime^[k] X ∈ Pi :=
  prime_mem_varietyOfFilter_iterate (fun _ ↦ .rfl) hX

lemma sub_mem_Pi {X : Chromosome} (Y : Chromosome) (hX : X ∈ Pi) : X - Y ∈ Pi :=
  IsPolarized_sub Y hX

end Pi

end Variety

section signature

lemma signature_pi_isNat {X : Chromosome} (hX : X ∈ Variety.Pi) :
    ∃ n : ℕ × ℕ, X.signature = (↑n.1, ↑n.2) := by
  induction X using Finsupp.induction with
  | zero => use 0; rfl
  | single_add g n X hg hn h =>
    replace hX := Variety.mem_Pi_iff_add.1 hX
    obtain ⟨k, hk⟩ := h hX.2
    obtain ⟨m, hm⟩ : ∃ m : ℕ × ℕ, signature (single g n) = (↑m.1, ↑m.2) := by
      rw [← Gene.ofRank_eq_gene_smul, map_nsmul, signature_ofRank]
      split_ifs
      · use 0; rw [smul_zero]; rfl
      · have polar := (IsPolarized_single hn).1 (Variety.mem_Pi_iff.1 hX.1)
        match g.type, polar with
        | .Positive, _ =>
          rw [Gene.signature_of_positive rfl]
          split_ifs with heven
          · obtain ⟨m, hm : g.rank = m + m⟩ := heven
            use n * m; norm_num [hm]
          · obtain ⟨m, hm : g.rank = 2 * m + 1⟩ := Nat.not_even_iff_odd.1 heven
            use (n * (m + 1), n * m); norm_num [hn, hm]; ring
        | .Negative, _ =>
          rw [Gene.signature_of_negative rfl]
          split_ifs with heven
          · obtain ⟨m, hm : g.rank = m + m⟩ := heven
            use n * m; norm_num [hm]
          · obtain ⟨m, hm : g.rank = 2 * m + 1⟩ := Nat.not_even_iff_odd.1 heven
            use (n * m, n * (m + 1)); norm_num [hn, hm]; ring
    rw [map_add, hm, hk]
    exact ⟨m + k, by simp only [Prod.mk_add_mk, Prod.fst_add, Nat.cast_add, Prod.snd_add]⟩

end signature

section order

/-- The rank-1 part of an element of `Variety.Pi` is determined by its signature. -/
lemma rankOneSigInj_Pi : Variety.RankOneSigInj .Pi := by
  intro X Y hX hY h
  ext g
  by_cases hg : ¬ g.rank ≤ 1
  · rw [below_def, below_def, filter_apply_neg _ X hg, filter_apply_neg _ Y hg]
  · replace hg : g.rank = 1 := Nat.le_antisymm (by tauto) g.rank_pos
    rw [below_def, below_def, filter_apply_pos _ X (Nat.le_of_eq hg),
      filter_apply_pos _ Y (Nat.le_of_eq hg)]
    rw [IsPolarized_signature hX, IsPolarized_signature hY] at h
    cases htype : g.type
    · rw [Finsupp.notMem_support_iff.1 (fun h ↦ IsPolarized_def'.1 hX g h htype),
        Finsupp.notMem_support_iff.1 (fun h ↦ IsPolarized_def'.1 hY g h htype)]
    · simpa [← hg, ← htype] using (Prod.ext_iff.1 h).1
    · simpa [← hg, ← htype] using (Prod.ext_iff.1 h).2

/-- `(Pi, Pi)` is a sigma-pair: `prime` preserves `Pi` and `Pi` is rank-one
signature injective. -/
lemma sigmaPair_Pi : Variety.SigmaPair Variety.Pi Variety.Pi where
  prime_left := Variety.prime_Pi.le
  prime_right := Variety.prime_Pi.le
  rankOne_left := rankOneSigInj_Pi
  rankOne_right := rankOneSigInj_Pi

/-- Elements of `Variety.Pi` are determined by their sigma sequence. -/
lemma sigmaUnique_Pi : Variety.SigmaUnique .Pi :=
  sigmaPair_Pi.sigmaUnique_left

variable {A B : Chromosome} (hA : A ∈ Variety.Pi) (hB : B ∈ Variety.Pi)

include hA hB

lemma below_one_eq_of_signature_eq (h : signature (A.below 1) = signature (B.below 1)) :
    A.below 1 = B.below 1 :=
  rankOneSigInj_Pi hA hB h

lemma below_one_eq_of_sig_eq (hsig : A.signature = B.signature)
    (habove : A.above 1 = B.above 1) : A.below 1 = B.below 1 :=
  Variety.RankOneSigInj.below_one_eq_of_sig_eq rankOneSigInj_Pi hA hB hsig habove

lemma eq_of_prime_eq_sig_eq (hprime : A.prime = B.prime)
    (hsig : A.signature = B.signature) : A = B :=
  Variety.RankOneSigInj.eq_of_prime_eq_sig_eq rankOneSigInj_Pi hA hB hprime hsig

instance : PartialOrder Variety.Pi := Variety.SigmaUnique.partialOrder sigmaUnique_Pi

end order

section rank_one

lemma rank_eq_one_pi_single {X : Chromosome} (hX : X ∈ Variety.Pi) (hr : X.rank = 1) :
    ∃ ε : GeneType, ε ≠ .NonPolarized ∧ X = Gene.ofRank 1 ε := by
  obtain ⟨ε, hε⟩ := rank_one hr
  exact ⟨ε, (IsPolarized_ofRank le_rfl).1 (hε ▸ Variety.mem_Pi_iff.1 hX), hε⟩

lemma rank_one_pi_sig {X : Chromosome} (hX : X ∈ Variety.Pi) (hr : X.rank = 1) :
    X.signature = (1, 0) ∨ X.signature = (0, 1) := by
  obtain ⟨ε, ⟨h1, h2⟩⟩ := rank_eq_one_pi_single hX hr
  match ε, h1 with
  | .Positive, _ => exact h2 ▸ Or.inl signature_ofRank_one_positive
  | .Negative, _ => exact h2 ▸ Or.inr signature_ofRank_one_negative

lemma Pi_rank_one_eq_of_sig_eq {X Y : Chromosome}
    (hX : X ∈ Variety.Pi) (hY : Y ∈ Variety.Pi)
    (hrX : X.rank = 1) (hrY : Y.rank = 1)
    (hsig : X.signature = Y.signature) : X = Y := by
  obtain ⟨_, -, hXε⟩ := rank_eq_one_pi_single hX hrX
  obtain ⟨_, -, hYε⟩ := rank_eq_one_pi_single hY hrY
  refine eq_of_prime_eq_sig_eq hX hY ?_ hsig
  simp only [hXε, hYε, prime_ofRank, tsub_self, Gene.ofRank_zero]

end rank_one

noncomputable section neg

namespace Pi

open Variety

lemma neg_mem_iff {X : Chromosome} : X ∈ Pi ↔ - X ∈ Pi :=
  IsPolarized_iff_neg_polarized

instance : InvolutiveNeg Pi where
  neg X := ⟨- X, neg_mem_iff.1 X.2⟩
  neg_neg X := Subtype.val_injective (neg_neg X.1)

lemma neg_val {X : Pi} : (- X).1 = - X.1 := rfl

@[simp] lemma neg_add {X Y : Pi} : - (X + Y) = - X + - Y :=
  Subtype.val_injective Chromosome.neg_add

lemma neg_le_neg_iff {X Y : Pi} : - X ≤ - Y ↔ X ≤ Y :=
  Chromosome.neg_le_neg_iff

lemma neg_lt_neg_iff {X Y : Pi} : - X < - Y ↔ X < Y :=
  Chromosome.neg_lt_neg_iff

end Pi

end neg
