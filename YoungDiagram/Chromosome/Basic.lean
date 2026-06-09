import Mathlib.Algebra.Order.Monoid.Prod
import YoungDiagram.Gene

open Finsupp

/--
A chromosome is a non-negative integral linear combination of genes.
It forms a free commutative monoid on the set of genes.
Formalized as `Finsupp` (finite support functions) from `Gene` to `ℕ`.
-/
abbrev Chromosome := Gene →₀ ℕ

noncomputable abbrev Gene.ofRank (n : ℕ) (ε : GeneType) : Chromosome :=
  if h : n = 0 then 0
  else single ⟨n, ε, Nat.pos_of_ne_zero h⟩ 1

noncomputable abbrev Gene.ofRankAlt (n : ℕ) (ε : GeneType) : Chromosome :=
  ofRank n (Int.negOnePow (n - 1) • ε)

lemma Gene.ofRank_def {n : ℕ} {ε : GeneType} :
  ofRank n ε = if h : n = 0 then 0
    else single ⟨n, ε, Nat.pos_of_ne_zero h⟩ 1 := rfl

lemma Gene.ofRankAlt_def {n : ℕ} {ε : GeneType} :
  ofRankAlt n ε = ofRank n (Int.negOnePow (n - 1) • ε) := rfl

@[simp] lemma Gene.ofRank_zero {ε : GeneType} : ofRank 0 ε = 0 := rfl

@[simp] lemma Gene.ofRankAlt_zero {ε : GeneType} : ofRankAlt 0 ε = 0 := rfl

lemma Gene.ofRankAlt_def' {n : ℕ} {ε : GeneType} :
    ofRankAlt n ε = if Even n then ofRank n (-ε) else ofRank n ε := by
  obtain (h1 | h1) := Nat.even_or_odd n
  · simp [h1, Int.negOnePow_odd, ofRankAlt_def]
  · replace h1 := Nat.not_even_iff_odd.2 h1
    rw [ofRankAlt_def, Int.negOnePow_even,
      ite_cond_eq_false _ _ (eq_false h1), one_smul]
    simp only [Int.even_coe_nat, h1, not_false_eq_true, Int.even_sub_one]

lemma Gene.ofRankAlt_positive {k : ℕ} :
  ofRankAlt k GeneType.Positive = if Even k then
    ofRank k GeneType.Negative else ofRank k GeneType.Positive :=
  ofRankAlt_def'

lemma Gene.ofRankAlt_negative {k : ℕ} :
  ofRankAlt k GeneType.Negative = if Even k then
    ofRank k GeneType.Positive else ofRank k GeneType.Negative :=
  ofRankAlt_def'

lemma Gene.ofRank_eq_gene {g : Gene} :
    ofRank g.rank g.type = single g 1 := by
  rw [ofRank_def]
  split_ifs with h
  · absurd h; exact Nat.ne_zero_of_lt g.rank_pos
  · rfl

lemma Gene.ofRank_eq_gene_smul {g : Gene} {m : ℕ} :
    m • ofRank g.rank g.type = single g m := by
  rw [← smul_single_one, ofRank_eq_gene]

lemma Gene.ofRank_eq_gene' {n : ℕ} (hn : n ≠ 0) {ε : GeneType} :
    ofRank n ε = single ⟨n, ε, Nat.pos_of_ne_zero hn⟩ 1 := by
  rw [Gene.ofRank, dif_neg hn]

lemma Gene.ofRankAlt_eq_gene {n : ℕ} (hn : 1 ≤ n) {ε : GeneType} :
    ofRankAlt n ε = single ⟨n, Int.negOnePow (n - 1) • ε, hn⟩ 1 := by
  simp only [dif_neg (by omega : n ≠ 0)]

lemma Gene.ofRankAlt_shift_negOnePow_smul {n k : ℕ} {ε : GeneType} :
  ofRankAlt (n + k) (Int.negOnePow k • ε) =
    ofRank (n + k) (Int.negOnePow (n - 1) • ε) := by
  unfold ofRankAlt
  congr 1
  rw [GeneType.negOnePow_smul_smul, Nat.cast_add, sub_add_eq_add_sub,
    add_assoc, ← two_mul, add_comm, add_sub_assoc, Int.negOnePow_add,
    Int.negOnePow_two_mul, one_mul]

namespace Chromosome

@[elab_as_elim]
lemma induction
    {motive : Chromosome → Prop} (X : Chromosome)
    (zero : motive 0)
    (ofRank_add :
      ∀ {k : ℕ} (hk : 1 ≤ k) (ε : GeneType) {n : ℕ} {Y : Chromosome},
        ⟨k, ε, hk⟩ ∉ Y.support → n ≠ 0 →
        motive Y → motive (n • Gene.ofRank k ε + Y)) :
    motive X := Finsupp.induction X zero fun g n Y hg hn ih ↦ by
  rw [← Gene.ofRank_eq_gene_smul]
  exact ofRank_add g.rank_pos g.type hg hn ih

@[elab_as_elim]
lemma induction'
    {motive : Chromosome → Prop} (X : Chromosome)
    (zero : motive 0)
    (ofRank_add :
      ∀ {k : ℕ} (_ : 1 ≤ k) (ε : GeneType) {n : ℕ} {Y : Chromosome},
        n ≠ 0 → motive Y →
        motive (n • Gene.ofRank k ε + Y)) :
    motive X :=
  induction X zero (fun hk ε _ _ _ hn ih ↦ ofRank_add hk ε hn ih)

-- subtraction here is tsub
lemma sub_single_add_single_eq {X : Chromosome} {g : Gene} (hg : 0 < X g) :
    X - single g 1 + single g 1 = X :=
  sub_add_single_one_cancel (Nat.ne_zero_of_lt hg)

-- remember neg below is not subtract
noncomputable section Neg

/-- The sign-dual additive equivalence on chromosomes. -/
abbrev negEquiv : Chromosome ≃+ Chromosome :=
  Finsupp.domCongr Gene.negEquiv

instance : NegZeroClass Chromosome where
  neg X := X.negEquiv
  neg_zero := negEquiv.map_zero

lemma neg_eq {X : Chromosome} : - X = X.negEquiv := rfl

@[simp] lemma neg_apply (X : Chromosome) (g : Gene) :
    (- X) g = X (- g) := by
  rw [neg_eq, domCongr_apply, equivMapDomain_apply]
  rfl

instance : InvolutiveNeg Chromosome where
  neg_neg _ := by
    ext _; rw [neg_apply, neg_apply, neg_neg]

@[simp] lemma neg_zero : - (0 : Chromosome) = 0 :=
  negEquiv.map_zero

@[simp] lemma neg_add {X Y : Chromosome} : - (X + Y) = - X + - Y :=
  negEquiv.map_add X Y

@[simp] lemma neg_smul {n : ℕ} {X : Chromosome} : - (n • X) = n • (- X) :=
  ext (congrFun rfl)

@[simp] lemma neg_single {g : Gene} {n : ℕ} :
    - single g n = single (- g) n := by
  rw [neg_eq, domCongr_apply, equivMapDomain_single]; rfl

@[simp] lemma neg_ofRank {n : ℕ} {ε : GeneType} :
    - (Gene.ofRank n ε) = Gene.ofRank n (-ε) := by
  rw [Gene.ofRank_def, Gene.ofRank_def]
  split_ifs
  · exact neg_zero
  · exact neg_single

@[simp] lemma neg_ofRankAlt {n : ℕ} {ε : GeneType} :
    - (Gene.ofRankAlt n ε) = Gene.ofRankAlt n (-ε) := by
  rw [Gene.ofRankAlt_def, neg_ofRank, GeneType.neg_negOnePow_smul, sub_add_cancel,
    Gene.ofRankAlt_def, GeneType.negOnePow_smul_neg, sub_add_cancel]

lemma mem_neg_support {g : Gene} {X : Chromosome} : g ∈ X.support ↔ (- g) ∈ (- X).support := by
  constructor <;> intro h
  · rwa [mem_support_iff, neg_apply, neg_neg, ← mem_support_iff]
  · rwa [mem_support_iff, neg_apply, neg_neg, ← mem_support_iff] at h

end Neg

end Chromosome
