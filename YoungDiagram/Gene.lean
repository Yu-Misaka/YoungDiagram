import Mathlib.Algebra.Ring.NegOnePow
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Data.Finsupp.Weight

inductive GeneType
  | NonPolarized
  | Positive
  | Negative
deriving DecidableEq, Repr

instance : Neg GeneType where
  neg
    | .NonPolarized => .NonPolarized
    | .Positive => .Negative | .Negative => .Positive

instance : InvolutiveNeg GeneType where
  neg_neg
    | .NonPolarized => rfl
    | .Positive => rfl | .Negative => rfl

instance : SMul ℤˣ GeneType where
  smul n ε := if n = - 1 then - ε else ε

instance : MulAction ℤˣ GeneType where
  one_smul n := rfl
  mul_smul m n ε := by
    obtain ⟨h1 | h1, h2 | h2⟩ := And.intro (Int.units_eq_one_or m) (Int.units_eq_one_or n)
    <;> (subst h1 h2; try rfl)
    exact (neg_neg _).symm

@[simp] lemma GeneType.neg_positive : - GeneType.Positive = .Negative := rfl

@[simp] lemma GeneType.neg_negative : - GeneType.Negative = .Positive := rfl

@[simp] lemma GeneType.neg_nonPolarized : - GeneType.NonPolarized = .NonPolarized := rfl

@[simp] lemma GeneType.neg_one_smul {ε : GeneType} : (- 1 : ℤˣ) • ε = - ε := rfl

lemma GeneType.negOnePow_smul {n : ℤ} {ε : GeneType} :
    n.negOnePow • ε = if Even n then ε else - ε := by
  split_ifs with h
  · simp [(Int.negOnePow_eq_one_iff n).2 h]
  · simp [(Int.negOnePow_eq_neg_one_iff n).2 (Int.not_even_iff_odd.1 h)]

lemma GeneType.negOnePow_smul' {n : ℕ} {ε : GeneType} :
    (n : ℤ).negOnePow • ε = if Even n then ε else - ε := by
  rw [negOnePow_smul]
  exact ite_cond_congr <| propext <| Int.even_coe_nat n

@[simp] lemma GeneType.negOnePow_smul_smul {m n : ℤ} {ε : GeneType} :
    m.negOnePow • n.negOnePow • ε = (m + n).negOnePow • ε := by
  rw [Int.negOnePow_add, mul_smul]

@[simp] lemma GeneType.neg_negOnePow_smul {n : ℤ} {ε : GeneType} :
    - (n.negOnePow • ε) = (n + 1).negOnePow • ε := by
  rw [add_comm, ← negOnePow_smul_smul]; rfl

@[simp] lemma GeneType.negOnePow_smul_neg {n : ℤ} {ε : GeneType} :
    n.negOnePow • (- ε) = (n + 1).negOnePow • ε := by
  rw [← negOnePow_smul_smul]; rfl

-- make this `@[simp]` causes error in MutationsAux.lean
lemma GeneType.neg_smul {n : ℤ} {ε : GeneType} :
    - n.negOnePow • ε = - (n.negOnePow • ε) := by
  rw [← Int.negOnePow_succ, neg_negOnePow_smul]

lemma GeneType.smul_neg {n : ℤ} {ε : GeneType} :
    n.negOnePow • (- ε) = - (n.negOnePow • ε) := by
  rw [neg_negOnePow_smul, negOnePow_smul_neg]

lemma GeneType.neg_ne_nonPolarized_iff {ε : GeneType} :
    ε ≠ .NonPolarized ↔ - ε ≠ .NonPolarized := by cases ε <;> decide

lemma GeneType.neg_eq_nonPolarized_iff {ε : GeneType} :
    ε = .NonPolarized ↔ - ε = .NonPolarized :=
  Decidable.not_iff_not.1 GeneType.neg_ne_nonPolarized_iff

lemma GeneType.smul_ne_nonPolarized_iff {n : ℤ} {ε : GeneType} :
    ε ≠ .NonPolarized ↔ n.negOnePow • ε ≠ .NonPolarized := by
  rw [negOnePow_smul]
  split_ifs
  · rfl
  · exact neg_ne_nonPolarized_iff

lemma Nat.even_sub_one {n : ℕ} (hn : 1 ≤ n) :
    Even n ↔ ¬ Even (n - 1) := by
  nth_rw 1 [← Nat.sub_add_cancel hn, Nat.even_add_one]

/--
A gene is an isomorphism class of strings, defined by its rank (size) and type.
-/
@[ext] structure Gene where
  /-- The number of vertices in the string representation of the gene. -/
  rank : ℕ
  /-- The polarity of the gene. -/
  type : GeneType
  /-- The rank of a gene is strictly positive. -/
  rank_pos : 1 ≤ rank := by decide
deriving DecidableEq, Repr

namespace Gene

instance : Finsupp.NonTorsionWeight ℕ Gene.rank :=
  Finsupp.nonTorsionWeight_of ℕ Gene.rank fun i ↦ Nat.ne_zero_of_lt i.rank_pos

instance : Neg Gene where
  neg g := ⟨g.rank, - g.type, g.rank_pos⟩

@[simp] lemma neg_rank (g : Gene) : (- g).rank = g.rank := rfl

@[simp] lemma neg_type (g : Gene) : (- g).type = -g.type := rfl

instance : InvolutiveNeg Gene where
  neg_neg _ := by
    refine Gene.ext rfl ?_
    rw [neg_type, neg_type, neg_neg]

/-- The sign-dual operation as an equivalence on genes. -/
abbrev negEquiv : Gene ≃ Gene := Equiv.neg Gene

def signature (g : Gene) : ℚ × ℚ :=
  match g.type with
  | .NonPolarized => (g.rank / 2, g.rank / 2)
  | .Positive =>
    if Even g.rank then ((g.rank : ℚ) / 2, (g.rank : ℚ) / 2)
    else (((g.rank : ℚ) + 1) / 2, ((g.rank : ℚ) - 1) / 2)
  | .Negative =>
    if Even g.rank then ((g.rank : ℚ) / 2, (g.rank : ℚ) / 2)
    else (((g.rank : ℚ) - 1) / 2, ((g.rank : ℚ) + 1) / 2)

lemma signature_of_nonPolarized {g : Gene} (hg : g.type = .NonPolarized) :
    g.signature = ((g.rank : ℚ) / 2, (g.rank : ℚ) / 2) := by
  unfold Gene.signature
  simp only [hg]

lemma signature_of_positive {g : Gene} (hg : g.type = .Positive) :
  g.signature =
    if Even g.rank then ((g.rank : ℚ) / 2, (g.rank : ℚ) / 2)
    else (((g.rank : ℚ) + 1) / 2, ((g.rank : ℚ) - 1) / 2) := by
  unfold Gene.signature
  simp only [hg]

lemma signature_of_negative {g : Gene} (hg : g.type = .Negative) :
  g.signature =
    if Even g.rank then ((g.rank : ℚ) / 2, (g.rank : ℚ) / 2)
    else (((g.rank : ℚ) - 1) / 2, ((g.rank : ℚ) + 1) / 2) := by
  unfold Gene.signature
  simp only [hg]

lemma signature_even_half {g : Gene} (h : Even g.rank) :
    g.signature = ((g.rank : ℚ) / 2, (g.rank : ℚ) / 2) := by
  unfold Gene.signature
  split <;> first | rfl | exact if_pos h

lemma signature_sum_eq_rank (g : Gene) :
    g.signature.1 + g.signature.2 = (g.rank : ℚ) := by
  match h : g.type with
  | .NonPolarized =>
    rw [signature_of_nonPolarized h, add_halves]
  | .Positive =>
    rw [Gene.signature_of_positive h]
    split_ifs <;> ring
  | .Negative =>
    rw [Gene.signature_of_negative h]
    split_ifs <;> ring

lemma signature_ge (g : Gene) :
    ((g.rank - 1 : ℚ) / 2, (g.rank - 1 : ℚ) / 2) ≤ g.signature := by
  match h : g.type with
  | .NonPolarized =>
    rw [signature_of_nonPolarized h, Prod.mk_le_mk, and_self]
    linarith
  | .Positive =>
    rw [Gene.signature_of_positive h, Prod.mk_le_mk]
    split_ifs
    · simp only [and_self]; linarith
    · simp only [Std.le_refl, and_true]; linarith
  | .Negative =>
    rw [Gene.signature_of_negative h, Prod.mk_le_mk]
    split_ifs
    · simp only [and_self]; linarith
    · simp only [Std.le_refl, true_and]; linarith

lemma signature_le (g : Gene) :
    g.signature ≤ ((g.rank + 1 : ℚ) / 2, (g.rank + 1 : ℚ) / 2) := by
  match h : g.type with
  | .NonPolarized =>
    rw [signature_of_nonPolarized h, Prod.mk_le_mk, and_self]
    linarith
  | .Positive =>
    rw [Gene.signature_of_positive h, Prod.mk_le_mk]
    split_ifs
    · simp only [and_self]; linarith
    · simp only [Std.le_refl, true_and]; linarith
  | .Negative =>
    rw [Gene.signature_of_negative h, Prod.mk_le_mk]
    split_ifs
    · simp only [and_self]; linarith
    · simp only [Std.le_refl, and_true]; linarith

lemma signature_pos (g : Gene) : 0 < g.signature := by
  match hg : g.type with
  | .NonPolarized =>
    rw [signature_of_nonPolarized hg]
    exact Prod.lt_of_le_of_lt (by positivity) (by positivity [g.rank_pos])
  | .Positive =>
    rw [signature_of_positive hg]
    split_ifs
    · exact Prod.lt_of_lt_of_le (by positivity [g.rank_pos]) (by positivity)
    · exact Prod.lt_of_lt_of_le (by positivity [g.rank_pos]) <|
        Rat.div_nonneg ((Rat.le_iff_sub_nonneg 1 _).1 <|
          Nat.one_le_cast.2 g.rank_pos) rfl
  | .Negative =>
    rw [signature_of_negative hg]
    split_ifs
    · exact Prod.lt_of_le_of_lt (by positivity) (by positivity [g.rank_pos])
    · refine Prod.lt_of_le_of_lt ?_ (by positivity [g.rank_pos])
      exact Rat.div_nonneg ((Rat.le_iff_sub_nonneg 1 _).1 <|
          Nat.one_le_cast.2 g.rank_pos) rfl

lemma signature_sum_neg_eq_rank {n : ℕ} {ε : GeneType} (hn : 1 ≤ n) :
    (⟨n, ε, hn⟩ : Gene).signature + (⟨n, - ε, hn⟩ : Gene).signature = n := by
  cases ε
  · rw [GeneType.neg_nonPolarized, signature_of_nonPolarized rfl,
      Prod.mk_add_mk, add_halves]; rfl
  · rw [GeneType.neg_positive, signature_of_positive rfl, signature_of_negative rfl]
    split_ifs <;> simp only [Prod.mk_add_mk, add_halves]
    · rfl
    · rw [← add_div, ← add_div, add_add_sub_cancel, sub_add_add_cancel,
        add_self_div_two]; rfl
  · rw [GeneType.neg_negative, signature_of_negative rfl, signature_of_positive rfl]
    split_ifs <;> simp only [Prod.mk_add_mk, add_halves]
    · rfl
    · rw [← add_div, ← add_div, add_add_sub_cancel, sub_add_add_cancel,
        add_self_div_two]; rfl

lemma neq_iff {g₁ g₂ : Gene} :
    g₁ ≠ g₂ ↔ g₁.rank ≠ g₂.rank ∨ g₁.type ≠ g₂.type := by
  grind only [@Gene.ext_iff g₁ g₂]

end Gene
