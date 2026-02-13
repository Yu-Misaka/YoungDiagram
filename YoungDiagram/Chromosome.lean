import Mathlib.Algebra.Order.Monoid.Prod
import Mathlib.Algebra.Star.Module
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Data.Finsupp.Order
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
  Gene.ofRank n (Int.negOnePow (n - 1) • ε)

lemma Gene.ofRank_def {n : ℕ} {ε : GeneType} :
  Gene.ofRank n ε = if h : n = 0 then 0
    else single ⟨n, ε, Nat.pos_of_ne_zero h⟩ 1 := rfl

lemma Gene.ofRankAlt_def {n : ℕ} {ε : GeneType} :
  Gene.ofRankAlt n ε = Gene.ofRank n (Int.negOnePow (n - 1) • ε) := rfl

@[simp] lemma Gene.ofRank_zero {ε : GeneType} : Gene.ofRank 0 ε = 0 := rfl

@[simp] lemma Gene.ofRankAlt_zero {ε : GeneType} : Gene.ofRankAlt 0 ε = 0 := rfl

lemma Gene.ofRank_eq_gene {g : Gene} :
    Gene.ofRank g.rank g.type = single g 1 := by
  rw [Gene.ofRank_def]
  split_ifs with h
  · absurd h; exact Nat.ne_zero_of_lt g.rank_pos
  · rfl

lemma Gene.ofRank_eq_gene_smul {g : Gene} {m : ℕ} :
    m • Gene.ofRank g.rank g.type = single g m := by
  rw [← smul_single_one, ofRank_eq_gene]

namespace Chromosome

def maxRank (c : Chromosome) : ℕ :=
  c.support.sup (fun g ↦ g.rank)

def rank : Chromosome →+ ℕ where
  toFun c := c.sum (fun g count ↦ count • g.rank)
  map_zero' := sum_zero_index
  map_add' _ _ := sum_add_index' (fun _ ↦ zero_smul ..) (fun _ _ _ ↦ add_smul ..)

section signature

/--
The signature of a chromosome is the weighted sum of the signatures of its constituent genes.
-/
def signature : Chromosome →+ ℚ × ℚ where
  toFun c := c.sum (fun g count ↦ (count : ℚ) • g.signature)
  map_zero' := sum_zero_index
  map_add' _ _ := by
    refine sum_add_index' (by simp) fun _ _ _ ↦ ?_
    simp only [Nat.cast_add]
    exact Module.add_smul ..

lemma signature_nonneg (X : Chromosome) : 0 ≤ X.signature := by
  dsimp [signature]
  exact sum_nonneg' fun g ↦
    smul_nonneg Rat.natCast_nonneg g.signature_pos.le

@[simp] lemma signature_ofRank_zero {ε : GeneType} :
    (Gene.ofRank 0 ε).signature = 0 := rfl

lemma signature_ofRank {n : ℕ} {ε : GeneType} :
  (Gene.ofRank n ε).signature =
    if h : n = 0 then 0
    else (⟨n, ε, Nat.pos_of_ne_zero h⟩ : Gene).signature := by
  dsimp [signature]
  split_ifs
  · rfl
  · simp

@[simp] lemma signature_ofRank_one_positive :
    (Gene.ofRank 1 .Positive).signature = (1, 0) := by
  simp [signature_ofRank]; rfl

@[simp] lemma signature_ofRank_one_negative :
    (Gene.ofRank 1 .Negative).signature = (0, 1) := by
  simp [signature_ofRank]; rfl

@[simp] lemma signature_single {k : ℕ} {n : ℕ} (hk : 1 ≤ k) {ε : GeneType} :
    signature (single (⟨k, ε, hk⟩ : Gene) n) =
    n * (⟨k, ε, hk⟩ : Gene).signature := by
  simp [signature]; rfl

lemma signature_ofRank_nonPolarized {n : ℕ} :
    (Gene.ofRank n .NonPolarized).signature =
    (Gene.ofRank n .NonPolarized).signature.swap := by
  simp [signature_ofRank]
  split_ifs
  · rfl
  · rw [Gene.signature_eq_nonPolarized rfl]; rfl

lemma signature_ofRank_swap {n : ℕ} {ε : GeneType} :
    (Gene.ofRank n (- ε)).signature = (Gene.ofRank n ε).signature.swap := by
  cases ε
  · exact signature_ofRank_nonPolarized
  all_goals
    simp [signature_ofRank]; split_ifs
    · rfl
    · first | rw [Gene.signature_eq_negative rfl, Gene.signature_eq_positive rfl] |
        rw [Gene.signature_eq_positive rfl, Gene.signature_eq_negative rfl]
      simp only; split_ifs <;> rfl

lemma signature_ofRank_positive_eq {k : ℕ} (hk : 1 ≤ k) :
    (Gene.ofRank k .Positive).signature =
    (Gene.ofRank (k - 1) .Negative).signature + (1, 0) := by
  have hk' : k ≠ 0 := by omega
  simp [hk', signature_ofRank]
  split_ifs with h
  · replace hk : k = 1 := by omega
    simp [Gene.signature_eq_positive, hk]
  · simp [Gene.signature_eq_positive]
    split_ifs with h1
    · have : ¬ Even (k - 1) := by
        rwa [(Nat.sub_eq_iff_eq_add hk).mp rfl, Nat.even_add_one] at h1
      simp [Gene.signature_eq_negative, this, Nat.cast_pred hk]
      ring
    · have : Even (k - 1) := by
        rwa [(Nat.sub_eq_iff_eq_add hk).mp rfl, Nat.even_add_one, not_not] at h1
      simp [Gene.signature_eq_negative, this, Nat.cast_pred hk]
      ring

lemma signature_ofRank_negative_eq {k : ℕ} (hk : 1 ≤ k) :
    (Gene.ofRank k .Negative).signature =
    (Gene.ofRank (k - 1) .Positive).signature + (0, 1) := by
  rw [← GeneType.neg_pos_eq_neg, signature_ofRank_swap,
    signature_ofRank_positive_eq hk, Prod.swap_add, ← signature_ofRank_swap]
  rfl

lemma signature_ofRank_eq {k : ℕ} {ε : GeneType} (hk : 1 ≤ k) (hε : ε ≠ .NonPolarized) :
    (Gene.ofRank k ε).signature =
    (Gene.ofRank (k - 1) (- ε)).signature + (Gene.ofRank 1 ε).signature := by
  match ε, hε with
  | .Positive, _ => simp [signature_ofRank_positive_eq hk]
  | .Negative, _ => simp [signature_ofRank_negative_eq hk]

lemma signature_ofRank_positive_eq₂ {k : ℕ} (hk : 2 ≤ k) :
    (Gene.ofRank k .Positive).signature =
    (Gene.ofRank (k - 2) .Positive).signature + (1, 1) := by
  change _ = (Gene.ofRank (k - 1 - 1) .Positive).signature + _
  rw [signature_ofRank_positive_eq (Nat.one_le_of_lt hk),
    signature_ofRank_negative_eq (Nat.le_sub_one_of_lt hk), add_assoc,
    Prod.mk_add_mk 0 1, zero_add, add_zero]

lemma signature_ofRank_eq₂ {k : ℕ} {ε : GeneType} (hk : 2 ≤ k) (hε : ε ≠ .NonPolarized) :
    (Gene.ofRank k ε).signature =
    (Gene.ofRank (k - 2) ε).signature + (1, 1) := by
  match ε, hε with
  | .Positive, _ => exact signature_ofRank_positive_eq₂ hk
  | .Negative, _ =>
    rw [← GeneType.neg_pos_eq_neg, signature_ofRank_swap,
      signature_ofRank_positive_eq₂ hk, Prod.swap_add, ← signature_ofRank_swap]
    rfl

end signature

section prime

/--
The "prime" operation on a single gene $g$, denoted $g'$ in [Djoković 1980, (8.2)].
* If $g$ has rank $> 1$, $g'$ is a gene of the same type with rank $n-1$.
* If $g$ has rank $1$, $g'$ is the zero chromosome.
-/
noncomputable def primeGene (g : Gene) : Chromosome :=
  Gene.ofRank (g.rank - 1) g.type

/--
The "prime" operation extended linearly to all chromosomes: $X' = \sum m_i g_i'$.
This operation corresponds to taking the derivative of the chromosome.
-/
noncomputable def prime : Chromosome →+ Chromosome where
  toFun c := c.sum (fun g m ↦ m • primeGene g)
  map_zero' := sum_zero_index
  map_add' _ _ := sum_add_index' (fun _ ↦ zero_nsmul _)
    fun _ _ _ ↦ add_nsmul ..

lemma prime_ofRank {n : ℕ} {ε : GeneType} :
    (Gene.ofRank n ε).prime = Gene.ofRank (n - 1) ε := by
  by_cases hn : n = 0
  · simp [hn]
  rw [prime, Gene.ofRank_def]
  simp [hn]
  rfl

lemma prime_iterate_ofRank {k n : ℕ} {ε : GeneType} :
    prime^[k] (Gene.ofRank n ε) = Gene.ofRank (n - k) ε := by
  induction hk : k using Nat.strong_induction_on generalizing k
  expose_names
  subst hk
  match k with
  | 0 => rw [Function.iterate_zero, id_eq, tsub_zero]
  | 1 => simp [prime_ofRank]
  | w + 2 =>
    specialize @h (w + 1) (Nat.lt_add_one _) (w + 1) rfl
    change prime^[w + 1 + 1] (Gene.ofRank n ε) = _
    rw [add_comm, Function.iterate_add_apply, Function.iterate_one, h, prime_ofRank]
    ac_rfl

end prime

section order

/--
The dominance relation defined in [Djoković 1980, p. 73].
$X$ dominates $Y$ ($X \ge Y$) if the signature of $X^{(k)}$ is
component-wise greater than or equal to
the signature of $Y^{(k)}$ for all $k \ge 0$.
-/
def Dominates (X Y : Chromosome) : Prop :=
  ∀ k : ℕ, signature (prime^[k] Y) ≤ signature (prime^[k] X)

instance : LE Chromosome where
  le a b := b.Dominates a

/--
The dominance relation forms a preorder on the set of all chromosomes.
-/
instance : Preorder Chromosome where
  le_refl a _ := le_refl _
  lt a b := b.Dominates a ∧ ¬a.Dominates b
  le_trans _ _ _ hab hbc k := le_trans (hab k) (hbc k)

@[simp] lemma le_iff_dominates {X Y : Chromosome} : X ≤ Y ↔
  ∀ k : ℕ, signature (prime^[k] X) ≤ signature (prime^[k] Y) := .rfl

instance : AddRightMono Chromosome where
  elim := by
    dsimp [Covariant, Function.swap_def]
    intros; simpa

instance : AddRightReflectLE Chromosome where
  elim := by
    dsimp [Contravariant]
    intro _ _ _ h; simpa using h

end order

end Chromosome
