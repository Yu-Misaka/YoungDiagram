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

noncomputable abbrev Gene.ofRank' (n : ℕ) (ε : GeneType) : Chromosome :=
  Gene.ofRank n ((- 1) ^ (n - 1) • ε)

lemma Gene.ofRank_def {n : ℕ} {ε : GeneType} :
  Gene.ofRank n ε = if h : n = 0 then 0
    else single ⟨n, ε, Nat.pos_of_ne_zero h⟩ 1 := rfl

@[simp] lemma Gene.ofRank_zero {ε : GeneType} : Gene.ofRank 0 ε = 0 := rfl

namespace Chromosome

section signature

/--
The signature of a chromosome is the weighted sum of the signatures of its constituent genes.
-/
def signature : Chromosome →+ ℚ × ℚ where
  toFun c := c.sum (fun g count ↦ (count : ℚ) • g.signature)
  map_zero' := sum_zero_index
  map_add' X Y := by
    refine Finsupp.sum_add_index' (by simp) fun a _ _ ↦ ?_
    simp only [Nat.cast_add]
    exact Module.add_smul _ _ a.signature

lemma signature_nonneg (c : Chromosome) : 0 ≤ c.signature := by
  dsimp [signature]
  exact sum_nonneg' fun g ↦
    smul_nonneg Rat.natCast_nonneg g.signature_nonneg

@[simp] lemma signature_ofRank_zero {ε : GeneType} :
    (Gene.ofRank 0 ε).signature = 0 := rfl

@[simp] lemma signature_ofRank {n : ℕ} {ε : GeneType} :
  (Gene.ofRank n ε).signature =
    if h : n = 0 then 0
    else (⟨n, ε, Nat.pos_of_ne_zero h⟩ : Gene).signature := by
  dsimp [signature]
  split_ifs
  · rfl
  · simp

@[simp] lemma signature_single {k : ℕ} (hk : 1 ≤ k) {ε : GeneType} :
    signature (single (⟨k, ε, hk⟩ : Gene) 1) =
    (⟨k, ε, hk⟩ : Gene).signature := by
  simp [signature]

lemma signature_ofRank_nonpol {n : ℕ} :
    (Gene.ofRank n .NonPolarized).signature =
    (Gene.ofRank n .NonPolarized).signature.swap := by
  simp
  split_ifs
  · rfl
  · rw [Gene.signature_eq_nonpolarized rfl]; rfl

lemma signature_ofRank_swap {n : ℕ} {ε : GeneType} :
    (Gene.ofRank n (- ε)).signature = (Gene.ofRank n ε).signature.swap := by
  cases ε
  · exact signature_ofRank_nonpol
  · simp
    split_ifs
    · rfl
    · rw [Gene.signature_eq_neg rfl, Gene.signature_eq_pos rfl]
      simp only
      split_ifs <;> rfl
  · simp
    split_ifs
    · rfl
    · rw [Gene.signature_eq_pos rfl, Gene.signature_eq_neg rfl]
      simp only
      split_ifs <;> rfl

lemma signature_it_ofRank_pos {k : ℕ} (hk : 1 ≤ k) :
    (Gene.ofRank k .Positive).signature =
    (Gene.ofRank (k - 1) .Negative).signature + (1, 0) := by
  have hk' : k ≠ 0 := by omega
  simp [hk']
  split_ifs with h
  · replace hk : k = 1 := by omega
    simp [Gene.signature_eq_pos, hk]
  · simp [Gene.signature_eq_pos]
    split_ifs with h1
    · have : ¬ Even (k - 1) := by
        rwa [(Nat.sub_eq_iff_eq_add hk).mp rfl, Nat.even_add_one] at h1
      simp [Gene.signature_eq_neg, this, Nat.cast_pred hk]
      linarith
    · have : Even (k - 1) := by
        rwa [(Nat.sub_eq_iff_eq_add hk).mp rfl, Nat.even_add_one, not_not] at h1
      simp [Gene.signature_eq_neg, this, Nat.cast_pred hk]
      linarith

lemma signature_it_ofRank_neg {k : ℕ} (hk : 1 ≤ k) :
    (Gene.ofRank k .Negative).signature =
    (Gene.ofRank (k - 1) .Positive).signature + (0, 1) := by
  rw [← GeneType.neg_pos_eq_neg, signature_ofRank_swap,
    signature_it_ofRank_pos hk, Prod.swap_add, ← signature_ofRank_swap]
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
  toFun := fun c ↦ c.sum (fun g m ↦ m • primeGene g)
  map_zero' := sum_zero_index
  map_add' X Y := sum_add_index' (by simp)
    fun a _ _ ↦ add_nsmul (primeGene a) _ _

lemma prime_ofRank {n : ℕ} {ε : GeneType} :
    (Gene.ofRank n ε).prime = Gene.ofRank (n - 1) ε := by
  by_cases hn : n = 0
  · simp [hn, Gene.ofRank_def]
  rw [prime, Gene.ofRank_def]
  simp [hn]
  rfl

lemma prime_ofRank_it {k n : ℕ} {ε : GeneType} :
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
def dominates (X Y : Chromosome) : Prop :=
  ∀ k : ℕ, signature (prime^[k] Y) ≤ signature (prime^[k] X)

instance : LE Chromosome where
  le a b := b.dominates a

/--
The dominance relation forms a preorder on the set of all chromosomes.
-/
instance : Preorder Chromosome where
  le_refl a _ := le_refl _
  lt a b := b.dominates a ∧ ¬a.dominates b
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

section variety

/-- The odd part of a chromosome $o(X)$, containing only genes of odd rank. -/
abbrev o (c : Chromosome) : Chromosome := c.filter (Odd  ·.rank)

/-- The even part of a chromosome $e(X)$, containing only genes of even rank. -/
abbrev e (c : Chromosome) : Chromosome := c.filter (Even ·.rank)

/-- Predicate for chromosomes consisting solely of genes with odd rank. -/
def IsOdd (c : Chromosome) : Prop  := o c = c

/-- Predicate for chromosomes consisting solely of genes with even rank. -/
def IsEven (c : Chromosome) : Prop := e c = c

/--
Every chromosome decomposes uniquely into an odd part and an even part: $X = o(X) + e(X)$.
See [Djoković 1980, p. 72].
-/
lemma parityDecomposition (c : Chromosome) : c = o c + e c := by
  simp [o, e]
  conv =>
    enter [2, 2, 1, a]
    rw [← Nat.not_odd_iff_even]
  rw [filter_pos_add_filter_neg]

/--
Predicate for polarized chromosomes (containing no `NonPolarized` genes).
-/
def IsPolarized (c : Chromosome) : Prop :=
  c.filter (·.type ≠ .NonPolarized) = c

/--
Predicate for non-polarized chromosomes (containing only `NonPolarized` genes).
-/
def IsNonPolarized (c : Chromosome) : Prop :=
  c.filter (·.type = .NonPolarized) = c

/-- A variety is a submonoid of the set of chromosomes. -/
abbrev variety := AddSubmonoid Chromosome

/--
The variety $\Pi$ of polarized chromosomes.
[Djoković 1980, p. 72].
-/
def Pi : variety where
  carrier := {c : Chromosome | IsPolarized c}
  add_mem' {a b} ha hb := by
    simp [IsPolarized] at *
    rw [ha, hb]
  zero_mem' := by
    simp [IsPolarized, filter_zero]

/--
The variety $\Lambda$ of non-polarized chromosomes.
[Djoković 1980, p. 72].
-/
def Lambda : variety where
  carrier := {c : Chromosome | IsNonPolarized c}
  add_mem' {a b} ha hb := by
    simp [IsNonPolarized] at *
    rw [ha, hb]
  zero_mem' := by
    simp [IsNonPolarized, filter_zero]

/--
Constructs a mixed variety $(\Phi, \Psi)$ consisting of chromosomes $X$ such that
$e(X) \in \Phi$ and $o(X) \in \Psi$. See [Djoković 1980, p. 72].
-/
def Mix (v : variety × variety) : variety where
  carrier := {c : Chromosome | e c ∈ v.1 ∧ o c ∈ v.2}
  add_mem' {a b} ha hb := by
    simp [o, e] at *
    exact ⟨add_mem ha.1 hb.1, add_mem ha.2 hb.2⟩
  zero_mem' := by
    simp [o, e, filter_zero]

end variety

end Chromosome
