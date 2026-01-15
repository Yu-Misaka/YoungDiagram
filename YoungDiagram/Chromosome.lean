import Mathlib
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

@[simp low] lemma Gene.ofRank_def {n : ℕ} {ε : GeneType} :
  Gene.ofRank n ε = if h : n = 0 then 0
    else single ⟨n, ε, Nat.pos_of_ne_zero h⟩ 1 := rfl

namespace Chromosome

section signature

/--
The signature of a chromosome is the weighted sum of the signatures of its constituent genes.
-/
def signature (c : Chromosome) : ℚ × ℚ :=
  c.sum (fun g count ↦ (count : ℚ) • g.Signature)

@[simp] lemma signature_add (X Y : Chromosome) :
    (X + Y).signature = X.signature + Y.signature := by
  dsimp [signature]
  refine Finsupp.sum_add_index' ?_ ?_
  · simp
  intro a _ _
  simp only [Nat.cast_add]
  exact Module.add_smul _ _ a.Signature

@[simp] lemma signature_ofRank_zero {ε : GeneType} :
    (Gene.ofRank 0 ε).signature = 0 := by
  dsimp [signature]

@[simp] lemma signature_ofRank {n : ℕ} {ε : GeneType} :
  (Gene.ofRank n ε).signature =
    if h : n = 0 then 0
    else (⟨n, ε, Nat.pos_of_ne_zero h⟩ : Gene).Signature := by
  dsimp [signature]
  split_ifs
  · rfl
  · simp

@[simp] lemma signature_single {k : ℕ} (hk : 1 ≤ k) {ε : GeneType} :
    signature (single (⟨k, ε, hk⟩ : Gene) 1) =
    (⟨k, ε, hk⟩ : Gene).Signature := by
  simp [signature]

lemma signature_ofRank_nonpol {n : ℕ} :
    (Gene.ofRank n .NonPolarized).signature =
    (Gene.ofRank n .NonPolarized).signature.swap := by
  simp
  split_ifs
  · rfl
  · rw [signature_eq_nonpolarized rfl]; rfl

lemma signature_ofRank_swap {n : ℕ} {ε : GeneType} :
    (Gene.ofRank n ε).signature = (Gene.ofRank n (- ε)).signature.swap := by
  cases ε
  · exact signature_ofRank_nonpol
  · simp
    split_ifs
    · rfl
    · rw [signature_eq_pos rfl, signature_eq_neg rfl]
      simp only
      split_ifs <;> rfl
  · simp
    split_ifs
    · rfl
    · rw [signature_eq_neg rfl, signature_eq_pos rfl]
      simp only
      split_ifs <;> rfl

lemma signature_it_ofRank_pos {k : ℕ} (hk : 1 ≤ k) :
    (Gene.ofRank k .Positive).signature =
    (Gene.ofRank (k - 1) .Negative).signature + (1, 0) := by
  have hk' : k ≠ 0 := by omega
  simp [hk']
  split_ifs with h
  · replace hk : k = 1 := by omega
    simp [signature_eq_pos, hk]
  · simp [signature_eq_pos]
    split_ifs with h1
    · have : ¬ Even (k - 1) := by
        rwa [(Nat.sub_eq_iff_eq_add hk).mp rfl, Nat.even_add_one] at h1
      simp [signature_eq_neg, this, Nat.cast_pred hk]
      linarith
    · have : Even (k - 1) := by
        rwa [(Nat.sub_eq_iff_eq_add hk).mp rfl, Nat.even_add_one, not_not] at h1
      simp [signature_eq_neg, this, Nat.cast_pred hk]
      linarith

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
noncomputable def prime (c : Chromosome) : Chromosome :=
  c.sum (fun g m ↦ m • primeGene g)

@[simp] lemma prime_add (X Y : Chromosome) :
    prime (X + Y) = prime X + prime Y := by
  simp [prime]
  refine Finsupp.sum_add_index' ?_ ?_
  · simp
  intro a b₁ b₂
  exact add_nsmul (primeGene a) b₁ b₂

@[simp] lemma prime_it_add (X Y : Chromosome) (k : ℕ) :
    prime^[k] (X + Y) = prime^[k] X + prime^[k] Y := by
  induction k generalizing X Y with
  | zero => simp
  | succ n hn => simp [hn]

/--
Applying the prime operation $n-1$ times to a gene of rank $n$ results in a gene of rank 1.
-/
lemma single_prime_it_pred_rank (g : Gene) :
    prime^[g.rank - 1] (single g 1) = Gene.ofRank 1 g.type := by
  induction hg : g.rank using Nat.strong_induction_on generalizing g
  expose_names
  by_cases hn : n = 1
  · subst hn; simp [← hg]
  have rank_pos := g.rank_pos
  specialize h (n - 1) (by omega) ⟨g.rank - 1, g.type, by omega⟩
  simp [hg] at h
  rw [show n - 1 = n - 1 - 1 + 1 by omega, Function.iterate_succ_apply]
  simp [prime, primeGene, show g.rank - 1 ≠ 0 by omega]
  simp_rw [hg, h]

/--
Applying the prime operation $n$ times to a gene of rank $n$ results in the zero chromosome.
-/
lemma single_prime_it_rank (g : Gene) :
    prime^[g.rank] (single g 1) = 0 := by
  rw [(Nat.sub_eq_iff_eq_add g.rank_pos).mp rfl, add_comm,
    Function.iterate_add_apply, single_prime_it_pred_rank]
  simp [prime, primeGene]

/--
Applying the prime operation $k$ times to a gene of rank $n$ (where $k \ge n$) results in zero.
-/
lemma single_prime_it_rank_le (g : Gene) {k : ℕ} (hk : g.rank ≤ k) :
    prime^[k] (single g 1) = 0 := by
  rw [(Nat.sub_eq_iff_eq_add hk).mp rfl, Function.iterate_add_apply,
    single_prime_it_rank, Function.iterate_fixed rfl]

end signature

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
Denoted by $\Lambda$ in your code (but $\Pi$ in the paper).
-/
def IsPolarized (c : Chromosome) : Prop :=
  c.filter (·.type ≠ .NonPolarized) = c

/--
Predicate for non-polarized chromosomes (containing only `NonPolarized` genes).
Denoted by $\Pi$ in your code (but $\Lambda$ in the paper).
-/
def IsNonPolarized (c : Chromosome) : Prop :=
  c.filter (·.type = .NonPolarized) = c

/-- A variety is a submonoid of the set of chromosomes. -/
abbrev variety := AddSubmonoid Chromosome

/--
The variety $\Pi$ of polarized chromosomes (following the corrected naming convention).
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

end Chromosome
