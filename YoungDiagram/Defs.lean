import Mathlib

/-!
# Closures of Conjugacy Classes: Chromosomes

This file formalizes the combinatorial structures called
"Chromosomes" introduced by
Dragomir Z. Djoković in the paper Closures of conjugacy
classes in classical real linear Lie groups (1980).

These structures are used to classify the closures of
nilpotent orbits in real classical Lie algebras.
A "chromosome" is a linear combination of "genes", where
each gene represents a signed (polarized)
or unsigned (non-polarized) Young diagram row.

## Main definitions

* `Gene`: A fundamental unit characterized by a rank ($n \ge 1$)
and a type (polarized or non-polarized).
* `Chromosome`: A formal linear combination of genes (formalized as
`Finsupp Gene ℕ`).
* `prime`: The operation $X \mapsto X'$ on chromosomes,
which decreases the rank of constituent genes.
* `dominates`: The dominance partial order $\le$ defined by
comparing the signatures of iterated prime operations.
* `Pi`, `Lambda`, `Mix`: Specific submonoids ("varieties") of
chromosomes used in the classification.

## References

* [Djoković, 1980]: Dragomir Z. Djoković,
Closures of conjugacy classes in classical real linear Lie groups.
-/

open Finsupp

/--
The polarity type of a gene as defined in [Djoković 1980, p. 71].
* `NonPolarized`: Corresponds to the gene $g(n)$.
* `Positive`: Corresponds to the gene $g^+(n)$.
* `Negative`: Corresponds to the gene $g^-(n)$.
-/
inductive GeneType
  | NonPolarized
  | Positive
  | Negative
deriving DecidableEq, Repr

/--
A gene is an isomorphism class of strings, defined by its rank (size) and type.
See [Djoković 1980, p. 72]. The rank must be at least 1.
-/
structure Gene where
  /-- The number of vertices in the string representation of the gene. -/
  rank : ℕ
  /-- The polarity of the gene. -/
  type : GeneType
  /-- The rank of a gene is strictly positive. -/
  rank_pos : 1 ≤ rank := by decide
deriving DecidableEq, Repr

section polarized

/--
Predicate checking if a list of booleans is alternating
(e.g., `[true, false, true]`).
Represents the alternating signs on the vertices of a polarized string.
-/
abbrev List.isAlt {l : List Bool} (hl : l ≠ [] := by decide) : Prop :=
  l = List.iterate not (l.head hl) l.length

/--
Constructs a `Gene` from an alternating boolean list.
According to [Djoković 1980, p. 71], the polarity of a gene ($g^+$ or $g^-$) is determined
by the sign of the **tail** (the last vertex) of the string.
* `true` corresponds to `+`
* `false` corresponds to `-`
-/
def List.toGene {l : List Bool} (hl : l ≠ [] := by decide)
    (_ : l.isAlt hl := by decide) : Gene :=
  ⟨l.length, if l.getLast hl = true then .Positive else .Negative, List.length_pos_iff.2 hl⟩

/--
Converts a `Gene` back into an alternating list of booleans.
The list is constructed such that its **tail** matches the polarity of the gene, preserving the
isomorphism class defined in the paper.
-/
def Gene.toList {g : Gene} (_ : g.type ≠ .NonPolarized := by decide) : List Bool :=
  List.iterate not
    (match g.type with | .Positive => true | .Negative => false | .NonPolarized => by tauto)
    g.rank |>.reverse

/--
Computes the signature $(r^+, r^-)$ of a gene by generating its list representation
and counting the positive (`true`) and negative (`false`) entries.
See [Djoković 1980, (8.1)].
-/
def Gene.Signature (g : Gene) : ℚ × ℚ :=
  match hg : g.type with
  | .NonPolarized => (g.rank / 2, g.rank / 2)
  | .Positive =>
    let l := g.toList <|
      (congrArg (fun _a ↦ _a ≠ .NonPolarized) hg).mpr
      (not_eq_of_beq_eq_false rfl)
    (l.count true, l.count false)
  | .Negative =>
    let l := g.toList <|
      (congrArg (fun _a ↦ _a ≠ .NonPolarized) hg).mpr
      (not_eq_of_beq_eq_false rfl)
    (l.count true, l.count false)

/--
Computes the signature of a gene using the arithmetic formulas derived from
the alternating structure.
For a polarized gene of rank $n$:
* If $n$ is even, $(n/2, n/2)$.
* If $n$ is odd, $((n+1)/2, (n-1)/2)$ for Positive, symmetric for Negative.
-/
def geneSignature (g : Gene) : ℚ × ℚ :=
  let n : ℚ := g.rank
  match g.type with
  | .NonPolarized => (n / 2, n / 2)
  | .Positive =>
      if g.rank % 2 == 0 then (n / 2, n / 2)
      else ((n + 1) / 2, (n - 1) / 2)
  | .Negative =>
      if g.rank % 2 == 0 then (n / 2, n / 2)
      else ((n - 1) / 2, (n + 1) / 2)

end polarized

/--
A chromosome is a non-negative integral linear combination of genes.
It forms a free commutative monoid on the set of genes.
Formalized as `Finsupp` (finite support functions) from `Gene` to `ℕ`.
-/
abbrev Chromosome := Gene →₀ ℕ

namespace Chromosome

/--
The signature of a chromosome is the weighted sum of the signatures of its constituent genes.
-/
def signature (c : Chromosome) : ℚ × ℚ :=
  c.sum (fun g count ↦ (count : ℚ) • g.Signature)

/--
The "prime" operation on a single gene $g$, denoted $g'$ in [Djoković 1980, (8.2)].
* If $g$ has rank $> 1$, $g'$ is a gene of the same type with rank $n-1$.
* If $g$ has rank $1$, $g'$ is the zero chromosome.
-/
noncomputable def primeGene (g : Gene) : Chromosome :=
  if h : 1 < g.rank then
    single ⟨g.rank - 1, g.type, Nat.le_sub_one_of_lt h⟩ 1
  else 0

/--
The "prime" operation extended linearly to all chromosomes: $X' = \sum m_i g_i'$.
This operation corresponds to taking the derivative of the chromosome.
-/
noncomputable def prime (c : Chromosome) : Chromosome :=
  c.sum (fun g m ↦ m • primeGene g)

/--
Applying the prime operation $n-1$ times to a gene of rank $n$ results in a gene of rank 1.
-/
lemma single_prime_it_pred_rank (g : Gene) :
    prime^[g.rank - 1] (single g 1) = single ⟨1, g.type, NeZero.one_le⟩ 1 := by
  induction hg : g.rank using Nat.strong_induction_on generalizing g
  expose_names
  by_cases hn : n = 1
  · subst hn; simp [← hg]
  have rank_pos := g.rank_pos
  specialize h (n - 1) (by omega) ⟨g.rank - 1, g.type, by omega⟩
  simp [hg] at h
  rw [show n - 1 = n - 1 - 1 + 1 by omega, Function.iterate_succ_apply]
  simp [prime, primeGene, show 1 < g.rank by omega]
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

/--
The dominance relation defined in [Djoković 1980, p. 73].
$X$ dominates $Y$ ($X \ge Y$) if the signature of $X^{(k)}$ is
component-wise greater than or equal to
the signature of $Y^{(k)}$ for all $k \ge 0$.
-/
def dominates (X Y : Chromosome) : Prop :=
  ∀ k : ℕ, signature (prime^[k] Y) ≤ signature (prime^[k] X)

/--
The dominance relation forms a preorder on the set of all chromosomes.
Note: It is a partial order only when restricted to specific varieties.
-/
instance : Preorder Chromosome where
  le a b := b.dominates a
  le_refl a _ := le_refl _
  lt a b := b.dominates a ∧ ¬a.dominates b
  le_trans _ _ _ hab hbc k := le_trans (hab k) (hbc k)

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
