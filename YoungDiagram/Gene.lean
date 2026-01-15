import YoungDiagram.ListAux

inductive GeneType
  | NonPolarized
  | Positive
  | Negative
deriving DecidableEq, Repr

instance : Neg GeneType where
  neg
    | .NonPolarized => .NonPolarized
    | .Positive => .Negative | .Negative => .Positive

instance : SMul ℤ GeneType where
  smul n ε := if n = - 1 then - ε else ε

@[simp] lemma GeneType.neg_pos_eq_neg : - GeneType.Positive = GeneType.Negative := rfl

@[simp] lemma GeneType.neg_neg_eq_pos : - GeneType.Negative = GeneType.Positive := rfl

@[simp] lemma GeneType.neg_one_smul {ε : GeneType} : - 1 • ε = - ε := rfl

@[simp] lemma GeneType.one_smul {ε : GeneType} : (1 : ℤ) • ε = ε := rfl

@[simp] lemma GeneType.neg_one_pow_smul {n : ℕ} {ε : GeneType} :
    (- 1) ^ n • ε = if Even n then ε else - ε := by
  split_ifs with h
  · simp [h]
  · simp [Nat.not_even_iff_odd.1 h]

/--
A gene is an isomorphism class of strings, defined by its rank (size) and type.
-/
structure Gene where
  /-- The number of vertices in the string representation of the gene. -/
  rank : ℕ
  /-- The polarity of the gene. -/
  type : GeneType
  /-- The rank of a gene is strictly positive. -/
  rank_pos : 1 ≤ rank := by decide
deriving DecidableEq, Repr

def List.toGene {l : List Bool} (hl : l ≠ [] := by decide)
    (_ : l.isAlt hl := by decide) : Gene :=
  ⟨l.length, if l.getLast hl = true then .Positive else .Negative, List.length_pos_iff.2 hl⟩

def Gene.toList {g : Gene} (_ : g.type ≠ .NonPolarized := by decide) : List Bool :=
  List.iterate not
    (match g.type with | .Positive => true | .Negative => false | .NonPolarized => by tauto)
    g.rank |>.reverse

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

lemma signature_eq_nonpolarized {g : Gene} (hg : g.type = .NonPolarized) :
    g.Signature = ((g.rank : ℚ) / 2, (g.rank : ℚ) / 2) := by
  simp [Gene.Signature]
  split <;> simp_all only [reduceCtorEq]

lemma signature_eq_pos {g : Gene} (hg : g.type = .Positive) :
  g.Signature =
    if Even g.rank then ((g.rank : ℚ) / 2, (g.rank : ℚ) / 2)
    else (((g.rank : ℚ) + 1) / 2, ((g.rank : ℚ) - 1) / 2) := by
  simp [Gene.Signature]
  split <;> simp_all only [reduceCtorEq]
  next hg =>
    simp [Gene.toList, hg]
    exact signature_eq_pos_aux

lemma signature_eq_neg {g : Gene} (hg : g.type = .Negative) :
  g.Signature =
    if Even g.rank then ((g.rank : ℚ) / 2, (g.rank : ℚ) / 2)
    else (((g.rank : ℚ) - 1) / 2, ((g.rank : ℚ) + 1) / 2) := by
  simp [Gene.Signature]
  split <;> simp_all only [reduceCtorEq]
  next hg =>
    simp [Gene.toList, hg]
    exact signature_eq_neg_aux
