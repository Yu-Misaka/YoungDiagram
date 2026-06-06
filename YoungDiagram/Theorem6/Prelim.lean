import YoungDiagram.Sigma
import YoungDiagram.Lifting.Pi

open Variety hiding prime prime_def
open Chromosome

abbrev nPi (n : ℕ) := {X : Pi // X.1.rank = n}

lemma ofRankAlt_eq_single_of_type_eq_altType {g : Gene} {ε : GeneType}
    (h : g.type = Sigma.altType g.rank ε) :
    Gene.ofRankAlt g.rank ε = Finsupp.single g 1 := by
  rw [Gene.ofRankAlt_eq_gene g.rank_pos]
  congr 1
  exact Gene.ext rfl h.symm

lemma gene_type_eq_negOnePow_positive_of_ne_negOnePow_negative {g : Gene}
    (hpol : g.type ≠ .NonPolarized)
    (hne : ¬ g.type = Int.negOnePow (g.rank - 1) • GeneType.Negative) :
    g.type = Int.negOnePow (g.rank - 1) • GeneType.Positive := by
  by_cases heven : Even ((g.rank : ℤ) - 1)
  · have hne' : g.type ≠ .Negative := by
      simpa [GeneType.negOnePow_smul, GeneType.neg_negative, heven] using hne
    have hpos : g.type = .Positive := by
      cases ht : g.type with
      | Positive => rfl
      | Negative => exact absurd ht hne'
      | NonPolarized => exact absurd ht hpol
    simpa [GeneType.negOnePow_smul, GeneType.neg_positive, heven] using hpos
  · have hne' : g.type ≠ .Positive := by
      simpa [GeneType.negOnePow_smul, GeneType.neg_negative, heven] using hne
    have hneg : g.type = .Negative := by
      cases ht : g.type with
      | Positive => exact absurd ht hne'
      | Negative => rfl
      | NonPolarized => exact absurd ht hpol
    simpa [GeneType.negOnePow_smul, GeneType.neg_positive, heven] using hneg

lemma gene_type_eq_negOnePow_negative_of_ne_negOnePow_positive {g : Gene}
    (hpol : g.type ≠ .NonPolarized)
    (hne : ¬ g.type = Int.negOnePow (g.rank - 1) • GeneType.Positive) :
    g.type = Int.negOnePow (g.rank - 1) • GeneType.Negative := by
  by_cases heven : Even ((g.rank : ℤ) - 1)
  · have hne' : g.type ≠ .Positive := by
      simpa [GeneType.negOnePow_smul, GeneType.neg_positive, heven] using hne
    have hneg : g.type = .Negative := by
      cases ht : g.type with
      | Positive => exact absurd ht hne'
      | Negative => rfl
      | NonPolarized => exact absurd ht hpol
    simpa [GeneType.negOnePow_smul, GeneType.neg_negative, heven] using hneg
  · have hne' : g.type ≠ .Negative := by
      simpa [GeneType.negOnePow_smul, GeneType.neg_positive, heven] using hne
    have hpos : g.type = .Positive := by
      cases ht : g.type with
      | Positive => rfl
      | Negative => exact absurd ht hne'
      | NonPolarized => exact absurd ht hpol
    simpa [GeneType.negOnePow_smul, GeneType.neg_negative, heven] using hpos

lemma gene_type_eq_negative_of_even_of_ne_negOnePow_negative {g : Gene} (heven : Even g.rank)
    (hpol : g.type ≠ .NonPolarized)
    (hne : ¬ g.type = Int.negOnePow (g.rank - 1) • GeneType.Negative) : g.type = .Negative := by
  have hfamily := gene_type_eq_negOnePow_positive_of_ne_negOnePow_negative hpol hne
  have hodd : ¬ Even ((g.rank : ℤ) - 1) := by simp [heven]
  simpa [GeneType.negOnePow_smul, GeneType.neg_positive, hodd] using hfamily

lemma gene_type_eq_positive_of_odd_of_ne_negOnePow_negative {g : Gene} (hodd : Odd g.rank)
    (hpol : g.type ≠ .NonPolarized)
    (hne : ¬ g.type = Int.negOnePow (g.rank - 1) • GeneType.Negative) : g.type = .Positive := by
  have hfamily := gene_type_eq_negOnePow_positive_of_ne_negOnePow_negative hpol hne
  have h_even : Even ((g.rank : ℤ) - 1) := by simp [hodd]
  simpa [GeneType.negOnePow_smul, GeneType.neg_positive, h_even] using hfamily

lemma theorem6_sigma_eq_add_of_sub_eq {p q δ : ℚ × ℚ} (h : p - q = δ) : p = q + δ := by
  rw [← h]; abel

lemma theorem6_sigma_fst_add_one_le_of_lt {X Y : Chromosome}
    (hX : X ∈ Variety.Pi) (hY : Y ∈ Variety.Pi) (i : ℕ)
    (h : (Sigma.sigma X i).1 < (Sigma.sigma Y i).1) :
    (Sigma.sigma X i).1 + 1 ≤ (Sigma.sigma Y i).1 := by
  obtain ⟨nX, hnX⟩ := Sigma.sigma_isNat X i hX
  obtain ⟨nY, hnY⟩ := Sigma.sigma_isNat Y i hY
  rw [hnX, hnY] at h ⊢
  simp only at h ⊢
  exact_mod_cast Nat.add_one_le_iff.mpr (by exact_mod_cast h)

lemma theorem6_sigma_snd_add_one_le_of_lt {X Y : Chromosome}
    (hX : X ∈ Variety.Pi) (hY : Y ∈ Variety.Pi) (i : ℕ)
    (h : (Sigma.sigma X i).2 < (Sigma.sigma Y i).2) :
    (Sigma.sigma X i).2 + 1 ≤ (Sigma.sigma Y i).2 := by
  obtain ⟨nX, hnX⟩ := Sigma.sigma_isNat X i hX
  obtain ⟨nY, hnY⟩ := Sigma.sigma_isNat Y i hY
  rw [hnX, hnY] at h ⊢
  simp only at h ⊢
  exact_mod_cast Nat.add_one_le_iff.mpr (by exact_mod_cast h)

/-! ## Case 1: X and Y share a gene -/

/-- Remove a shared gene from both X and Y, apply IH, then reattach. -/
lemma exists_mutation_le_shared_gene (m : ℕ)
    (ih : ∀ k, k < m + 2 → ∀ X Y : nPi k, X.1 < Y.1 →
      ∃ Z : Pi, Pi.Step X.1 Z ∧ Z ≤ Y.1)
    (X Y : nPi (m + 2))
    (hXY : X.1 < Y.1)
    (hcommon : ∃ g : Gene, 0 < X.1.val g ∧ 0 < Y.1.val g) :
    ∃ Z : Pi, Pi.Step X.1 Z ∧ Z ≤ Y.1 := by
  obtain ⟨g, hgX, hgY⟩ := hcommon
  have hg_pol : g.type ≠ .NonPolarized :=
    IsPolarized_def'.mp (mem_Pi_iff.mp X.1.2) g
      (Finsupp.mem_support_iff.mpr (Nat.pos_iff_ne_zero.mp hgX))
  have hg1_Pi : Finsupp.single g 1 ∈ Pi :=
    mem_Pi_iff.mpr <| (IsPolarized_single Nat.one_ne_zero).2 hg_pol
  let X'v : Chromosome := X.1.val - Finsupp.single g 1
  let Y'v : Chromosome := Y.1.val - Finsupp.single g 1
  have hX'Pi : X'v ∈ Pi := sub_mem_Pi _ X.1.2
  have hY'Pi : Y'v ∈ Pi := sub_mem_Pi _ Y.1.2
  have hlt' : (⟨X'v, hX'Pi⟩ : Pi) < ⟨Y'v, hY'Pi⟩ :=
    sub_single_lt_sub_single hgX hgY hXY
  have hX'rank : X'v.rank = m + 2 - g.rank := by
    rw [rank_sub_single hgX, X.2]
  have hY'rank : Y'v.rank = m + 2 - g.rank := by
    rw [rank_sub_single hgY, Y.2]
  obtain ⟨Z', hmut', hle'⟩ :=
    ih (m + 2 - g.rank) (Nat.sub_lt (by omega) g.rank_pos)
      ⟨⟨X'v, hX'Pi⟩, hX'rank⟩ ⟨⟨Y'v, hY'Pi⟩, hY'rank⟩ hlt'
  refine ⟨⟨Z'.val + Finsupp.single g 1,
      mem_Pi_iff.mpr (IsPolarized_iff_add.mpr
        ⟨mem_Pi_iff.mp Z'.2, mem_Pi_iff.mp hg1_Pi⟩)⟩, ?_, ?_⟩
  · convert Pi.Step.add_right ⟨Finsupp.single g 1, hg1_Pi⟩ hmut' using 1
    · exact Subtype.ext (sub_single_add_single_eq hgX).symm
    · rfl
  · change Z'.val + Finsupp.single g 1 ≤ Y.1.val
    rw [← sub_single_add_single_eq hgY, le_iff_dominates]
    intro k
    have h := (le_iff_dominates.mp hle') k
    simp only [iterate_map_add, map_add, add_le_add_iff_right]
    exact h

/-! ## Sub-case 2a: disjoint supports, some sigma column agrees -/

/-- Drop to prime^[k] level where sigma agrees, apply IH, then lift back. -/
lemma exists_mutation_le_disjoint_sigma_eq (m : ℕ)
    (ih : ∀ k, k < m + 2 → ∀ X Y : nPi k, X.1 < Y.1 →
      ∃ Z : Pi, Pi.Step X.1 Z ∧ Z ≤ Y.1)
    (X : Pi) (Y : nPi (m + 2))
    (hXY : X < Y.1)
    (hcommon : ¬∃ g : Gene, 0 < X.val g ∧ 0 < Y.1.val g)
    (hsigeq : ∃ k : ℕ, 0 < k ∧ prime^[k] Y.1.val ≠ 0 ∧
      Sigma.sigma X k = Sigma.sigma Y.1 k) :
    ∃ Z : Pi, Pi.Step X Z ∧ Z ≤ Y.1 := by
  push Not at hcommon
  obtain ⟨k, hkpos, hYkne, hk⟩ := hsigeq
  have hle_k : prime^[k] X.val ≤ prime^[k] Y.1.val := by
    intro j
    simp_rw [← Function.iterate_add_apply]
    exact le_iff_dominates.mp hXY.le (j + k)
  have hdisj_k : ∀ (g' : Gene), 0 < (prime^[k] X.val) g' →
      (prime^[k] Y.1.val) g' = 0 := by
    intro g' hg'
    rw [prime_iterate_coeff k X.val g'] at hg'
    rw [prime_iterate_coeff k Y.1.val g']
    exact Nat.eq_zero_of_le_zero (hcommon ⟨g'.rank + k, g'.type, by linarith [g'.rank_pos]⟩ hg')
  let Xk : Pi := ⟨prime^[k] X.val, prime_mem_Pi_iterate X.2⟩
  let Yk : Pi := ⟨prime^[k] Y.1.val, prime_mem_Pi_iterate Y.1.2⟩
  have hXk_Yk_rank : Xk.val.rank = Yk.val.rank := by
    have h := congr_arg (fun p : ℚ × ℚ => p.1 + p.2) hk
    simp only [Sigma.sigma, signature_sum_eq_rank] at h
    exact_mod_cast h
  have hXk_rank_lt : Xk.val.rank < m + 2 := by
    rw [hXk_Yk_rank, ← Y.2]
    exact prime_iterate_rank_lt_of_ne_zero hkpos hYkne
  have hlt_k : Xk < Yk := by
    change Yk.val.Dominates Xk.val ∧ ¬Xk.val.Dominates Yk.val
    refine ⟨le_iff_dominates.mp hle_k, fun hcontra => ?_⟩
    have hXkYk_eq : Xk.val = Yk.val :=
      Subtype.val_inj.2 (le_antisymm hle_k hcontra)
    obtain ⟨g', hg'⟩ : ∃ g', 0 < Yk.val g' := by
      obtain ⟨g', hg'mem⟩ := Finsupp.support_nonempty_iff.mpr hYkne
      exact ⟨g', Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hg'mem)⟩
    have hXkg' : 0 < Xk.val g' := by rwa [hXkYk_eq]
    have hYkg'zero := hdisj_k g' hXkg'
    simp only [Yk] at hg'
    omega
  obtain ⟨U, hU_step, hU_le⟩ : ∃ U : Pi, Pi.Step Xk U ∧ U ≤ Yk :=
    ih Xk.val.rank hXk_rank_lt ⟨Xk, rfl⟩ ⟨Yk, hXk_Yk_rank.symm⟩ hlt_k
  obtain ⟨Z, hZ, hZ_step, hZ_prime, hZ_sig⟩ :=
    Pi.mutation_lifting X.2 U.2 hU_step
  refine ⟨⟨Z, hZ⟩, hZ_step, ?_⟩
  change Z ≤ Y.1.val
  rw [le_iff_dominates]
  intro j
  by_cases hjk : j ≤ k
  · rw [← hZ_sig j hjk]
    exact le_iff_dominates.mp hXY.le j
  · push Not at hjk
    have hj_eq : j = (j - k) + k := (Nat.sub_add_cancel hjk.le).symm
    conv_lhs => rw [hj_eq, Function.iterate_add_apply, hZ_prime]
    calc signature (prime^[j - k] U.val)
        ≤ signature (prime^[j - k] Yk.val) := le_iff_dominates.mp hU_le (j - k)
      _ = signature (prime^[j] Y.1.val) := by
          simp only [Yk, ← Function.iterate_add_apply, Nat.sub_add_cancel hjk.le]

/-! ## Sub-case 2b: disjoint supports, X contains g⁺(k) + g⁻(k) -/

private lemma prime_iterate_no_gene_of_rank {Y : Chromosome} {r : ℕ}
    (hY_no_gene : ∀ g : Gene, g.rank = r → Y g = 0)
    (j : ℕ) (hj : j ≤ r - 1) (h : Gene) (hh : h.rank = r - j) :
    (prime^[j] Y) h = 0 := by
  induction j generalizing h with
  | zero => exact hY_no_gene h (by omega)
  | succ j ihj =>
    simp only [Function.iterate_succ', Function.comp,
      prime_def, Finsupp.sum_apply, Finsupp.smul_apply, smul_eq_mul]
    simp only [Finsupp.sum]
    apply Finset.sum_eq_zero
    intro g hg
    have hg_ne : (prime^[j] Y) g ≠ 0 := Finsupp.mem_support_iff.mp hg
    by_cases hrk : g.rank - 1 = h.rank
    · exfalso
      have _ := g.rank_pos
      exact hg_ne (ihj (by omega) g (by omega))
    · simp only [Nat.mul_eq_zero]
      right
      simp only [primeGene, Gene.ofRank_def]
      split_ifs with h0
      · rfl
      · rw [Finsupp.single_apply, if_neg]
        intro heq
        exact hrk (congrArg Gene.rank heq)

private lemma prime_ne_zero_of_Y_no_gene {Y : Chromosome} {r : ℕ} (hr : 1 ≤ r)
    (hY_no_gene : ∀ g : Gene, g.rank = r → Y g = 0)
    (hYr_minus_one : prime^[r - 1] Y ≠ 0) : prime^[r] Y ≠ 0 := by
  have hr_eq : r = 1 + (r - 1) := by omega
  rw [hr_eq, Function.iterate_add_apply, Function.iterate_one]
  apply prime_ne_zero_of_rank_ge_two hYr_minus_one
  intro h hmem
  rw [Finsupp.mem_support_iff] at hmem
  by_contra! hlt
  have hh1 : h.rank = 1 := le_antisymm (by omega) h.rank_pos
  exact hmem (prime_iterate_no_gene_of_rank hY_no_gene (r - 1) (by omega) h (by omega))

private lemma Y_no_gene_of_rank {X Y : Chromosome} (hYPi : Y ∈ Pi)
    (hcommon : ∀ g, 0 < X g → Y g ≤ 0)
    (gpos gneg : Gene) (hrank : gpos.rank = gneg.rank)
    (hgpos : gpos.type = .Positive) (hgneg : gneg.type = .Negative)
    (hXgpos : 0 < X gpos) (hXgneg : 0 < X gneg)
    (g : Gene) (hgr : g.rank = gpos.rank) : Y g = 0 := by
  by_contra hne
  have hg_pol : g.type ≠ .NonPolarized :=
    IsPolarized_def'.mp (mem_Pi_iff.mp hYPi) g (Finsupp.mem_support_iff.mpr hne)
  cases ht : g.type with
  | NonPolarized => exact hg_pol ht
  | Positive =>
    have hgeq : g = gpos := Gene.ext hgr (ht.trans hgpos.symm)
    subst hgeq
    have h := hcommon g hXgpos
    omega
  | Negative =>
    have hgeq : g = gneg := Gene.ext (hgr.trans hrank) (ht.trans hgneg.symm)
    subst hgeq
    have h := hcommon g hXgneg
    omega

private lemma one_le_signature_fst_of_contains_positive {X : Chromosome} {gpos : Gene}
    (hgpos : gpos.type = .Positive) (hXgpos : 0 < X gpos) :
    1 ≤ (signature (prime^[gpos.rank - 1] X)).1 := by
  let r := gpos.rank
  have hr : 1 ≤ r := gpos.rank_pos
  have hgpos_single : Gene.ofRank r .Positive = (Finsupp.single gpos 1 : Chromosome) := by
    have h := Gene.ofRank_eq_gene (g := gpos)
    rw [hgpos] at h
    exact h
  have hprime_gpos : prime^[r - 1] (Finsupp.single gpos 1 : Chromosome) =
      Gene.ofRank 1 .Positive := by
    rw [← hgpos_single, prime_iterate_ofRank, Nat.sub_sub_self hr]
  have hXeq : X = Finsupp.single gpos 1 + (X - Finsupp.single gpos 1) := by
    rw [add_comm, sub_single_add_single_eq hXgpos]
  calc (1 : ℚ)
      = (signature (Gene.ofRank 1 .Positive : Chromosome)).1 := by
        simp [signature_ofRank_one_positive]
    _ = (signature (prime^[r - 1] (Finsupp.single gpos 1 : Chromosome))).1 := by
        rw [hprime_gpos]
    _ ≤ (signature (prime^[r - 1] X)).1 := by
        conv_rhs => rw [hXeq]
        rw [iterate_map_add, map_add]
        exact le_add_of_nonneg_right (signature_nonneg _).1

private lemma X_eq_X1_add_rest {X : Chromosome} {gpos gneg : Gene}
    (hXgpos : 0 < X gpos) (hXgneg : 0 < X gneg) (hne : gpos ≠ gneg) :
    Finsupp.single gpos 1 + Finsupp.single gneg 1 +
      (X - Finsupp.single gpos 1 - Finsupp.single gneg 1) = X := by
  ext g'
  simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
  by_cases h1 : gpos = g'
  · subst h1
    have h2 : gneg ≠ gpos := hne.symm
    simp [if_neg h2]
    omega
  · by_cases h2 : gneg = g'
    · subst h2
      simp [if_neg hne]
      omega
    · simp [if_neg h1, if_neg h2]

private lemma prod_lt_or_lt_of_le_ne {p q : ℚ × ℚ} (hle : p ≤ q) (hne : p ≠ q) :
    p.1 < q.1 ∨ p.2 < q.2 := by
  rcases lt_or_eq_of_le hle.1 with hlt | hfst
  · exact Or.inl hlt
  rcases lt_or_eq_of_le hle.2 with hlt | hsnd
  · exact Or.inr hlt
  exact (hne (Prod.ext hfst hsnd)).elim

private lemma cast_add_one_le_of_lt {m n : ℕ} (h : (m : ℚ) < n) :
    (m : ℚ) + 1 ≤ n := by
  have : m < n := by exact_mod_cast h
  exact_mod_cast this

private lemma signature_type1_eq_before {ε : GeneType} (hε : ε ≠ .NonPolarized)
    {r j : ℕ} (hr : 1 ≤ r) (hj : j < r) :
    signature (prime^[j] (Pi.Y1 hε (le_refl r) hr).val) =
      signature (prime^[j] (Pi.X1 hε (le_refl r) hr).val) := by
  rw [Pi.Y1_eq, Pi.X1_eq]
  have key := mutation_type1_iterate_signature_eq hε le_rfl le_rfl j (r - 1) (by omega)
  have hsucc_pred : 1 + (r - 1) = r := by omega
  simp only [hsucc_pred] at key
  exact key.symm

private lemma signature_type1_source_self_eq_zero {ε : GeneType}
    (hε : ε ≠ .NonPolarized) {r : ℕ} (hr : 1 ≤ r) :
    signature (prime^[r] (Pi.X1 hε (le_refl r) hr).val) = 0 := by
  rw [Pi.X1_eq]
  simp only [iterate_map_add, prime_iterate_ofRank,
    Nat.sub_self, Gene.ofRank_zero, map_zero, add_zero]

private lemma signature_type1_target_self_eq {ε : GeneType}
    (hε : ε ≠ .NonPolarized) {r : ℕ} (hr : 1 ≤ r) :
    signature (prime^[r] (Pi.Y1 hε (le_refl r) hr).val) =
      signature (Gene.ofRank 1 ε : Chromosome) := by
  have hpred_sub : r - 1 - r = 0 := by omega
  have hsucc_sub : r + 1 - r = 1 := by omega
  rw [Pi.Y1_eq]
  simp only [iterate_map_add, prime_iterate_ofRank,
    hpred_sub, hsucc_sub, Gene.ofRank_zero, zero_add]

private lemma signature_type1_target_self_positive
    (hε : GeneType.Positive ≠ .NonPolarized) {r : ℕ} (hr : 1 ≤ r) :
    signature (prime^[r] (Pi.Y1 hε (le_refl r) hr).val) = (1, 0) := by
  simpa [signature_ofRank_one_positive] using signature_type1_target_self_eq hε hr

private lemma signature_type1_target_self_negative
    (hε : GeneType.Negative ≠ .NonPolarized) {r : ℕ} (hr : 1 ≤ r) :
    signature (prime^[r] (Pi.Y1 hε (le_refl r) hr).val) = (0, 1) := by
  simpa [signature_ofRank_one_negative] using signature_type1_target_self_eq hε hr

private lemma signature_type1_source_after_eq_zero {ε : GeneType}
    (hε : ε ≠ .NonPolarized) {r j : ℕ} (hr : 1 ≤ r) (hj : r < j) :
    signature (prime^[j] (Pi.X1 hε (le_refl r) hr).val) = 0 := by
  have hr_sub : r - j = 0 := by omega
  rw [Pi.X1_eq]
  simp only [iterate_map_add, prime_iterate_ofRank,
    hr_sub, Gene.ofRank_zero, map_zero, add_zero]

private lemma signature_type1_target_after_eq_zero {ε : GeneType}
    (hε : ε ≠ .NonPolarized) {r j : ℕ} (hr : 1 ≤ r) (hj : r < j) :
    signature (prime^[j] (Pi.Y1 hε (le_refl r) hr).val) = 0 := by
  have hpred_sub : r - 1 - j = 0 := by omega
  have hsucc_sub : r + 1 - j = 0 := by omega
  rw [Pi.Y1_eq]
  simp only [iterate_map_add, prime_iterate_ofRank,
    hpred_sub, hsucc_sub, Gene.ofRank_zero, map_zero, add_zero]

/-- Construct a type-1 mutation directly from a positive-negative gene pair. -/
lemma exists_mutation_le_disjoint_pair
    (X Y : Pi)
    (hXY : X < Y)
    (hcommon : ¬∃ g : Gene, 0 < X.val g ∧ 0 < Y.val g)
    (hsigeq : ¬∃ k : ℕ, 0 < k ∧ prime^[k] Y.val ≠ 0 ∧
      Sigma.sigma X k = Sigma.sigma Y k)
    (hXpn : ∃ (g h : Gene), g.rank = h.rank ∧
      g.type = .Positive ∧ h.type = .Negative ∧
      0 < X.val g ∧ 0 < X.val h) :
    ∃ Z : Pi, Pi.Step X Z ∧ Z ≤ Y := by
  push Not at hcommon hsigeq
  obtain ⟨gpos, gneg, hrank, hgpos, hgneg, hXgpos, hXgneg⟩ := hXpn
  let r := gpos.rank
  have hr : 1 ≤ r := gpos.rank_pos
  have hY_no_gene : ∀ (g : Gene), g.rank = r → Y.val g = 0 :=
    Y_no_gene_of_rank Y.2 hcommon gpos gneg hrank hgpos hgneg hXgpos hXgneg
  have h1a : 1 ≤ (signature (prime^[r - 1] X.val)).1 :=
    one_le_signature_fst_of_contains_positive hgpos hXgpos
  have h1c : prime^[r - 1] Y.val ≠ 0 := by
    intro heq
    have h1b : 1 ≤ (signature (prime^[r - 1] Y.val)).1 :=
      le_trans h1a ((le_iff_dominates.mp hXY.le (r - 1)).1)
    have : (signature (prime^[r - 1] Y.val)).1 = 0 := by simp [heq]
    linarith
  have hYr : prime^[r] Y.val ≠ 0 := prime_ne_zero_of_Y_no_gene hr hY_no_gene h1c
  have hsig_ne : Sigma.sigma X r ≠ Sigma.sigma Y r :=
    hsigeq r gpos.rank_pos hYr
  have hle_r : Sigma.sigma X r ≤ Sigma.sigma Y r := le_iff_dominates.mp hXY.le r
  have hsig_lt : (Sigma.sigma X r).1 < (Sigma.sigma Y r).1 ∨
                 (Sigma.sigma X r).2 < (Sigma.sigma Y r).2 :=
    prod_lt_or_lt_of_le_ne hle_r hsig_ne
  let restval := X.val - Finsupp.single gpos 1 - Finsupp.single gneg 1
  have hne : gpos ≠ gneg := by
    intro h
    apply absurd (congrArg Gene.type h)
    rw [hgpos, hgneg]
    decide
  have hgpos_eq : Gene.ofRank r .Positive = (Finsupp.single gpos 1 : Chromosome) := by
    rw [← hgpos]
    exact Gene.ofRank_eq_gene
  have hgneg_eq : Gene.ofRank r .Negative = (Finsupp.single gneg 1 : Chromosome) := by
    have h := Gene.ofRank_eq_gene (g := gneg)
    rw [hgneg] at h
    rwa [← hrank] at h
  have rest_mem : restval ∈ Pi := by
    rw [mem_Pi_iff, IsPolarized_def']
    intro g hg
    apply IsPolarized_def'.mp (mem_Pi_iff.mp X.2) g
    rw [Finsupp.mem_support_iff] at hg ⊢
    intro hX0
    apply hg
    simp only [restval, Finsupp.tsub_apply, Finsupp.single_apply, hX0]
    omega
  rcases hsig_lt with h_pos | h_neg
  · let ε : GeneType := .Positive
    have hε : ε ≠ .NonPolarized := by decide
    let X1 : Pi := Pi.X1 hε (le_refl r) hr
    let Y1 : Pi := Pi.Y1 hε (le_refl r) hr
    let rest_pi : Pi := ⟨restval, rest_mem⟩
    have hX1_val : X1.val = Finsupp.single gpos 1 + Finsupp.single gneg 1 := by
      rw [Pi.X1_eq, GeneType.neg_positive, hgpos_eq, hgneg_eq]
    have hX_eq : X1.val + restval = X.val := by
      rw [hX1_val]
      exact X_eq_X1_add_rest hXgpos hXgneg hne
    let Z : Pi := ⟨Y1.val + restval, add_mem Y1.2 rest_mem⟩
    refine ⟨Z, (Subtype.ext hX_eq : X1 + rest_pi = X) ▸
      Pi.Step.mk X1 Y1 rest_pi (Pi.Primitive.type1 ε hε (le_refl r) hr), ?_⟩
    change Y1.val + restval ≤ Y.val
    rw [le_iff_dominates]
    intro j
    rw [iterate_map_add, map_add]
    have hdecomp : signature (prime^[j] X.val) =
        signature (prime^[j] X1.val) + signature (prime^[j] restval) := by
      rw [← hX_eq, iterate_map_add, map_add]
    have hXYj : signature (prime^[j] X.val) ≤ signature (prime^[j] Y.val) :=
      le_iff_dominates.mp hXY.le j
    rcases lt_trichotomy j r with hjr | rfl | hjr
    · have hY1X1 : signature (prime^[j] Y1.val) = signature (prime^[j] X1.val) :=
        signature_type1_eq_before hε hr hjr
      rw [hY1X1, ← hdecomp]
      exact hXYj
    · have hrest_eq : signature (prime^[r] restval) = signature (prime^[r] X.val) := by
        rw [hdecomp, signature_type1_source_self_eq_zero hε hr, zero_add]
      rw [signature_type1_target_self_positive hε hr, hrest_eq]
      simp only [Sigma.sigma] at h_pos hle_r
      obtain ⟨nX, hnX⟩ := signature_pi_isNat (prime_mem_Pi_iterate X.2 (k := r))
      obtain ⟨nY, hnY⟩ := signature_pi_isNat (prime_mem_Pi_iterate Y.2 (k := r))
      constructor
      · simp only [Prod.fst_add]
        rw [hnX, hnY] at h_pos ⊢
        simpa [add_comm] using cast_add_one_le_of_lt h_pos
      · simp only [Prod.snd_add, zero_add]
        exact hle_r.2
    · have hrestj : signature (prime^[j] restval) = signature (prime^[j] X.val) := by
        rw [hdecomp, signature_type1_source_after_eq_zero hε hr hjr, zero_add]
      rw [signature_type1_target_after_eq_zero hε hr hjr, zero_add, hrestj]
      exact hXYj
  · let ε : GeneType := .Negative
    have hε : ε ≠ .NonPolarized := by decide
    let X1 : Pi := Pi.X1 hε (le_refl r) hr
    let Y1 : Pi := Pi.Y1 hε (le_refl r) hr
    let rest_pi : Pi := ⟨restval, rest_mem⟩
    have hX1_val : X1.val = Finsupp.single gpos 1 + Finsupp.single gneg 1 := by
      rw [Pi.X1_eq, GeneType.neg_negative, hgneg_eq, hgpos_eq, add_comm]
    have hX_eq : X1.val + restval = X.val := by
      rw [hX1_val]
      exact X_eq_X1_add_rest hXgpos hXgneg hne
    let Z : Pi := ⟨Y1.val + restval, add_mem Y1.2 rest_mem⟩
    refine ⟨Z, (Subtype.ext hX_eq : X1 + rest_pi = X) ▸
      Pi.Step.mk X1 Y1 rest_pi (Pi.Primitive.type1 ε hε (le_refl r) hr), ?_⟩
    change Y1.val + restval ≤ Y.val
    rw [le_iff_dominates]
    intro j
    rw [iterate_map_add, map_add]
    have hdecomp : signature (prime^[j] X.val) =
        signature (prime^[j] X1.val) + signature (prime^[j] restval) := by
      rw [← hX_eq, iterate_map_add, map_add]
    have hXYj : signature (prime^[j] X.val) ≤ signature (prime^[j] Y.val) :=
      le_iff_dominates.mp hXY.le j
    rcases lt_trichotomy j r with hjr | rfl | hjr
    · have hY1X1 : signature (prime^[j] Y1.val) = signature (prime^[j] X1.val) :=
        signature_type1_eq_before hε hr hjr
      rw [hY1X1, ← hdecomp]
      exact hXYj
    · have hrest_eq : signature (prime^[r] restval) = signature (prime^[r] X.val) := by
        rw [hdecomp, signature_type1_source_self_eq_zero hε hr, zero_add]
      rw [signature_type1_target_self_negative hε hr, hrest_eq]
      simp only [Sigma.sigma] at h_neg hle_r
      obtain ⟨nX, hnX⟩ := signature_pi_isNat (prime_mem_Pi_iterate X.2 (k := r))
      obtain ⟨nY, hnY⟩ := signature_pi_isNat (prime_mem_Pi_iterate Y.2 (k := r))
      constructor
      · simp only [Prod.fst_add, zero_add]
        exact hle_r.1
      · simp only [Prod.snd_add]
        rw [hnX, hnY] at h_neg ⊢
        simpa [add_comm] using cast_add_one_le_of_lt h_neg
    · have hrestj : signature (prime^[j] restval) = signature (prime^[j] X.val) := by
        rw [hdecomp, signature_type1_source_after_eq_zero hε hr hjr, zero_add]
      rw [signature_type1_target_after_eq_zero hε hr hjr, zero_add, hrestj]
      exact hXYj

/-- If `X` and `Y` have the same rank and `X.1 ≤ Y.1` in `Pi`, then their sigma values
agree at level `0`.

The key is that `signature_sum_eq_rank` gives `a₀ + b₀ = rank = c₀ + d₀`, and since
`a₀ ≤ c₀` and `b₀ ≤ d₀` from sigma-dominance, equality is forced componentwise. -/
lemma sigma_zero_eq {n : ℕ} (X Y : nPi n) (hXY : X.1 ≤ Y.1) :
    Sigma.sigma X.1 0 = Sigma.sigma Y.1 0 := by
  simp only [Sigma.sigma, Function.iterate_zero, id]
  have hsig_le := (le_iff_dominates.mp hXY) 0
  simp only [Function.iterate_zero, id] at hsig_le
  obtain ⟨h1_le, h2_le⟩ := Prod.le_def.mp hsig_le
  have hXsum := @signature_sum_eq_rank X.1.val
  have hYsum := @signature_sum_eq_rank Y.1.val
  have hXrank : (X.1.val.rank : ℚ) = n := by exact_mod_cast X.2
  have hYrank : (Y.1.val.rank : ℚ) = n := by exact_mod_cast Y.2
  exact Prod.ext (by linarith) (by linarith)

/-- First component of `sigma_zero_eq`. -/
lemma sigma_zero_fst_eq {n : ℕ} (X Y : nPi n) (hXY : X.1 ≤ Y.1) :
    (Sigma.sigma X.1 0).1 = (Sigma.sigma Y.1 0).1 :=
  congrArg Prod.fst (sigma_zero_eq X Y hXY)

/-- Second component of `sigma_zero_eq`. -/
lemma sigma_zero_snd_eq {n : ℕ} (X Y : nPi n) (hXY : X.1 ≤ Y.1) :
    (Sigma.sigma X.1 0).2 = (Sigma.sigma Y.1 0).2 :=
  congrArg Prod.snd (sigma_zero_eq X Y hXY)

lemma theorem6_snd_gap_le_of_dominates {n i : ℕ} (X Y : nPi n) (hXY : X.1 ≤ Y.1) :
    (Sigma.sigma Y.1 0).2 - (Sigma.sigma Y.1 i).2 ≤
      (Sigma.sigma X.1 0).2 - (Sigma.sigma X.1 i).2 := by
  have hb0_eq_d0 : (Sigma.sigma X.1 0).2 = (Sigma.sigma Y.1 0).2 := sigma_zero_snd_eq X Y hXY
  have hbi_le_di : (Sigma.sigma X.1 i).2 ≤ (Sigma.sigma Y.1 i).2 :=
    (le_iff_dominates.mp hXY i).2
  linarith

/-- **X-side equalities** (Step 5, Case 1 of §15, Djoković 1982).

For `j < g₂.rank = k`, the alternating sigma-differences of `X` are all equal to `a₀ − a₁`:
the `.1`-difference at even `j` and `.2`-difference at odd `j` equal
`(Sigma.sigma X 0).1 − (Sigma.sigma X 1).1`.

The proof uses the column-count formula: `aᵢ₋₁ − aᵢ` counts g₊-genes of rank ≥ i when i is odd,
and g₋-genes of rank ≥ i when i is even. Minimality of k (among g₊-ranks) forces the g₊-count
to equal P on the whole range [1, k], giving the constant chain. -/
lemma x_side_equalities
    {X : Pi} {g₂ : Gene}
    (hg₂min : ∀ g' : Gene,
      Gene.ofRankAlt g'.rank GeneType.Positive = Finsupp.single g' 1 →
      0 < X.val g' → g₂.rank ≤ g'.rank)
    {j : ℕ} (hj : j < g₂.rank) :
    (if Even j then
      (Sigma.sigma X j).1 - (Sigma.sigma X (j + 1)).1
    else
      (Sigma.sigma X j).2 - (Sigma.sigma X (j + 1)).2) =
    (Sigma.sigma X 0).1 - (Sigma.sigma X 1).1 := by
  -- Column-count formula: the alternating sigma-diff at i equals the total multiplicity of
  -- g₊-subscript genes in X with rank > i.
  -- (For even i the `.1` diff counts g₊-genes contributing to column i+1; for odd i the `.2` diff.)
  have hcol : ∀ i : ℕ, (if Even i then
      (Sigma.sigma X i).1 - (Sigma.sigma X (i + 1)).1
    else
      (Sigma.sigma X i).2 - (Sigma.sigma X (i + 1)).2) =
    ∑ g ∈ X.val.support.filter (fun g =>
        i < g.rank ∧ g.type = Int.negOnePow (g.rank - 1) • GeneType.Positive),
      (X.val g : ℚ) := by
    intro i
    split_ifs
    · rw [Sigma.sigma_fst_diff X.val i X.2]
      exact Sigma.prime_iterate_sum_pos_eq X.val i ‹Even i›
    · rw [Sigma.sigma_snd_diff X.val i X.2]
      exact Sigma.prime_iterate_sum_neg_eq X.val i ‹¬Even i›
  rw [hcol j]
  -- At i = 0 (even), rank > 0 holds for all genes (rank_pos), so the formula gives the
  -- total g₊-count P = Σ_{g₊-genes in X} X.val g.
  have hRHS : (Sigma.sigma X 0).1 - (Sigma.sigma X 1).1 =
      ∑ g ∈ X.val.support.filter (fun g =>
        g.type = Int.negOnePow (g.rank - 1) • GeneType.Positive), (X.val g : ℚ) := by
    have h0 := hcol 0
    -- Reduce the `if Even 0 then A(0+1) else B(0+1)` form in h0 to `A(1)` by proving heq
    -- against an explicitly-written if-expression (avoiding the pattern-matching failure that
    -- occurs when if_pos is applied directly to h0 whose `Even 0` may be stored unfolded).
    have heq : (if Even (0 : ℕ) then (Sigma.sigma X 0).1 - (Sigma.sigma X (0 + 1)).1
                else (Sigma.sigma X 0).2 - (Sigma.sigma X (0 + 1)).2) =
               (Sigma.sigma X 0).1 - (Sigma.sigma X 1).1 := by
      rw [if_pos (by norm_num : Even (0 : ℕ))]
    rw [← heq, h0]
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext g
    simp only [Finset.mem_filter]
    exact ⟨fun ⟨hs, _, ht⟩ => ⟨hs, ht⟩, fun ⟨hs, ht⟩ => ⟨hs, g.rank_pos, ht⟩⟩
  rw [hRHS]
  -- Constancy: for j < g₂.rank every g₊-gene has rank ≥ g₂.rank > j,
  -- so the condition `j < g.rank` is redundant and the two filter-sums agree.
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext g
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hsupp, _, htype⟩
    exact ⟨hsupp, htype⟩
  · rintro ⟨hsupp, htype⟩
    refine ⟨hsupp, ?_, htype⟩
    have hg2le : g₂.rank ≤ g.rank :=
      hg₂min g
        (by
          rw [Gene.ofRankAlt_eq_gene g.rank_pos]
          congr 1
          exact Gene.ext rfl htype.symm)
        (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hsupp))
    omega

private lemma prime_iterate_actual_type_sum_eq (X : Chromosome) (k : ℕ) (ε : GeneType) :
    (prime^[k] X).sum (fun g m ↦ if g.type = ε then (m : ℚ) else 0) =
    ∑ g ∈ X.support.filter (fun g => k < g.rank ∧ g.type = ε), (X g : ℚ) := by
  simp only [Finsupp.sum]
  conv_lhs =>
    arg 2
    ext g
    rw [prime_iterate_coeff k X g]
  rw [← Finset.sum_filter]
  refine Finset.sum_bij'
      (fun g _ => (⟨g.rank + k, g.type, Nat.le_add_right_of_le g.rank_pos⟩ : Gene))
      (fun g' hg' => (⟨g'.rank - k, g'.type, by
        have hlt := (Finset.mem_filter.mp hg').2.1
        omega⟩ : Gene))
      ?_ ?_ ?_ ?_ ?_
  · intro g hg
    simp only [Finset.mem_filter, Finsupp.mem_support_iff] at hg ⊢
    obtain ⟨hgsupp, hgtype⟩ := hg
    refine ⟨by rwa [← prime_iterate_coeff], ?_, ?_⟩
    · have := g.rank_pos
      omega
    · exact hgtype
  · intro g' hg'
    simp only [Finset.mem_filter, Finsupp.mem_support_iff] at hg' ⊢
    obtain ⟨hgsupp', hlt, hgtype'⟩ := hg'
    have hle : k ≤ g'.rank := Nat.le_of_lt hlt
    refine ⟨?_, ?_⟩
    · rw [prime_iterate_coeff]
      simp only [Nat.sub_add_cancel hle]
      exact hgsupp'
    · exact hgtype'
  · intro g _
    exact Gene.ext (Nat.add_sub_cancel g.rank k) rfl
  · intro g' hg'
    have hle : k ≤ g'.rank := Nat.le_of_lt (Finset.mem_filter.mp hg').2.1
    exact Gene.ext (Nat.sub_add_cancel hle) rfl
  · intros
    rfl

lemma x_actual_negative_prefix_equalities
    {X : Pi} {g₂ : Gene}
    (hg₂_min : ∀ g' : Gene, g'.type = .Negative → 0 < X.val g' → g₂.rank ≤ g'.rank)
    {i : ℕ} (hi : 1 ≤ i) (hi₂ : i ≤ g₂.rank) :
    (Sigma.sigma X.val 0).2 - (Sigma.sigma X.val (i - 1)).2 =
      (Sigma.sigma X.val 1).1 - (Sigma.sigma X.val i).1 := by
  have hcount0 := Sigma.b0_sub_a1_eq_neg_count X.val X.2
  have hcounti := Sigma.b0_sub_a1_eq_neg_count (prime^[i - 1] X.val)
    (Variety.prime_mem_Pi_iterate X.2 (k := i - 1))
  simp only [Sigma.sigma, Function.iterate_zero, id, Function.iterate_one] at hcount0 hcounti
  have hcount :
      (prime^[i - 1] X.val).sum
          (fun g m => if g.type = GeneType.Negative then (m : ℚ) else 0) =
        X.val.sum (fun g m => if g.type = GeneType.Negative then (m : ℚ) else 0) := by
    rw [prime_iterate_actual_type_sum_eq X.val (i - 1) GeneType.Negative]
    rw [Finsupp.sum, ← Finset.sum_filter]
    apply Finset.sum_congr
    · ext g
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hsupp, _, hneg⟩
        exact ⟨hsupp, hneg⟩
      · rintro ⟨hsupp, hneg⟩
        refine ⟨hsupp, ?_ , hneg⟩
        have hpos : 0 < X.val g := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hsupp)
        have hg₂_le := hg₂_min g hneg hpos
        omega
    · intro g _
      rfl
  have hprime_i : prime (prime^[i - 1] X.val) = prime^[i] X.val := by
    have hi_eq : i = i - 1 + 1 := by omega
    rw [hi_eq]
    exact (Function.iterate_succ_apply' prime (i - 1) X.val).symm
  simp only [Sigma.sigma, Function.iterate_zero, id, Function.iterate_one]
  rw [← hprime_i]
  linarith

lemma caseA2_strict_fst
    {n : ℕ} (X Y : nPi n) (hXY : X.1 < Y.1)
    {g₂ : Gene}
    (hg₂_min : ∀ g' : Gene, g'.type = .Negative → 0 < X.1.val g' → g₂.rank ≤ g'.rank)
    (hb₀_eq_d₀ : (Sigma.sigma X.1.val 0).2 = (Sigma.sigma Y.1.val 0).2)
    (ha : (Sigma.sigma X.1 1).1 < (Sigma.sigma Y.1 1).1)
    {i : ℕ} (hi : 1 ≤ i) (hi₂ : i ≤ g₂.rank) :
    (Sigma.sigma X.1.val i).1 < (Sigma.sigma Y.1.val i).1 := by
  have hY_chain : (Sigma.sigma Y.1.val 0).2 - (Sigma.sigma Y.1.val (i - 1)).2 ≥
      (Sigma.sigma Y.1.val 1).1 - (Sigma.sigma Y.1.val i).1 :=
    Sigma.a1_ai_le_b0_bi_1 Y.1.val Y.1.2 hi
  have hX_eq : (Sigma.sigma X.1.val 0).2 - (Sigma.sigma X.1.val (i - 1)).2 =
      (Sigma.sigma X.1.val 1).1 - (Sigma.sigma X.1.val i).1 := by
    exact x_actual_negative_prefix_equalities hg₂_min hi hi₂
  have hXY_pred : (Sigma.sigma X.1.val (i - 1)).2 ≤
      (Sigma.sigma Y.1.val (i - 1)).2 :=
    (le_iff_dominates.mp hXY.le (i - 1)).2
  linarith
