import YoungDiagram.Sigma.Basic
import YoungDiagram.Sigma.Diff

open Chromosome Finsupp

namespace Sigma

variable (X : Chromosome)

local notation "a" X:max k:max => Prod.fst (sigma X k)

local notation "b" X:max k:max => Prod.snd (sigma X k)

lemma mem_support_single_add_self (g : Gene) {n : ℕ} {f : Chromosome} (hn : n ≠ 0) :
    g ∈ (Finsupp.single g n + f).support := by
  simp [Finsupp.mem_support_iff, hn]

lemma mem_support_single_add_of_mem_support {g g' : Gene} {n : ℕ} {f : Chromosome}
    (hgf : g ∉ f.support) (hg' : g' ∈ f.support) :
    g' ∈ (Finsupp.single g n + f).support := by
  have hne : g' ≠ g := fun h => hgf (h ▸ hg')
  simp [Finsupp.mem_support_iff, Finsupp.add_apply, hne, Finsupp.mem_support_iff.mp hg']

lemma b_single_add (g : Gene) (n : ℕ) (f : Chromosome) (k : ℕ) :
    b (Finsupp.single g n + f) k = b (Finsupp.single g n) k + b f k :=
  congr_arg Prod.snd (sigma_linearity (X := Finsupp.single g n) (Y := f) (i := k))

lemma b_single_nsmul (g : Gene) (n k : ℕ) :
    b (Finsupp.single g n) k = n * b (Finsupp.single g 1) k := by
  have heq : Finsupp.single g n = n • Finsupp.single g 1 := (smul_single_one g n).symm
  simp only [sigma, heq, iterate_map_nsmul, map_nsmul, nsmul_eq_mul]
  simp

lemma b_single_add_diff (g : Gene) (n : ℕ) (f : Chromosome) (i j : ℕ) :
    b (Finsupp.single g n + f) i - b (Finsupp.single g n + f) j =
      (b f i - b f j) + n * (b (Finsupp.single g 1) i - b (Finsupp.single g 1) j) := by
  rw [b_single_add, b_single_add, b_single_nsmul g n i, b_single_nsmul g n j]
  ring

lemma single_b0_eq_a1_of_positive (g : Gene) (hgt : g.type = .Positive) :
    b(Finsupp.single g 1)0 = a(Finsupp.single g 1)1 := by
  rcases Nat.even_or_odd g.rank with ⟨j, hj⟩ | ⟨j, hj⟩
  · have hk : 1 ≤ g.rank - 1 := by have := g.rank_pos; omega
    have hb₀ : b(Finsupp.single g 1)0 = (g.rank : ℚ) / 2 := by
      simp only [sigma, Function.iterate_zero, id, signature_single g.rank_pos]
      rw [Gene.signature_of_positive hgt, if_pos ⟨j, hj⟩]; simp
    have ha₁ : a(Finsupp.single g 1)1 = ((↑(g.rank - 1) : ℚ) + 1) / 2 := by
      simp only [sigma, Function.iterate_succ_apply', Function.iterate_zero, id,
        prime_single, one_nsmul, hgt]
      rw [show Gene.ofRank (g.rank - 1) GeneType.Positive =
            Finsupp.single (⟨g.rank - 1, GeneType.Positive, hk⟩ : Gene) 1 from
            @Gene.ofRank_eq_gene ⟨g.rank - 1, GeneType.Positive, hk⟩,
          signature_single hk, Gene.signature_of_positive rfl,
          if_neg (show ¬Even (g.rank - 1) by rw [Nat.even_iff, hj]; omega)]
      simp
    rw [ha₁, hb₀]
    linarith [show (↑(g.rank - 1) : ℚ) + 1 = g.rank
      by exact_mod_cast Nat.sub_add_cancel g.rank_pos]
  · by_cases h1 : g.rank = 1
    · have hb₀ : b(Finsupp.single g 1)0 = 0 := by
        simp only [sigma, Function.iterate_zero, id, signature_single g.rank_pos]
        rw [Gene.signature_of_positive hgt,
            if_neg (show ¬Even g.rank by rw [Nat.even_iff, hj]; omega)]
        norm_num [h1]
      have ha₁ : a(Finsupp.single g 1)1 = 0 := by
        simp only [sigma, Function.iterate_succ_apply', Function.iterate_zero, id,
          prime_single, one_nsmul, hgt, h1, Nat.sub_self, Gene.ofRank_zero, map_zero]
        rfl
      linarith
    · have hk : 1 ≤ g.rank - 1 := by omega
      have hb₀ : b(Finsupp.single g 1)0 = ((g.rank : ℚ) - 1) / 2 := by
        simp only [sigma, Function.iterate_zero, id, signature_single g.rank_pos]
        rw [Gene.signature_of_positive hgt,
            if_neg (show ¬Even g.rank by rw [Nat.even_iff, hj]; omega)]
        simp
      have ha₁ : a(Finsupp.single g 1)1 = (↑(g.rank - 1) : ℚ) / 2 := by
        simp only [sigma, Function.iterate_succ_apply', Function.iterate_zero, id,
          prime_single, one_nsmul, hgt]
        rw [show Gene.ofRank (g.rank - 1) GeneType.Positive =
              Finsupp.single (⟨g.rank - 1, GeneType.Positive, hk⟩ : Gene) 1 from
              @Gene.ofRank_eq_gene ⟨g.rank - 1, GeneType.Positive, hk⟩,
            signature_single hk, Gene.signature_of_positive rfl,
            if_pos (show Even (g.rank - 1) by rw [Nat.even_iff, hj]; omega)]
        simp
      rw [ha₁, hb₀]
      linarith [show (↑(g.rank - 1) : ℚ) = g.rank - 1
        by exact_mod_cast Nat.cast_sub g.rank_pos]

lemma single_b0_eq_a1_add_one_of_negative (g : Gene) (hgt : g.type = .Negative) :
    b(Finsupp.single g 1)0 = a(Finsupp.single g 1)1 + 1 := by
  rcases Nat.even_or_odd g.rank with ⟨j, hj⟩ | ⟨j, hj⟩
  · have hk : 1 ≤ g.rank - 1 := by have := g.rank_pos; omega
    have hb₀ : b(Finsupp.single g 1)0 = (g.rank : ℚ) / 2 := by
      simp only [sigma, Function.iterate_zero, id, signature_single g.rank_pos]
      rw [Gene.signature_of_negative hgt, if_pos ⟨j, hj⟩]; simp
    have ha₁ : a(Finsupp.single g 1)1 = ((↑(g.rank - 1) : ℚ) - 1) / 2 := by
      simp only [sigma, Function.iterate_succ_apply', Function.iterate_zero, id,
        prime_single, one_nsmul, hgt]
      rw [show Gene.ofRank (g.rank - 1) GeneType.Negative =
            Finsupp.single (⟨g.rank - 1, GeneType.Negative, hk⟩ : Gene) 1 from
            @Gene.ofRank_eq_gene ⟨g.rank - 1, GeneType.Negative, hk⟩,
          signature_single hk, Gene.signature_of_negative rfl,
          if_neg (show ¬Even (g.rank - 1) by rw [Nat.even_iff, hj]; omega)]
      simp
    rw [ha₁, hb₀]
    linarith [show (↑(g.rank - 1) : ℚ) + 1 = g.rank
      by exact_mod_cast Nat.sub_add_cancel g.rank_pos]
  · by_cases h1 : g.rank = 1
    · have hb₀ : b(Finsupp.single g 1)0 = 1 := by
        simp only [sigma, Function.iterate_zero, id, signature_single g.rank_pos]
        rw [Gene.signature_of_negative hgt,
            if_neg (show ¬Even g.rank by rw [Nat.even_iff, hj]; omega)]
        norm_num [h1]
      have ha₁ : a(Finsupp.single g 1)1 = 0 := by
        simp only [sigma, Function.iterate_succ_apply', Function.iterate_zero, id,
          prime_single, one_nsmul, hgt, h1, Nat.sub_self, Gene.ofRank_zero, map_zero]
        rfl
      linarith
    · have hk : 1 ≤ g.rank - 1 := by omega
      have hb₀ : b(Finsupp.single g 1)0 = ((g.rank : ℚ) + 1) / 2 := by
        simp only [sigma, Function.iterate_zero, id, signature_single g.rank_pos]
        rw [Gene.signature_of_negative hgt,
            if_neg (show ¬Even g.rank by rw [Nat.even_iff, hj]; omega)]
        simp
      have ha₁ : a(Finsupp.single g 1)1 = (↑(g.rank - 1) : ℚ) / 2 := by
        simp only [sigma, Function.iterate_succ_apply', Function.iterate_zero, id,
          prime_single, one_nsmul, hgt]
        rw [show Gene.ofRank (g.rank - 1) GeneType.Negative =
              Finsupp.single (⟨g.rank - 1, GeneType.Negative, hk⟩ : Gene) 1 from
              @Gene.ofRank_eq_gene ⟨g.rank - 1, GeneType.Negative, hk⟩,
            signature_single hk, Gene.signature_of_negative rfl,
            if_pos (show Even (g.rank - 1) by rw [Nat.even_iff, hj]; omega)]
        simp
      rw [ha₁, hb₀]
      linarith [show (↑(g.rank - 1) : ℚ) = g.rank - 1
        by exact_mod_cast Nat.cast_sub g.rank_pos]

lemma neg_type_of_b0_gt_a1_single (g : Gene) (hg : Finsupp.single g 1 ∈ Variety.Pi)
    (h : a(Finsupp.single g 1)1 < b(Finsupp.single g 1)0) :
    g.type = .Negative := by
  have hpol : g.type ≠ .NonPolarized :=
    (Chromosome.IsPolarized_def'.mp (Variety.mem_Pi_iff.mp hg)) g
      (Finsupp.mem_support_iff.mpr (by simp))
  cases hgt : g.type with
  | Negative => rfl
  | Positive =>
    linarith [single_b0_eq_a1_of_positive g hgt]
  | NonPolarized => exact absurd hgt hpol

lemma pos_type_of_b0_le_a1_single (g : Gene) (hg : Finsupp.single g 1 ∈ Variety.Pi)
    (h : a(Finsupp.single g 1)1 ≥ b(Finsupp.single g 1)0) :
    g.type = .Positive := by
  have hpol : g.type ≠ .NonPolarized :=
    (Chromosome.IsPolarized_def'.mp (Variety.mem_Pi_iff.mp hg)) g
      (Finsupp.mem_support_iff.mpr (by simp))
  cases hgt : g.type with
  | Positive => rfl
  | Negative =>
    linarith [single_b0_eq_a1_add_one_of_negative g hgt]
  | NonPolarized => exact absurd hgt hpol

lemma b0_sub_a1_eq_neg_count (hX : X ∈ Variety.Pi) :
    b X 0 - a X 1 = X.sum (fun g n => if g.type = .Negative then (n : ℚ) else 0) := by
  have hb₀ : b X 0 = X.sum (fun g n => n • b(Finsupp.single g 1)0) := by
    simp [sigma, signature_snd]
  have ha₁ : a X 1 = X.sum (fun g n => n • a(Finsupp.single g 1)1) := by
    simp [sigma, signature_prime_fst]
  rw [hb₀, ha₁]
  simp only [Finsupp.sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun g hg => ?_)
  have hpol : g.type ≠ .NonPolarized :=
    IsPolarized_def'.mp (Variety.mem_Pi_iff.mp hX) g hg
  cases hgt : g.type with
  | NonPolarized => exact absurd hgt hpol
  | Positive =>
    simp only [reduceCtorEq, ↓reduceIte]
    have hba := single_b0_eq_a1_of_positive g hgt
    rw [hba]
    simp
  | Negative =>
    simp only [↓reduceIte, nsmul_eq_mul]
    have hba := single_b0_eq_a1_add_one_of_negative g hgt
    rw [hba]
    ring

/-- For a polarized gene of rank ≥ 2, applying prime twice drops the signature by (1, 1). -/
lemma signature_sub_prime2_ofRank (g : Gene) (hε : g.type ≠ .NonPolarized)
    (hrank : 2 ≤ g.rank) :
    (Gene.ofRank g.rank g.type).signature -
      (Gene.ofRank (g.rank - 2) g.type).signature = (1, 1) := by
  cases hgt : g.type with
  | NonPolarized => exact absurd hgt hε
  | Positive =>
    rw [signature_ofRank_positive g.rank_pos,
        signature_ofRank_negative (by omega : 1 ≤ g.rank - 1),
        show g.rank - 1 - 1 = g.rank - 2 from by omega]
    abel_nf
    simp
  | Negative =>
    rw [signature_ofRank_negative g.rank_pos,
        signature_ofRank_positive (by omega : 1 ≤ g.rank - 1),
        show g.rank - 1 - 1 = g.rank - 2 from by omega]
    abel_nf
    simp

lemma b0_minus_b2_pol_gene (g : Gene) (hε : g.type ≠ .NonPolarized)
  (hrank : g.rank ≥ 2) :
  b (Finsupp.single g 1) 0 - b (Finsupp.single g 1) 2 = 1 := by
  have hb₀ : b (Finsupp.single g 1) 0 = (Gene.ofRank g.rank g.type).signature.2 := by
    simp only [sigma, Function.iterate_zero, id]
    rw [← Gene.ofRank_eq_gene]
  have hb₂ : b (Finsupp.single g 1) 2 = (Gene.ofRank (g.rank - 2) g.type).signature.2 := by
    simp only [sigma]
    rw [← Gene.ofRank_eq_gene, prime_iterate_ofRank]
  rw [hb₀, hb₂]
  have := congr_arg Prod.snd (signature_sub_prime2_ofRank g hε hrank)
  simpa using this

lemma b0_minus_b2 {X : Variety.Pi} (m : ℕ)
    (hm : m ≥ 2) (hmin : ∀ g ∈ X.val.support, m ≤ g.rank) :
    b X 0 - b X 2 = X.val.sum (fun _ n => n) := by
  -- Prove the equivalent statement for any Chromosome, then specialize.
  -- The rank-≥-m hypothesis lifts to rank ≥ 2 via hm.
  suffices h : ∀ (f : Chromosome),
      (∀ g ∈ f.support, g.type ≠ .NonPolarized) →
      (∀ g ∈ f.support, 2 ≤ g.rank) →
      b f 0 - b f 2 = f.sum (fun _ n => (n : ℚ)) by
    have hpol : ∀ g ∈ X.val.support, g.type ≠ .NonPolarized :=
      IsPolarized_def'.mp (Variety.mem_Pi_iff.mp X.2)
    exact_mod_cast h X.val hpol (fun g hg => hm.trans (hmin g hg))
  intro f
  -- Rewrite f as the sum of its individual genes via Finsupp.induction.
  -- At each step, sigma_linearity splits b (single g n + f') k = b (single g n) k + b f' k,
  -- and nsmul linearity gives b (single g n) k = n * b (single g 1) k.
  induction f using Finsupp.induction with
  | zero => simp [sigma, map_zero]
  | single_add g n f' hgf hn ih =>
    -- Finsupp.induction gives the term as (single g n + f')
    intro hpol hrank
    -- Lift hypotheses from (single g n + f').support to {g} and f'.support.
    have hmem_g : g ∈ (Finsupp.single g n + f').support :=
      mem_support_single_add_self g hn
    have hsupp_mono : ∀ g' ∈ f'.support, g' ∈ (Finsupp.single g n + f').support :=
      fun _ => mem_support_single_add_of_mem_support hgf
    -- Conditions on the single gene g
    have hpol_g : g.type ≠ .NonPolarized := hpol g hmem_g
    have hrank_g : 2 ≤ g.rank := hrank g hmem_g
    -- Conditions on f' (for the inductive hypothesis)
    have hpol_f' : ∀ g' ∈ f'.support, g'.type ≠ .NonPolarized :=
      fun g' hg' => hpol g' (hsupp_mono g' hg')
    have hrank_f' : ∀ g' ∈ f'.support, 2 ≤ g'.rank :=
      fun g' hg' => hrank g' (hsupp_mono g' hg')
    -- The single-gene result: b (single g 1) 0 - b (single g 1) 2 = 1
    have hone : b (Finsupp.single g 1) 0 - b (Finsupp.single g 1) 2 = 1 :=
      b0_minus_b2_pol_gene g hpol_g hrank_g
    -- Inductive hypothesis applied to f'
    have ih' : b f' 0 - b f' 2 = f'.sum (fun _ k => (k : ℚ)) := ih hpol_f' hrank_f'
    rw [b_single_add_diff g n f' 0 2, ih', hone, mul_one]
    -- Finsupp.sum of (single g n + f') = n + Finsupp.sum f'
    rw [Finsupp.sum_add_index' (fun _ => by norm_cast) (fun _ _ _ => by push_cast; ring),
        Finsupp.sum_single_index (by norm_cast)]
    ring

lemma bk_minus_bk2 {X : Variety.Pi} (k m : ℕ)
    (hmin : ∀ g ∈ X.val.support, m ≤ g.rank)
    (hk : k + 2 ≤ m) :
    b X k - b X (k + 2) = X.val.sum (fun _ n => n) := by
  -- Step 1: Reduce to b (prime^[k] X) 0 - b (prime^[k] X) 2.
  -- By sigma definition: b X k = (signature (prime^[k] X)).2 = b (prime^[k] X) 0.
  -- Similarly b X (k+2) = b (prime^[k] X) 2 via prime^[k+2] = prime^[2] ∘ prime^[k].
  have hbk : b X k = b (Chromosome.prime^[k] X) 0 := by
    simp [sigma, Function.iterate_zero]
  have hbk2 : b X (k + 2) = b (Chromosome.prime^[k] X) 2 := by
    simp only [sigma]
    rw [show k + 2 = 2 + k from Nat.add_comm k 2, Function.iterate_add_apply]
  rw [hbk, hbk2]
  -- Step 2: Let Y := prime^[k] X as a Variety.Pi element.
  let Y : Variety.Pi := ⟨Chromosome.prime^[k] X, Variety.prime_mem_Pi_iterate X.2⟩
  -- Step 3: All genes in Y have rank ≥ m - k ≥ 2.
  have hmin_Y : ∀ g ∈ Y.val.support, m - k ≤ g.rank := by
    intro g hg
    rw [Finsupp.mem_support_iff, prime_iterate_coeff] at hg
    have hgX : ⟨g.rank + k, g.type, Nat.le_add_right_of_le g.rank_pos⟩ ∈ X.val.support :=
      Finsupp.mem_support_iff.mpr hg
    have := hmin _ hgX
    simp
    omega
  have hm_Y : m - k ≥ 2 := by omega
  -- Step 4: Apply b0_minus_b2 to Y.
  rw [show b (Chromosome.prime^[k] X) 0 = b Y 0 from rfl,
      show b (Chromosome.prime^[k] X) 2 = b Y 2 from rfl,
      b0_minus_b2 (m - k) hm_Y hmin_Y]
  -- Step 5: (prime^[k] X).sum (fun _ n => n) = X.val.sum (fun _ n => n).
  -- Via prime_iterate_coeff: g ↦ ⟨g.rank + k, g.type, _⟩ is a bijection
  -- from (prime^[k] X).support to X.val.support (since all ranks in X exceed k).
  simp only [Finsupp.sum, Y]
  -- Goal: ↑(∑ g ∈ (prime^[k] X).support, (prime^[k] X) g) = ↑(∑ g ∈ X.support, X g)
  -- Strip outer ℕ→ℚ casts, then prove ℕ equality via the bijection g ↦ ⟨g.rank+k, g.type, _⟩.
  norm_cast
  refine Finset.sum_bij'
      (fun g _ => (⟨g.rank + k, g.type, Nat.le_add_right_of_le g.rank_pos⟩ : Gene))
      (fun g' hg' =>
        have hle : k + 2 ≤ g'.rank := by
          have := hmin g' (Finsupp.mem_support_iff.mpr (Finsupp.mem_support_iff.mp hg'))
          simp only at this; omega
        (⟨g'.rank - k, g'.type, by omega⟩ : Gene))
      ?_ ?_ ?_ ?_ ?_
  · -- forward maps into X.val.support
    intro g hg
    rw [Finsupp.mem_support_iff] at hg ⊢
    rwa [← prime_iterate_coeff]
  · -- backward maps into (prime^[k] X).support
    intro g' hg'
    rw [Finsupp.mem_support_iff] at hg' ⊢
    rw [prime_iterate_coeff]
    have hle : k ≤ g'.rank := by
      have := hmin g' (Finsupp.mem_support_iff.mpr hg'); simp only at this; omega
    simp only [Nat.sub_add_cancel hle]
    exact hg'
  · -- forward then backward = id
    intro g _; exact Gene.ext (Nat.add_sub_cancel g.rank k) rfl
  · -- backward then forward = id
    intro g' hg'
    have hle : k ≤ g'.rank := by
      have := hmin g' (Finsupp.mem_support_iff.mpr (Finsupp.mem_support_iff.mp hg'))
      simp only at this; omega
    exact Gene.ext (Nat.sub_add_cancel hle) rfl
  · -- coefficient preserved: (prime^[k] X) g = X.val ⟨g.rank + k, g.type, _⟩
    intro g _; rw [prime_iterate_coeff]

-- case 3
/-- If all genes in X have rank ≥ m, and all rank-m genes are positive,
    then for k ≤ m - 2 the b-sequence satisfies b₀ - bₖ = b₂ - b_{k+2}. -/
lemma b0_eq_b2_positive {X : Variety.Pi} (m : ℕ)
    (hmin : ∀ g ∈ X.val.support, m ≤ g.rank)
    {k : ℕ} (hk : k ≤ m - 2) :
    b X 0 - b X k = b X 2 - b X (k + 2) := by
  by_cases hm : m ≥ 2
  · -- m ≥ 2: both b X 0 - b X 2 and b X k - b X (k+2) equal X.val.sum (fun _ n => n).
    have hk2 : k + 2 ≤ m := by omega
    have h1 := b0_minus_b2 m hm hmin
    have h2 := bk_minus_bk2 k m hmin hk2
    linarith
  · -- m < 2: k = 0 (since k ≤ m - 2 = 0 in ℕ), so both sides are 0.
    have hk0 : k = 0 := by omega
    subst hk0; ring

-- case 2
/-- If all genes in X have rank ≥ m, and all rank-m genes are negative,
    then for k ≤ m - 1 the b-sequence satisfies b₀ - bₖ = b₂ - b_{k+2}. -/
lemma b0_minus_b2_neg_gene (g : Gene) (hε : g.type = .Negative)
  (hrank : g.rank = 1) :
  b (Finsupp.single g 1) 0 - b (Finsupp.single g 1) 2 = 1 := by
  rw [show g = (⟨1, GeneType.Negative, by decide⟩ : Gene) from Gene.ext hrank hε]
  norm_num [sigma, Gene.signature, prime_single, primeGene_def]

lemma b0_minus_b2_pos_gene (g : Gene) (hε : g.type = .Positive)
  (hrank : g.rank = 1) :
  b (Finsupp.single g 1) 0 - b (Finsupp.single g 1) 2 = 0 := by
  rw [show g = (⟨1, GeneType.Positive, by decide⟩ : Gene) from Gene.ext hrank hε]
  norm_num [sigma, Gene.signature, prime_single, primeGene_def]

lemma b0_minus_b2_min_neg {X : Variety.Pi} (m : ℕ)
    (hm : m ≥ 2) (hmin : ∀ g ∈ X.val.support, m ≤ g.rank)
    (_hmin_type : ∀ g ∈ X.val.support, g.rank = m → g.type = .Negative) :
    b X 0 - b X 2 = X.val.sum (fun _ n => n) :=
  b0_minus_b2 m hm hmin

--note the bound are less strict
lemma bk_minus_bk2_min_neg {X : Variety.Pi} (k m : ℕ)
    (hk : k + 1 ≤ m) (hmin : ∀ g ∈ X.val.support, m ≤ g.rank)
    (_hmin_type : ∀ g ∈ X.val.support, g.rank = m → g.type = .Negative) :
    b X k - b X (k + 2) = X.val.sum (fun _ n => n) := by
  rcases Nat.eq_or_lt_of_le hk with h | h
  · -- k + 1 = m; reduce to b (prime^[k] X) 0 - b (prime^[k] X) 2
    have hbk : b X k = b (Chromosome.prime^[k] X) 0 := by simp [sigma]
    have hbk2 : b X (k + 2) = b (Chromosome.prime^[k] X) 2 := by
      simp only [sigma]
      rw [show k + 2 = 2 + k from Nat.add_comm k 2, Function.iterate_add_apply]
    rw [hbk, hbk2]
    let Y : Variety.Pi := ⟨Chromosome.prime^[k] X, Variety.prime_mem_Pi_iterate X.2⟩
    -- Rank-1 genes in Y came from rank-(k+1) = rank-m genes in X, so are Negative by hmin_type.
    have hrank1_neg : ∀ g ∈ Y.val.support, g.rank = 1 → g.type = .Negative := by
      intro g hg hgr
      rw [Finsupp.mem_support_iff, prime_iterate_coeff] at hg
      have hgX : ⟨g.rank + k, g.type, Nat.le_add_right_of_le g.rank_pos⟩ ∈ X.val.support :=
        Finsupp.mem_support_iff.mpr hg
      have hrank_eq : g.rank + k = m := by omega
      exact _hmin_type ⟨g.rank + k, g.type, Nat.le_add_right_of_le g.rank_pos⟩ hgX hrank_eq
    have hb_Y : b Y 0 - b Y 2 = Y.val.sum (fun _ n => (n : ℚ)) := by
      suffices h : ∀ (f : Chromosome),
          (∀ g ∈ f.support, g.type ≠ .NonPolarized) →
          (∀ g ∈ f.support, g.rank = 1 → g.type = .Negative) →
          b f 0 - b f 2 = f.sum (fun _ n => (n : ℚ)) by
        exact h Y.val (IsPolarized_def'.mp (Variety.mem_Pi_iff.mp Y.2)) hrank1_neg
      intro f
      induction f using Finsupp.induction with
      | zero => simp [sigma, map_zero]
      | single_add g n f' hgf hn ih =>
        intro hpol hrneg
        have hmem_g : g ∈ (Finsupp.single g n + f').support :=
          mem_support_single_add_self g hn
        have hsupp_mono : ∀ g' ∈ f'.support, g' ∈ (Finsupp.single g n + f').support :=
          fun _ => mem_support_single_add_of_mem_support hgf
        have hpol_g := hpol g hmem_g
        have hrneg_g := hrneg g hmem_g
        have hpol_f' : ∀ g' ∈ f'.support, g'.type ≠ .NonPolarized :=
          fun g' hg' => hpol g' (hsupp_mono g' hg')
        have hrneg_f' : ∀ g' ∈ f'.support, g'.rank = 1 → g'.type = .Negative :=
          fun g' hg' => hrneg g' (hsupp_mono g' hg')
        have hone : b (Finsupp.single g 1) 0 - b (Finsupp.single g 1) 2 = 1 := by
          by_cases hr : g.rank = 1
          · exact b0_minus_b2_neg_gene g (hrneg_g hr) hr
          · exact b0_minus_b2_pol_gene g hpol_g (by have := g.rank_pos; omega)
        have ih' := ih hpol_f' hrneg_f'
        rw [b_single_add_diff g n f' 0 2, ih', hone, mul_one,
            Finsupp.sum_add_index' (fun _ => by norm_cast) (fun _ _ _ => by push_cast; ring),
            Finsupp.sum_single_index (by norm_cast)]
        ring
    have hsum : Y.val.sum (fun _ n => (n : ℚ)) = X.val.sum (fun _ n => (n : ℚ)) := by
      simp only [Finsupp.sum, Y]
      norm_cast
      refine Finset.sum_bij'
          (fun g _ => (⟨g.rank + k, g.type, Nat.le_add_right_of_le g.rank_pos⟩ : Gene))
          (fun g' hg' =>
            have hle : k + 1 ≤ g'.rank := by
              have := hmin g' (Finsupp.mem_support_iff.mpr (Finsupp.mem_support_iff.mp hg'))
              simp only at this; omega
            (⟨g'.rank - k, g'.type, by omega⟩ : Gene))
          ?_ ?_ ?_ ?_ ?_
      · intro g hg
        rw [Finsupp.mem_support_iff] at hg ⊢
        rwa [← prime_iterate_coeff]
      · intro g' hg'
        rw [Finsupp.mem_support_iff] at hg' ⊢
        rw [prime_iterate_coeff]
        have hle : k ≤ g'.rank := by
          have := hmin g' (Finsupp.mem_support_iff.mpr hg'); simp only at this; omega
        simp only [Nat.sub_add_cancel hle]
        exact hg'
      · intro g _; exact Gene.ext (Nat.add_sub_cancel g.rank k) rfl
      · intro g' hg'
        have hle : k ≤ g'.rank := by
          have := hmin g' (Finsupp.mem_support_iff.mpr (Finsupp.mem_support_iff.mp hg'))
          simp only at this; omega
        exact Gene.ext (Nat.sub_add_cancel hle) rfl
      · intro g _; rw [prime_iterate_coeff]
    rw [show b (Chromosome.prime^[k] X) 0 = b Y 0 from rfl,
        show b (Chromosome.prime^[k] X) 2 = b Y 2 from rfl, hb_Y, hsum]
    norm_cast
  · -- k + 2 ≤ m
    exact bk_minus_bk2 k m hmin (by omega)

lemma b0_eq_b2_negative {X : Variety.Pi} (m : ℕ) (hm : m ≥ 2)
    (hmin : ∀ g ∈ X.val.support, m ≤ g.rank)
    (hpos : ∀ g ∈ X.val.support, g.rank = m → g.type = .Negative)
    {k : ℕ} (hk : k ≤ m - 1) :
    b X 0 - b X k = b X 2 - b X (k + 2) := by
  have h1 : b X 0 - b X 2 = X.val.sum (fun _ n => n) := b0_minus_b2 m hm hmin
  have h2 : b X k - b X (k + 2) = X.val.sum (fun _ n => n) :=
    bk_minus_bk2_min_neg k m (by omega) hmin hpos
  linarith

lemma bi_sum_ai1_eq_neg_count_1 {i : ℕ} (hX : X ∈ Variety.Pi) :
    b X i - a X (i + 1) =
     (prime^[i] X).sum (fun g n => if g.type = .Negative then (n : ℚ) else 0) := by
  -- b X i = b (prime^[i] X) 0, since sigma X i = signature (prime^[i] X)
  have hbᵢ : b X i = b (prime^[i] X) 0 := by simp [sigma]
  -- a X (i+1) = a (prime^[i] X) 1, since prime^[i+1] X = prime (prime^[i] X)
  have haᵢ : a X (i + 1) = a (prime^[i] X) 1 := by
    simp [sigma, Function.iterate_succ_apply']
  rw [hbᵢ, haᵢ]
  exact b0_sub_a1_eq_neg_count (prime^[i] X) (Variety.prime_mem_Pi_iterate hX)

lemma neg_count_sum_prime_expand :
    (X.sum (fun g m => m • primeGene g)).sum
        (fun g n => if g.type = .Negative then (n : ℚ) else 0) =
      X.sum (fun g m =>
        (m • primeGene g).sum (fun g' n => if g'.type = .Negative then (n : ℚ) else 0)) := by
  rw [Finsupp.sum_sum_index (fun _ => by simp) (fun g m n => by split_ifs <;> push_cast <;> ring)]

lemma neg_count_eq_aux (hg : ∀ g ∈ X.support, g.rank = 1 → g.type = .Positive) :
    (prime X).sum (fun g n => if g.type = .Negative then (n : ℚ) else 0) =
    X.sum (fun g n => if g.type = .Negative then (n : ℚ) else 0) := by
  rw [prime_def, neg_count_sum_prime_expand]
  refine Finsupp.sum_congr (fun g hg_supp => ?_)
  by_cases hrank : g.rank = 1
  · have hpos : g.type = .Positive := hg g hg_supp hrank
    simp [primeGene_def, hrank, Gene.ofRank_zero, hpos]
  · have hne : g.rank - 1 ≠ 0 := by have := g.rank_pos; omega
    rw [primeGene_def, Gene.ofRank_eq_gene' hne]
    simp [Finsupp.sum_single_index]

lemma rank_one_positive_of_prime_iterate_support (i : ℕ)
    (hg : ∀ g ∈ X.support, g.rank ≤ i + 1 → g.type = .Positive) :
    ∀ g' ∈ (prime^[i] X).support, g'.rank = 1 → g'.type = .Positive := by
  intro g' hg' hrank1
  rw [Finsupp.mem_support_iff, prime_iterate_coeff] at hg'
  set g'' : Gene := ⟨g'.rank + i, g'.type, Nat.le_add_right_of_le g'.rank_pos⟩
  have hXsupp : g'' ∈ X.support := Finsupp.mem_support_iff.mpr hg'
  have hrank_le : g''.rank ≤ i + 1 := by
    change g'.rank + i ≤ i + 1
    omega
  exact hg g'' hXsupp hrank_le

/-- Iterating prime i times preserves the negative gene count, provided all genes
    of rank ≤ i in X are Positive (so prime^[i] kills no Negative genes). -/
lemma neg_count_eq (i : ℕ) (hg : ∀ g ∈ X.support, g.rank ≤ i → g.type = .Positive) :
    (prime^[i] X).sum (fun g n => if g.type = .Negative then (n : ℚ) else 0) =
    X.sum (fun g n => if g.type = .Negative then (n : ℚ) else 0) := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply', neg_count_eq_aux (X := prime^[i] X)]
    · exact ih (fun g hg_supp hrank_le => hg g hg_supp (Nat.le_succ_of_le hrank_le))
    · exact rank_one_positive_of_prime_iterate_support (X := X) i hg

-- This is used in case 3
lemma b0_bi_eq_a1_ai1 (hX : X ∈ Variety.Pi) (i : ℕ)
    (hg : ∀ g ∈ X.support, g.rank ≤ i → g.type = .Positive) :
    b X 0 - b X i = a X 1 - a X (i + 1) := by
  -- b X 0 - a X 1 = neg_count X  (at index 0)
  have h0 := bi_sum_ai1_eq_neg_count_1 X hX (i := 0)
  simp at h0
  -- b X i - a X (i+1) = neg_count (prime^[i] X)  (at index i)
  have hi := bi_sum_ai1_eq_neg_count_1 X hX (i := i)
  -- neg_count (prime^[i] X) = neg_count X  (since rank-≤i genes are Positive)
  have heq := neg_count_eq X i hg
  linarith

lemma neg_gene_of_b0_gt_a1 (hX : X ∈ Variety.Pi)
    (h : a X 1 < b X 0) :
    ∃ g : Gene, g.type = .Negative ∧ 0 < X g := by
  have hsum : 0 < X.sum (fun g n => if g.type = .Negative then (n : ℚ) else 0) := by
    have hcount := b0_sub_a1_eq_neg_count X hX
    linarith
  by_contra hnone
  push Not at hnone
  have hzero : X.sum (fun g n => if g.type = .Negative then (n : ℚ) else 0) = 0 := by
    rw [Finsupp.sum]
    apply Finset.sum_eq_zero
    intro g hg
    by_cases hneg : g.type = .Negative
    · have hg0 : X g = 0 := by
        have := hnone g hneg
        omega
      simp [hneg, hg0]
    · simp [hneg]
  linarith

lemma sigma_type2_left_eq {m n : ℕ} (ε : GeneType) (hε : ε ≠ .NonPolarized)
    (hle : m ≤ n) (hm : 1 < m) :
    ∀ i, i ≤ m - 2 → sigma (Pi.X2 hε hle hm) i = sigma (Pi.Y2 hε hle hm) i := by
  intro i hi
  simp only [Pi.X2_eq, Pi.Y2_eq, sigma, iterate_map_add, prime_iterate_ofRank, map_add]
  rw [show m - i = m - 2 - i + 2 from by omega,
      show n + 2 - i = n - i + 2 from by omega,
      signature_ofRank_eq₂' (m - 2 - i),
      signature_ofRank_eq₂' (n - i)]
  abel

lemma sigma_type2_right_eq {m n : ℕ} (ε : GeneType) (hε : ε ≠ .NonPolarized)
    (hle : m ≤ n) (hm : 1 < m) :
    ∀ i, n + 2 ≤ i → sigma (Pi.X2 hε hle hm) i = sigma (Pi.Y2 hε hle hm) i := by
  intro i hi
  simp only [Pi.X2_eq, Pi.Y2_eq, sigma, iterate_map_add, prime_iterate_ofRank, map_add]
  simp only [show m - i = 0 from by omega, show n - i = 0 from by omega,
    show m - 2 - i = 0 from by omega, show n + 2 - i = 0 from by omega,
    Gene.ofRank_zero, map_zero, add_zero]

lemma sigma_type2_left_boundary {m n : ℕ} (ε : GeneType) (hε : ε ≠ .NonPolarized)
    (hle : m ≤ n) (hm : 1 < m) :
    sigma (Pi.Y2 hε hle hm) (m - 1) - sigma (Pi.X2 hε hle hm) (m - 1) =
      if ε = .Positive then (0, 1) else (1, 0) := by
  simp only [Pi.X2_eq, Pi.Y2_eq, sigma]
  simp only [iterate_map_add, prime_iterate_ofRank, map_add]
  have hm1 : m - (m - 1) = 1 := by omega
  have hm0 : m - 2 - (m - 1) = 0 := by omega
  have hnrank : n + 2 - (m - 1) = n - (m - 1) + 2 := by omega
  rw [hnrank, signature_ofRank_eq₂' (n - (m - 1))]
  simp only [hm1, hm0, Gene.ofRank_zero, map_zero, zero_add]
  rcases ε with _ | _ | _
  · exact absurd rfl hε
  · simp [sub_eq_add_neg, add_assoc, add_comm]
  · simp [sub_eq_add_neg, add_assoc, add_comm]

lemma sigma_type2_mid {m n : ℕ} (ε : GeneType) (hε : ε ≠ .NonPolarized)
    (hle : m ≤ n) (hm : 1 < m) :
    ∀ i, m ≤ i → i ≤ n → sigma (Pi.Y2 hε hle hm) i - sigma (Pi.X2 hε hle hm) i = (1, 1) := by
  intro i him hin
  simp only [Pi.X2_eq, Pi.Y2_eq, sigma]
  simp only [iterate_map_add, prime_iterate_ofRank, map_add]
  have hmX : m - i = 0 := by omega
  have hmY : m - 2 - i = 0 := by omega
  have hnrank : n + 2 - i = n - i + 2 := by omega
  rw [hnrank, signature_ofRank_eq₂' (n - i)]
  simp only [hmX, hmY, Gene.ofRank_zero, map_zero, zero_add]
  simp

lemma sigma_type2_right_boundary {m n : ℕ} (ε : GeneType) (hε : ε ≠ .NonPolarized)
    (hle : m ≤ n) (hm : 1 < m) :
    sigma (Pi.Y2 hε hle hm) (n + 1) - sigma (Pi.X2 hε hle hm) (n + 1) =
      if ε = .Positive then (1, 0) else (0, 1) := by
  simp only [Pi.X2_eq, Pi.Y2_eq, sigma]
  simp only [iterate_map_add, prime_iterate_ofRank, map_add]
  have hmX : m - (n + 1) = 0 := by omega
  have hnX : n - (n + 1) = 0 := by omega
  have hmY : m - 2 - (n + 1) = 0 := by omega
  have hnY : n + 2 - (n + 1) = 1 := by omega
  simp only [hmX, hnX, hmY, hnY, Gene.ofRank_zero, map_zero, zero_add, add_zero]
  rcases ε with _ | _ | _
  · exact absurd rfl hε
  · simp [signature_ofRank_one_positive]
  · simp [signature_ofRank_one_negative]

lemma sigma_0_type2_same_rank {m : ℕ} (hm : 1 < m) :
    ∀ ε : GeneType, (hε : ε ≠ .NonPolarized) →
    let X : Chromosome := Pi.X2 hε (le_refl m) hm
    let Y : Chromosome := Pi.Y2 hε (le_refl m) hm
    sigma X 0 = sigma Y 0 := by
  intro ε hε
  simpa using sigma_type2_left_eq ε hε (le_refl m) hm 0 (by omega)

/-- Sigma invariants of the type2 mutation X2 → Y2 when both genes have the same rank m.
    The source X2 = 2·gene(m,ε) and the target Y2 = gene(m-2,ε) + gene(m+2,ε) agree on sigma
    outside the window [m-1, m+1], and differ by (1,0) (resp. (0,1)) inside
    when m is even (resp. odd). -/
lemma sigma_type2_same_rank {m : ℕ} (ε : GeneType) (hε : ε ≠ .NonPolarized) (hm : 1 < m) :
    let X : Chromosome := Pi.X2 hε (le_refl m) hm
    let Y : Chromosome := Pi.Y2 hε (le_refl m) hm
    (∀ i, i ≤ m - 2 → sigma X i = sigma Y i) ∧
    (∀ i, m + 2 ≤ i → sigma X i = sigma Y i) ∧
    (∀ i, m - 1 ≤ i → i ≤ m + 1 →
      sigma Y i - sigma X i = if i = m then (1, 1)
                              else if i = m - 1 then
                                if ε = .Positive then (0, 1) else (1, 0)
                              else if ε = .Positive then (1, 0) else (0, 1)) := by
  refine ⟨sigma_type2_left_eq ε hε (le_refl m) hm, sigma_type2_right_eq ε hε (le_refl m) hm, ?_⟩
  intro i hi1 hi2
  by_cases him1 : i = m - 1
  · rw [him1]
    simpa [show m - 1 ≠ m by omega] using sigma_type2_left_boundary ε hε (le_refl m) hm
  · by_cases him : i = m
    · rw [him]
      have hmid := sigma_type2_mid ε hε (le_refl m) hm m (le_refl m) (le_refl m)
      simpa using hmid
    · have : i = m + 1 := by omega
      rw [this]
      simpa [show m + 1 ≠ m - 1 by omega] using sigma_type2_right_boundary ε hε (le_refl m) hm

lemma sigma_type2_mn_rank_left {m n : ℕ} (ε : GeneType) (hε : ε ≠ .NonPolarized)
    (hmn : m < n) (hm : 1 < m) :
    ∀ i, i ≤ m - 2 →
      sigma (Pi.X2 hε (Nat.le_of_lt hmn) hm) i =
      sigma (Pi.Y2 hε (Nat.le_of_lt hmn) hm) i :=
  sigma_type2_left_eq ε hε (Nat.le_of_lt hmn) hm

lemma sigma_type2_mn_rank_right {m n : ℕ} (ε : GeneType) (hε : ε ≠ .NonPolarized)
    (hmn : m < n) (hm : 1 < m) :
    ∀ i, n + 2 ≤ i →
      sigma (Pi.X2 hε (Nat.le_of_lt hmn) hm) i =
      sigma (Pi.Y2 hε (Nat.le_of_lt hmn) hm) i :=
  sigma_type2_right_eq ε hε (Nat.le_of_lt hmn) hm

lemma sigma_type2_mn_rank_window {m n : ℕ} (ε : GeneType) (hε : ε ≠ .NonPolarized)
    (hmn : m < n) (hm : 1 < m) :
    ∀ i, m - 1 ≤ i → i ≤ n + 1 →
      sigma (Pi.Y2 hε (Nat.le_of_lt hmn) hm) i -
      sigma (Pi.X2 hε (Nat.le_of_lt hmn) hm) i =
      if (i > m - 1) ∧ (i < n + 1) then (1, 1)
      else if i = m - 1 then
        if ε = .Positive then (0, 1) else (1, 0)
      else if ε = .Positive then (1, 0) else (0, 1) := by
  intro i hi1 hi2
  by_cases him1 : i = m - 1
  · rw [him1]
    simp only [show ¬((m - 1 > m - 1) ∧ (m - 1 < n + 1)) from by omega, if_false, if_true]
    simpa using sigma_type2_left_boundary ε hε (Nat.le_of_lt hmn) hm
  · by_cases hin1 : i = n + 1
    · rw [hin1]
      simp only [show ¬((n + 1 > m - 1) ∧ (n + 1 < n + 1)) from by omega,
        if_false, show n + 1 ≠ m - 1 from by omega]
      simpa using sigma_type2_right_boundary ε hε (Nat.le_of_lt hmn) hm
    · have him : m ≤ i := by omega
      have hin : i ≤ n := by omega
      simp only [show (i > m - 1) ∧ (i < n + 1) from by omega, true_and, if_true]
      simpa using sigma_type2_mid ε hε (Nat.le_of_lt hmn) hm i him hin

lemma sigma_type2_mn_rank {m n : ℕ} (ε : GeneType) (hε : ε ≠ .NonPolarized)
  (hmn : m < n) (hm : 1 < m) :
    let hle : m ≤ n := Nat.le_of_lt hmn
    let X : Chromosome := Pi.X2 hε hle hm
    let Y : Chromosome := Pi.Y2 hε hle hm
    (∀ i, i ≤ m - 2 → sigma X i = sigma Y i) ∧
    (∀ i, n + 2 ≤ i → sigma X i = sigma Y i) ∧
    (∀ i, m - 1 ≤ i → i ≤ n + 1 →
      sigma Y i - sigma X i = if (i > m - 1) ∧ (i < n + 1) then (1, 1)
                              else if i = m - 1 then
                                if ε = .Positive then (0, 1) else (1, 0)
                              else
                                if ε = .Positive then (1, 0) else (0, 1)) := by
  exact ⟨sigma_type2_mn_rank_left ε hε hmn hm,
    sigma_type2_mn_rank_right ε hε hmn hm,
    sigma_type2_mn_rank_window ε hε hmn hm⟩

end Sigma
