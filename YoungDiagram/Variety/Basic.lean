import Mathlib.Algebra.GroupWithZero.Submonoid.Pointwise
import YoungDiagram.Chromosome.Lift
import YoungDiagram.Chromosome.Order

abbrev Variety := AddSubmonoid Chromosome

noncomputable def Variety.prime (v : Variety) : Variety :=
  v.map Chromosome.prime

lemma Variety.prime_def (v : Variety) :
  v.prime = v.map Chromosome.prime := rfl

open Finsupp Pointwise

lemma Variety.variety_prime_smul {v : Variety} {n : ℕ} :
    (n • v).prime = n • v.prime := by
  ext x; constructor <;> intro hx
  · obtain ⟨y, ⟨⟨z, ⟨hz, hyz : n • z = y⟩⟩, heq⟩⟩ := hx
    refine ⟨z.prime, ⟨?_, (?_ : n • z.prime = x)⟩⟩
    · use z
    · rw [← map_nsmul, hyz, heq]
  · obtain ⟨y, ⟨⟨z, ⟨hz, hyz⟩⟩, heq : n • y = x⟩⟩ := hx
    refine ⟨n • z, ⟨?_, ?_⟩⟩
    · use z, hz; rfl
    · rw [map_nsmul, hyz, heq]

lemma Variety.neg_mem_smul_iff {v : Variety} {n : ℕ} {X : Chromosome}
    (hv : ∀ {Y}, Y ∈ v ↔ -Y ∈ v) : X ∈ n • v ↔ - X ∈ n • v := by
  rw [AddSubmonoid.mem_smul_pointwise_iff_exists,
    AddSubmonoid.mem_smul_pointwise_iff_exists]
  constructor <;> rintro ⟨Y, ⟨hY, hXY⟩⟩
  · refine ⟨- Y, ⟨hv.1 hY, ?_⟩⟩
    rw [← Chromosome.neg_smul, hXY]
  · refine ⟨- Y, ⟨hv.1 hY, ?_⟩⟩
    rw [← Chromosome.neg_smul, hXY, neg_neg]

namespace Chromosome

lemma signature_filter_le (X : Chromosome) (p : Gene → Prop) [DecidablePred p] :
    signature (X.filter p) ≤ X.signature := by
  induction X using Finsupp.induction
  · rw [filter_zero]
  · expose_names
    rw [filter_add, map_add, map_add]
    refine add_le_add ?_ h_2
    by_cases ha : p a
    · rwa [filter_single_of_pos]
    · rw [filter_single_of_neg, map_zero]
      · exact signature_nonneg _
      exact ha

section IsFiltered

variable {p : Gene → Prop} [DecidablePred p] {X : Chromosome}

variable (p X) in
def IsFiltered : Prop := X.filter p = X

lemma IsFiltered_def : X.IsFiltered p ↔ X.filter p = X := .rfl

lemma IsFiltered_def' : X.IsFiltered p ↔ ∀ g ∈ X.support, p g := by
  simp [IsFiltered_def, filter_eq_self_iff]

lemma IsFiltered_zero : IsFiltered p 0 := by
  simp only [IsFiltered, filter_zero]

lemma IsFiltered_single {g : Gene} {n : ℕ} (hn : n ≠ 0) :
    IsFiltered p (single g n) ↔ p g := by
  rw [IsFiltered_def', support_single _ hn]
  exact List.forall_mem_singleton

lemma IsFiltered_filter {q : Gene → Prop} [DecidablePred q]
    (h : X.IsFiltered p) : IsFiltered p (X.filter q) := by
  rw [IsFiltered_def'] at h ⊢
  exact fun _ hg ↦ h _ ((Finset.filter_subset ..) hg)

lemma IsFiltered_add_single {g : Gene} {n : ℕ} (hn : 1 ≤ n) :
    IsFiltered p (X + single g n) ↔ X.IsFiltered p ∧ p g := by
  constructor <;> intro h
  · by_cases hg : p g
    · simp only [IsFiltered, filter_add, hg, filter_single_of_pos, add_left_inj] at h
      exact ⟨h, hg⟩
    · simp only [IsFiltered, filter_add, hg, not_false_eq_true, filter_single_of_neg,
      add_zero] at h
      apply_fun signature at h
      have := h ▸ (signature_filter_le X p)
      rw [map_add, signature_single g.rank_pos,
        add_le_iff_nonpos_right, Prod.le_def] at this
      change n * g.signature.1 ≤ 0 ∧ n * g.signature.2 ≤ 0 at this
      exact absurd ⟨nonpos_of_mul_nonpos_right this.1 (Rat.natCast_pos.2 hn),
        nonpos_of_mul_nonpos_right this.2 (Rat.natCast_pos.2 hn)⟩
        (not_le_of_gt g.signature_pos)
  · simp [IsFiltered, h, IsFiltered_def.1 h.1]

lemma IsFiltered_iff_add {X Y : Chromosome} :
    (X + Y).IsFiltered p ↔ X.IsFiltered p ∧ Y.IsFiltered p := by
  induction Y using Finsupp.induction with
  | zero =>
    rw [add_zero]
    exact (and_iff_left_of_imp fun _ ↦ IsFiltered_zero).symm
  | single_add g' n f hg' hn hf =>
    rw [add_comm _ f, ← add_assoc, IsFiltered_add_single
      (Nat.one_le_iff_ne_zero.2 hn), hf, IsFiltered_add_single
      (Nat.one_le_iff_ne_zero.2 hn)]
    tauto

lemma IsFiltered_iff_nsmul {n : ℕ} (hn : n ≠ 0) :
    (n • X).IsFiltered p ↔ X.IsFiltered p := by
  induction n using Nat.twoStepInduction with
  | zero => tauto
  | one => rw [one_nsmul]
  | more m _ hm =>
    specialize hm (by omega)
    change ((m + 1 + 1) • X).IsFiltered p ↔ _
    rw [add_nsmul, one_nsmul, IsFiltered_iff_add, hm]
    tauto

lemma IsFiltered_sub (Y : Chromosome) (hX : X.IsFiltered p) :
    (X - Y).IsFiltered p := by
  rw [IsFiltered_def'] at hX ⊢
  refine fun h hh ↦ hX h ?_
  rw [Finsupp.mem_support_iff] at hh ⊢
  refine fun hXh ↦ hh ?_
  simp only [Finsupp.tsub_apply, hXh]; omega

variable (p) in
def LiftStable : Prop :=
  ∀ g : Gene, p g ↔ p ⟨g.rank + 1, g.type, Nat.le_add_left 1 g.rank⟩

lemma IsFiltered_iff_lift (hp : LiftStable p) :
    X.lift.IsFiltered p ↔ X.IsFiltered p := by
  constructor <;> intro h
  · induction X using Finsupp.induction
    · exact IsFiltered_zero
    · expose_names
      rw [map_add, IsFiltered_iff_add] at h
      specialize h_3 h.2
      refine IsFiltered_iff_add.2 ⟨?_, h_3⟩
      replace h := h.1
      simp only [lift_def, liftGene, smul_dite, Nat.add_eq_zero_iff, one_ne_zero, and_false,
        ↓reduceDIte, smul_single, smul_eq_mul, mul_one, single_zero, sum_single_index] at h
      rw [IsFiltered_single h_2] at h ⊢
      exact (hp _).2 h
  · induction X using Finsupp.induction
    · exact IsFiltered_zero
    · expose_names
      rw [map_add, IsFiltered_iff_add]
      rw [IsFiltered_iff_add] at h
      refine ⟨?_, h_3 h.2⟩
      replace h := h.1
      simp only [lift_def, liftGene, smul_dite, Nat.add_eq_zero_iff, one_ne_zero, and_false,
        ↓reduceDIte, smul_single, smul_eq_mul, mul_one, single_zero, sum_single_index]
      rw [IsFiltered_single h_2] at h ⊢
      exact (hp _).1 h

lemma IsFiltered_iff_iterate_lift {k : ℕ} (hp : LiftStable p) :
    (lift^[k] X).IsFiltered p ↔ X.IsFiltered p := by
  induction k with
  | zero => rfl
  | succ n hn => rwa [Function.iterate_succ_apply', IsFiltered_iff_lift hp]

variable (p) in
def varietyOfFilter : Variety where
  carrier := {X : Chromosome | X.IsFiltered p}
  add_mem' ha hb := IsFiltered_iff_add.2 ⟨ha, hb⟩
  zero_mem' := IsFiltered_zero

lemma mem_varietyOfFilter_iff :
  X ∈ varietyOfFilter p ↔ X.IsFiltered p := .rfl

lemma prime_varietyOfFilter (hp : LiftStable p) :
    (varietyOfFilter p).prime = varietyOfFilter p := by
  refine le_antisymm ?_ ?_ <;> intro x hx
  · rw [Variety.prime_def, AddSubmonoid.mem_map] at hx
    rcases hx with ⟨y, ⟨h1, h2⟩⟩
    rw [mem_varietyOfFilter_iff, ← h2]
    induction y using Finsupp.induction generalizing x
    · exact IsFiltered_zero
    · expose_names
      rw [mem_varietyOfFilter_iff, IsFiltered_iff_add] at h1
      rw [map_add, IsFiltered_iff_add]
      refine ⟨?_, h_2 h1.2 rfl⟩
      simp only [prime_def, primeGene, smul_dite, nsmul_zero, smul_single, smul_eq_mul, mul_one,
        single_zero, dite_eq_ite, ite_self, sum_single_index]
      split_ifs with h
      · exact IsFiltered_zero
      · rw [IsFiltered_single h_1] at h1 ⊢
        rw [hp]
        convert h1.1
        refine Nat.sub_add_cancel a.rank_pos
  · rw [Variety.prime_def, AddSubmonoid.mem_map]
    use x.lift
    refine ⟨?_, prime_lift_leftInverse x⟩
    exact (IsFiltered_iff_lift hp).2 hx

lemma prime_mem_varietyOfFilter {X : Chromosome} (hp : LiftStable p)
    (hX : X ∈ varietyOfFilter p) : X.prime ∈ varietyOfFilter p :=
  ((congrArg (prime X ∈ ·) (prime_varietyOfFilter hp).symm)).mpr ⟨X, ⟨hX, rfl⟩⟩

noncomputable def prime_on_varietyOfFilter (hp : LiftStable p) (X : varietyOfFilter p) :
    varietyOfFilter p := ⟨X.1.prime, prime_mem_varietyOfFilter hp X.2⟩

lemma prime_on_varietyOfFilter_iterate (hp : LiftStable p) (X : varietyOfFilter p) (k : ℕ) :
    ((prime_on_varietyOfFilter hp)^[k] X).1 = Chromosome.prime^[k] X := by
  unfold prime_on_varietyOfFilter
  induction k with
  | zero => rw [Function.iterate_zero_apply, Function.iterate_zero_apply]
  | succ n hn => simp_rw [Function.iterate_succ_apply', hn]

lemma prime_mem_varietyOfFilter_iterate {X : Chromosome} (hp : LiftStable p) {k : ℕ}
    (hX : X ∈ varietyOfFilter p) : Chromosome.prime^[k] X ∈ varietyOfFilter p := by
  convert ((prime_on_varietyOfFilter hp)^[k] ⟨X, hX⟩).2
  exact (prime_on_varietyOfFilter_iterate hp ⟨X, hX⟩ k).symm

lemma filter_mem_smul_varietyOfFilter (q : Gene → Prop) [DecidablePred q]
  {n : ℕ} (h : X ∈ n • (varietyOfFilter p)) :
    X.filter q ∈ n • (varietyOfFilter p) := by
  obtain ⟨Y, ⟨h1, h2 : n • Y = X⟩⟩ := h
  refine ⟨Y.filter q, IsFiltered_filter h1, (?_ : n • (Y.filter q) = X.filter q)⟩
  rw [← h2, filter_smul]

end IsFiltered

end Chromosome

namespace Variety

open Chromosome

section sigma

variable {v v₁ v₂ : Variety}

/--
A Variety `v` is rank-one signature injective if any two elements of `v` whose
rank-1 parts share a signature have equal rank-1 parts.
-/
def RankOneSigInj (v : Variety) : Prop :=
  ∀ {X Y : Chromosome}, X ∈ v → Y ∈ v →
    (X.below 1).signature = (Y.below 1).signature → X.below 1 = Y.below 1

/--
A pair `(v₁, v₂)` of varieties is a sigma-pair if `Chromosome.prime` swaps them
and each side is rank-one signature injective. In a sigma-pair, the sigma
sequence (the signature of every prime iterate) uniquely determines an element
on either side; see `SigmaPair.sigmaUnique_left` and `SigmaPair.sigmaUnique_right`.
-/
structure SigmaPair (v₁ v₂ : Variety) : Prop where
  prime_left : v₁.prime ≤ v₂
  prime_right : v₂.prime ≤ v₁
  rankOne_left : RankOneSigInj v₁
  rankOne_right : RankOneSigInj v₂

def SigmaPair.symm (h : SigmaPair v₁ v₂) : SigmaPair v₂ v₁ where
  prime_left := h.prime_right
  prime_right := h.prime_left
  rankOne_left := h.rankOne_right
  rankOne_right := h.rankOne_left

/--
A Variety is sigma-unique if its elements are determined by their sigma
sequence (the signature of every prime iterate).
-/
def SigmaUnique (v : Variety) : Prop :=
  ∀ {A B : Chromosome}, A ∈ v → B ∈ v →
    (∀ k, (.prime^[k] A).signature = (.prime^[k] B).signature) → A = B

namespace RankOneSigInj

lemma mono {v₁ v₂ : Variety} (h : v₁ ≤ v₂) (hv : RankOneSigInj v₂) :
    RankOneSigInj v₁ :=
  fun hX hY heq ↦ hv (h hX) (h hY) heq

lemma below_one_eq_of_sig_eq (hv : RankOneSigInj v) {A B : Chromosome}
    (hA : A ∈ v) (hB : B ∈ v) (hsig : A.signature = B.signature)
    (habove : A.above 1 = B.above 1) : A.below 1 = B.below 1 := by
  refine hv hA hB ?_
  rwa [congr_arg signature (A.rank_decomposition 1), congr_arg signature
    (B.rank_decomposition 1), map_add, map_add, congr_arg signature habove,
    add_right_cancel_iff] at hsig

lemma eq_of_prime_eq_sig_eq (hv : RankOneSigInj v) {A B : Chromosome}
    (hA : A ∈ v) (hB : B ∈ v) (hprime : A.prime = B.prime)
    (hsig : A.signature = B.signature) : A = B := by
  have habove := above_one_eq_of_prime_eq hprime
  rw [rank_decomposition A 1, habove,
    RankOneSigInj.below_one_eq_of_sig_eq hv hA hB hsig habove, ← rank_decomposition]

end RankOneSigInj

namespace SigmaPair

lemma sigmaUnique_left (h : SigmaPair v₁ v₂) : SigmaUnique v₁ := by
  suffices key : ∀ n, ∀ A B : Chromosome,
      (A.maxRank ⊔ B.maxRank) ≤ n →
      ((A ∈ v₁ ∧ B ∈ v₁) ∨ (A ∈ v₂ ∧ B ∈ v₂)) →
      (∀ k, (.prime^[k] A).signature = (.prime^[k] B).signature) →
      A = B from fun _ _ hA hB heq ↦ key _ _ _ le_rfl (Or.inl ⟨hA, hB⟩) heq
  intro n
  induction n with
  | zero =>
    intro _ _ hn _ _
    obtain ⟨hAr, hBr⟩ := max_le_iff.1 hn
    rw [maxRank_eq_zero (Nat.le_zero.1 hAr), maxRank_eq_zero (Nat.le_zero.1 hBr)]
  | succ n ih =>
    intro A B hn hAB hk
    have hsig0 : signature A = signature B := hk 0
    by_cases hA0 : A = 0
    · rw [hA0, map_zero] at hsig0
      rw [hA0, signature_eq_zero hsig0.symm]
    have hB0 : B ≠ 0 := fun hB0 ↦
      hA0 <| signature_eq_zero <| by rw [hsig0, hB0, map_zero]
    have hprime_mem :
        (A.prime ∈ v₁ ∧ B.prime ∈ v₁) ∨ (A.prime ∈ v₂ ∧ B.prime ∈ v₂) := by
      rcases hAB with ⟨hAv, hBv⟩ | ⟨hAv, hBv⟩
      · exact Or.inr ⟨h.prime_left ⟨A, hAv, rfl⟩, h.prime_left ⟨B, hBv, rfl⟩⟩
      · exact Or.inl ⟨h.prime_right ⟨A, hAv, rfl⟩, h.prime_right ⟨B, hBv, rfl⟩⟩
    have hprime_eq : A.prime = B.prime := by
      refine ih A.prime B.prime ?_ hprime_mem ?_
      · have hAlt := maxRank_prime_lt hA0
        have hBlt := maxRank_prime_lt hB0
        omega
      · intro k
        rw [← Function.iterate_succ_apply, ← Function.iterate_succ_apply]
        exact hk (k + 1)
    rcases hAB with ⟨hAv, hBv⟩ | ⟨hAv, hBv⟩
    · exact RankOneSigInj.eq_of_prime_eq_sig_eq h.rankOne_left hAv hBv hprime_eq hsig0
    · exact RankOneSigInj.eq_of_prime_eq_sig_eq h.rankOne_right hAv hBv hprime_eq hsig0

lemma sigmaUnique_right (h : SigmaPair v₁ v₂) : SigmaUnique v₂ :=
  h.symm.sigmaUnique_left

end SigmaPair

/--
Promote sigma-uniqueness on a Variety to a `PartialOrder` instance on its
subtype, induced from the dominance order on chromosomes.
-/
@[reducible]
def SigmaUnique.partialOrder (hv : SigmaUnique v) : PartialOrder v where
  le_antisymm A B hAB hBA := Subtype.val_injective <|
    hv A.2 B.2 fun k ↦ le_antisymm (hAB k) (hBA k)

end sigma

end Variety
