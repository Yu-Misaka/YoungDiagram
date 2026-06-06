import YoungDiagram.Theorem6.CaseA

open Variety hiding prime prime_def
open Chromosome Sigma

/-! ## (15.10): X has no positive-negative gene pair of equal rank -/
/-- Dispatcher for Cases A and B of §15.10.
Case A is proved in `YoungDiagram.Theorem6.CaseA`; Case B is its sign-dual. -/
private lemma exists_mutation_le_fifteen_ten {m : ℕ}
    (ih : ∀ k, k < m + 2 → ∀ X Y : nPi k, X < Y →
      ∃ Z : Pi, Pi.Step X Z ∧ Z ≤ Y)
    (X Y : nPi (m + 2)) (hXY : X < Y)
    (hcommon : ¬∃ g : Gene, 0 < X.1.1 g ∧ 0 < Y.1.1 g)
    (hsigeq : ¬∃ k : ℕ, 0 < k ∧ prime^[k] Y ≠ 0 ∧ sigma X k = sigma Y k)
    (hXpn : ¬∃ (g h : Gene), g.rank = h.rank ∧
      g.type = .Positive ∧ h.type = .Negative ∧
      0 < X.1.1 g ∧ 0 < X.1.1 h) :
    ∃ Z : Pi, Pi.Step X Z ∧ Z ≤ Y := by
  by_cases ha : (sigma X 1).1 < (sigma Y 1).1
  · exact exists_mutation_le_fifteen_ten_caseA m ih X Y hXY hcommon hsigeq hXpn ha
  · have ha_eq : (sigma X 1).1 = (sigma Y 1).1 :=
      le_antisymm (le_iff_dominates.mp hXY.le 1).1 (le_of_not_gt ha)
    have hYprime_ne : prime Y ≠ 0 := by
      intro hYprime
      have hXprime_zero : prime X = 0 := by
        have hle1 := le_iff_dominates.mp hXY.le 1
        simp only [Function.iterate_one, hYprime, map_zero] at hle1
        exact signature_eq_zero (le_antisymm hle1 (signature_nonneg _))
      have hsig_all (k : ℕ):
          (prime^[k] X).signature = (prime^[k] Y).signature := by
        cases k with
        | zero => simpa only [sigma, Function.iterate_zero, id_eq] using
            sigma_zero_eq X Y hXY.le
        | succ k => simp only [Function.iterate_succ_apply, hXprime_zero,
            iterate_map_zero, map_zero, hYprime]
      exact (ne_of_lt hXY) <| Subtype.val_injective
        <| Subtype.val_injective <| sigmaUnique_Pi X.1.2 Y.1.2 hsig_all
    have hsig_ne : sigma X 1 ≠ sigma Y 1 := fun hsig ↦ hsigeq ⟨1, Nat.one_pos, hYprime_ne, hsig⟩
    have hb_ne : (sigma X 1).2 ≠ (sigma Y 1).2 := fun hb_eq ↦ hsig_ne (Prod.ext ha_eq hb_eq)
    have hb_lt : (sigma X 1).2 < (sigma Y 1).2 :=
      lt_of_le_of_ne (le_iff_dominates.mp hXY.le 1).2 hb_ne
    set Xd : nPi (m + 2) :=
      ⟨- X.1, by rw [Pi.neg_val, rank_neg, X.2]⟩ with Xd_def
    set Yd : nPi (m + 2) :=
      ⟨- Y.1, by rw [Pi.neg_val, rank_neg, Y.2]⟩ with Yd_def
    have hcommond : ¬∃ g : Gene, 0 < Xd.1.1 g ∧ 0 < Yd.1.1 g := by
      refine fun ⟨g, hgX, hgY⟩ ↦ hcommon ⟨- g, ?_, ?_⟩
      · rw [← neg_apply]
        convert hgX; rfl
      · rw [← neg_apply]
        convert hgY; rfl
    have hsigeqd : ¬∃ k : ℕ, 0 < k ∧ prime^[k] Yd ≠ 0 ∧
        sigma Xd k = sigma Yd k := by
      refine fun ⟨k, hkpos, hYd_ne, hsig⟩ ↦ hsigeq ⟨k, hkpos, ?_, ?_⟩
      · refine fun hYzero ↦ hYd_ne ?_
        rw [Pi.neg_val, ← prime_iterate_neg, hYzero, neg_zero]
      · have hsig_swap : (prime^[k] (- X)).signature.swap =
          (prime^[k] (- Y)).signature.swap := congrArg Prod.swap hsig
        rwa [← @prime_iterate_neg k X, ← @prime_iterate_neg k Y,
          signature_neg, signature_neg, Prod.swap_swap, Prod.swap_swap] at hsig_swap
    have hXpnd : ¬∃ (g h : Gene), g.rank = h.rank ∧
        g.type = .Positive ∧ h.type = .Negative ∧
        0 < Xd.1.1 g ∧ 0 < Xd.1.1 h := by
      refine fun ⟨g, h, hrank, hgpos, hhneg, hgX, hhX⟩ ↦
        hXpn ⟨- h, - g, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [Gene.neg_rank, hrank]
      · rw [Gene.neg_type, hhneg]; rfl
      · rw [Gene.neg_type, hgpos]; rfl
      · rw [← neg_apply]; convert hhX; rfl
      · rw [← neg_apply]; convert hgX; rfl
    have had : (sigma Xd 1).1 < (sigma Yd 1).1 := by
      change (prime^[1] (- X)).signature.1 <
        (prime^[1] (- Y)).signature.1
      rwa [← @prime_iterate_neg 1 X, ← @prime_iterate_neg 1 Y,
        signature_neg, signature_neg, Function.iterate_one,
        Prod.fst_swap, Prod.fst_swap]
    obtain ⟨W, hstepW, hWY⟩ := exists_mutation_le_fifteen_ten_caseA m ih Xd Yd
      (Pi.neg_lt_neg_iff.2 hXY) hcommond hsigeqd hXpnd had
    let Z : Pi := - W
    refine ⟨Z, ?_, ?_⟩
    · exact Pi.Step.of_neg (by simpa only [neg_neg, Z] using hstepW)
    · simpa only [neg_neg] using (Pi.neg_le_neg_iff (Y := - Y)).2 hWY

private lemma exists_mutation_le_rank_zero {X Y : nPi 0} (hXY : X < Y) :
    ∃ Z : Pi, Pi.Step X.1 Z ∧ Z ≤ Y.1 :=
  absurd ((rank_zero X.2).trans (rank_zero Y.2).symm) (ne_of_lt hXY)

private lemma exists_mutation_le_rank_one {X Y : nPi 1} (hXY : X < Y) :
    ∃ Z : Pi, Pi.Step X Z ∧ Z ≤ Y :=
  have hsig_le : signature X ≤ signature Y := hXY.le 0
  have hXsum : (signature X).1 + (signature X).2 = 1 := by
    rcases rank_one_pi_sig X.1.2 X.2 with h | h <;> simp only [h, zero_add, add_zero]
  have hYsum : (signature Y).1 + (signature Y).2 = 1 := by
    rcases rank_one_pi_sig Y.1.2 Y.2 with h | h <;> simp only [h, zero_add, add_zero]
  have hsig_eq : signature X = signature Y := by
    obtain ⟨h1_le, h2_le⟩ := Prod.le_def.1 hsig_le
    exact Prod.ext (h1_le.antisymm (by linarith [h2_le])) (h2_le.antisymm (by linarith [h1_le]))
  absurd (Pi_rank_one_eq_of_sig_eq X.1.2 Y.1.2 X.2 Y.2 hsig_eq) (ne_of_lt hXY)

/--
Proposition after (15.7) [Djoković 1982, p. 29]:
Let X, Y ∈ Π(n) with X < Y.  Then there exists a Π-mutation X → Z such that Z ≤ Y.
-/
theorem exists_mutation_le {n : ℕ} : ∀ (X Y : nPi n), X < Y →
    ∃ Z : Pi, Pi.Step X Z ∧ Z ≤ Y :=
  Nat.strongRecOn n fun n ih X Y hXY ↦
  match n with
  | 0 => exists_mutation_le_rank_zero hXY
  | 1 => exists_mutation_le_rank_one hXY
  | m + 2 => by
    by_cases hcommon : ∃ g : Gene, 0 < X.1.1 g ∧ 0 < Y.1.1 g
    · exact exists_mutation_le_shared_gene m ih X Y hXY hcommon
    · by_cases hsigeq : ∃ k : ℕ, 0 < k ∧ prime^[k] Y ≠ 0 ∧ sigma X k = sigma Y k
      · exact exists_mutation_le_disjoint_sigma_eq m ih X Y hXY hcommon hsigeq
      · by_cases hXpn : ∃ (g h : Gene), g.rank = h.rank ∧
            g.type = .Positive ∧ h.type = .Negative ∧ 0 < X.1.1 g ∧ 0 < X.1.1 h
        · exact exists_mutation_le_disjoint_pair X Y hXY hcommon hsigeq hXpn
        · exact exists_mutation_le_fifteen_ten ih X Y hXY hcommon hsigeq hXpn
