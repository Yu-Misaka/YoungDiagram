import YoungDiagram.Mutations

open Chromosome Variety Mutation

namespace Variety

section Pi

variable {k : ℕ} {X U : Chromosome} (hX : X ∈ Pi) (hU : U ∈ Pi)

include hX in
private lemma Pi_mem_Xk : Chromosome.prime^[k] X ∈ Pi :=
  (Function.iterate_fixed prime_Pi _) ▸ (mem_prime_iterate hX (k := k))

variable (hMu : Step 0 ⟨Chromosome.prime^[k] X, Pi_mem_Xk hX⟩ ⟨U, hU⟩)

include hU hMu in
private lemma Pi_mutation_lifting : ∃ (Z : Chromosome) (hZ : Z ∈ Pi),
    Step 0 ⟨X, hX⟩ ⟨Z, hZ⟩ ∧
    Chromosome.prime^[k] Z = U ∧
    ∀ i ≤ k, signature (Chromosome.prime^[i] X) = signature (Chromosome.prime^[i] Z) := by
  generalize X_def : (⟨Chromosome.prime^[k] X, Pi_mem_Xk hX⟩ : Label 0) = Xk at hMu
  generalize U_def : (⟨U, hU⟩ : Label 0) = U' at hMu
  cases hMu with
  | mk α β γ h =>
    have mem1 : lift^[k] γ + (X.below k) ∈ Pi :=
      add_mem (IsPolarized_iff_iterate_lift.2 γ.2) (IsPolarized_filter hX)
    cases h with
    | @type1 ε hε m n hle hm =>
      have le1 := Nat.add_le_add_right hle k
      have le2 : 1 ≤ m + k := Nat.le_add_right_of_le hm
      rw [← Subtype.val_inj, AddSubmonoid.coe_add, Pi.X1_eq hε hle hm,
        lift_prime, iterate_map_add, iterate_map_add, lift_iterate_ofRank (by omega),
        lift_iterate_ofRank (by omega), ← Pi.X1_eq hε le1 le2, add_assoc] at X_def
      replace U_def : U = Gene.ofRank (m - 1) (-ε) + Gene.ofRank (n + 1) ε + γ := by
        rwa [← Subtype.val_inj, AddSubmonoid.coe_add, Pi.Y1_eq hε hle hm] at U_def
      set ζ := Pi.Y1 hε le1 le2 with ζ_def
      set Z : Chromosome := ζ + (lift^[k] γ + (X.below k)) with Z_def
      have hZ : Z ∈ Pi := add_mem (SetLike.coe_mem _) mem1
      refine ⟨Z, hZ, ⟨?_, ?_, ?_⟩⟩
      · convert Pi.Step.mk (Pi.X1 hε le1 le2) ζ ⟨lift^[k] γ + (X.below k), mem1⟩
          (Pi.Primitive.type1 ε hε le1 le2)
      · rw [Z_def, iterate_map_add, iterate_map_add, prime_lift_leftInverse_iterate k,
          prime_below le_rfl, add_zero, ζ_def, Pi.Y1_eq, iterate_map_add,
          prime_iterate_ofRank, prime_iterate_ofRank, U_def, add_left_inj]
        congr 2 <;> omega
      · intro i hi
        rw [X_def, Z_def, iterate_map_add, iterate_map_add (x := ζ.1),
          map_add, map_add, add_left_inj, ζ_def]
        exact mutation_type1_iterate_signature_eq hε hle hm i k hi
    | @type2 ε hε m n hle hm =>
      have le1 := Nat.add_le_add_right hle k
      have le2 : 1 < m + k := Nat.lt_add_right k hm
      rw [← Subtype.val_inj, AddSubmonoid.coe_add, Pi.X2_eq hε hle hm,
        lift_prime, iterate_map_add, iterate_map_add, lift_iterate_ofRank (by omega),
        lift_iterate_ofRank (by omega), ← Pi.X2_eq hε le1 le2, add_assoc] at X_def
      replace U_def : U = Gene.ofRank (m - 2) ε + Gene.ofRank (n + 2) ε + γ := by
        rwa [← Subtype.val_inj, AddSubmonoid.coe_add, Pi.Y2_eq hε hle hm] at U_def
      set ζ := Pi.Y2 hε le1 le2 with ζ_def
      set Z : Chromosome := ζ + (lift^[k] γ + (X.below k)) with Z_def
      have hZ : Z ∈ Pi := add_mem (SetLike.coe_mem _) mem1
      refine ⟨Z, hZ, ⟨?_, ?_, ?_⟩⟩
      · convert Pi.Step.mk (Pi.X2 hε le1 le2) ζ ⟨lift^[k] γ + (X.below k), mem1⟩
          (Pi.Primitive.type2 ε hε le1 le2)
      · rw [Z_def, iterate_map_add, iterate_map_add, prime_lift_leftInverse_iterate k,
          prime_below le_rfl, add_zero, ζ_def, Pi.Y2_eq, iterate_map_add,
          prime_iterate_ofRank, prime_iterate_ofRank, U_def, add_left_inj]
        congr 2 <;> omega
      · intro i hi
        rw [X_def, Z_def, iterate_map_add, iterate_map_add (x := ζ.1),
          map_add, map_add, add_left_inj, ζ_def]
        exact mutation_type2_iterate_signature_eq hε hle hm i k hi
    | @type3 ε hε m n hle hm =>
      have le1 := Nat.add_le_add_right hle k
      have le2 : 1 ≤ m + k := Nat.le_add_right_of_le hm
      have eq1 : Int.negOnePow k • ε ≠ .NonPolarized :=
        GeneType.ne_nonPolarized_iff_one_pow_smul_ne.1 hε
      rw [← Subtype.val_inj, AddSubmonoid.coe_add, Pi.X3_eq hε hle hm,
        lift_prime, iterate_map_add, iterate_map_add, lift_iterate_ofRank (by omega),
        lift_iterate_ofRank (by omega), ← Gene.ofRankAlt_shift_negOnePow_smul,
        ← Gene.ofRankAlt_shift_negOnePow_smul, GeneType.smul_neg,
        ← Pi.X3_eq eq1 le1 le2, add_assoc] at X_def
      replace U_def : U = Gene.ofRankAlt (m - 1) (-ε) + Gene.ofRankAlt (n + 1) ε + γ := by
        rwa [← Subtype.val_inj, AddSubmonoid.coe_add, Pi.Y3_eq] at U_def
      set ζ := Pi.Y3 eq1 le1 le2 with ζ_def
      set Z : Chromosome := ζ + (lift^[k] γ + (X.below k)) with Z_def
      have hZ : Z ∈ Pi := add_mem (SetLike.coe_mem _) mem1
      refine ⟨Z, hZ, ⟨?_, ?_, ?_⟩⟩
      · convert Pi.Step.mk (Pi.X3 eq1 le1 le2) ζ ⟨lift^[k] γ + (X.below k), mem1⟩
          (Pi.Primitive.type3 (Int.negOnePow k • ε) eq1 le1 le2)
      · rw [Z_def, iterate_map_add, iterate_map_add, prime_lift_leftInverse_iterate k,
          prime_below le_rfl, add_zero, ζ_def, Pi.Y3_eq, iterate_map_add,
          prime_iterate_ofRank, prime_iterate_ofRank, U_def, add_left_inj]
        congr 2
        · omega
        · rw [GeneType.smul_neg, GeneType.neg_one_pow_smul_smul, GeneType.smul_neg,
            Nat.cast_sub le2, Nat.cast_sub hm, Nat.cast_add]
          congr 2
          ring_nf
          rw [mul_comm, Int.negOnePow_add, Int.negOnePow_two_mul, mul_one]
        · omega
        · rw [GeneType.neg_one_pow_smul_smul, Nat.cast_add, Nat.cast_add, Nat.cast_add]
          ring_nf
          rw [mul_comm, Int.negOnePow_add, Int.negOnePow_two_mul, mul_one]
      · intro i hi
        rw [X_def, Z_def, iterate_map_add, iterate_map_add (x := ζ.1),
          map_add, map_add, add_left_inj, ζ_def, Pi.X3_eq, Pi.Y3_eq, ← GeneType.smul_neg]
        exact mutation_type3_iterate_signature_eq hε hle hm i k hi

end Pi

end Variety

noncomputable section

variable (idx : Fin 5) (k : ℕ)

private abbrev φ := Label idx
private abbrev ψ := Label (Label.prime^[k] idx)

variable {X U : Chromosome} (hX : X ∈ φ idx) (hU : U ∈ ψ idx k)

variable (hMu : Step (Label.prime^[k] idx) (Label.of_mem_prime_iterate hX) ⟨U, hU⟩)

include hU hMu in
lemma mutation_lifting : ∃ (Z : Chromosome) (hZ : Z ∈ φ idx),
    Step idx ⟨X, hX⟩ ⟨Z, hZ⟩ ∧
    Chromosome.prime^[k] Z = U ∧
    ∀ i ≤ k, signature (Chromosome.prime^[i] X) = signature (Chromosome.prime^[i] Z) := by
  match idx with
  | 0 =>
    replace hU : U ∈ Pi := ((congrArg (U ∈ ·)
      (congrArg Label Label.prime_iterate_zero).symm)).mpr hU
    have hXk := Label.prime_iterate_zero ▸ Label.prime_eq_iterate ▸
      (mem_prime_iterate hX (k := k))
    have hMu' : Step 0 ⟨Chromosome.prime^[k] X, hXk⟩ ⟨U, hU⟩ := by
      convert hMu
      exact Label.prime_iterate_zero.symm
    exact Pi_mutation_lifting hX hU hMu'
  | 1 => sorry
  | 2 => sorry
  | 3 => sorry
  | 4 => sorry

end
