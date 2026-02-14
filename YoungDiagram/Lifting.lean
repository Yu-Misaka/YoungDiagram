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
    cases h with
    | @type1 ε hε m n hle hm =>
      have le1 := Nat.add_le_add_right hle k
      have le2 : 1 ≤ m + k := by omega
      rw [← Subtype.val_inj, AddSubmonoid.coe_add, Pi.X1_eq hε hle hm,
        lift_prime, iterate_map_add, iterate_map_add, lift_iterate_ofRank (by omega),
        lift_iterate_ofRank (by omega), ← Pi.X1_eq hε le1 le2] at X_def
      replace U_def : U = Gene.ofRank (m - 1) (-ε) + Gene.ofRank (n + 1) ε + γ := by
        rwa [← Subtype.val_inj, AddSubmonoid.coe_add, Pi.Y1_eq hε hle hm] at U_def
      set Zk := Pi.Y1 hε le1 le2 with Zk_def
      set Z : Chromosome := Zk + (lift^[k] γ + (X.below k)) with Z_def
      have mem1 : lift^[k] γ + (X.below k) ∈ Pi :=
        add_mem (IsPolarized_iff_iterate_lift.2 γ.2) (IsPolarized_filter hX)
      have hZ : Z ∈ Pi := add_mem (SetLike.coe_mem _) mem1
      refine ⟨Z, hZ, ⟨?_, ?_, ?_⟩⟩
      · convert Pi.Step.mk (Pi.X1 hε le1 le2) Zk ⟨lift^[k] γ + (X.below k), mem1⟩
          (Pi.Primitive.type1 ε hε le1 le2)
        nth_rw 1 [X_def, AddSubmonoid.coe_add, add_assoc]
      · rw [Z_def, iterate_map_add, iterate_map_add, prime_lift_leftInverse_iterate k,
          prime_below le_rfl, add_zero, Zk_def, Pi.Y1_eq, iterate_map_add,
          prime_iterate_ofRank, prime_iterate_ofRank, U_def, add_left_inj]
        congr 2 <;> omega
      · intro i hi
        rw [X_def, Z_def, add_assoc, iterate_map_add, iterate_map_add (x := Zk.1),
          map_add, map_add, add_left_inj, Zk_def]
        exact mutation_type1_iterate_signature_eq hε hle hm i k hi
    | @type2 ε hε m n hle hm =>
      sorry
    | @type3 ε hε m n hle hm =>
      sorry

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
    have hψ : ψ 0 k = Pi := congrArg Label (Function.iterate_fixed rfl _)
    have hφ : φ 0 = Pi := rfl
    have hXk := Label.prime_iterate_zero ▸ Label.prime_eq_iterate ▸ (mem_prime_iterate hX (k := k))
    rw [hψ] at hU
    rw [hφ] at hX
    have hMu' : Step 0 ⟨Chromosome.prime^[k] X, hXk⟩ ⟨U, hU⟩ := by
      convert hMu
      symm; exact Function.iterate_fixed rfl _
    exact Pi_mutation_lifting hX hU hMu'
  | 1 => sorry
  | 2 => sorry
  | 3 => sorry
  | 4 => sorry

end
