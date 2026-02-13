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
  generalize Xk_def : (⟨Chromosome.prime^[k] X, Pi_mem_Xk hX⟩ : Label 0) = Xk at hMu
  generalize U_def : (⟨U, hU⟩ : Label 0) = U' at hMu
  cases hMu with
  | mk α β γ h =>
    cases h with
    | @type1 ε hε m n hle hm =>
      apply_fun (·.1) at Xk_def U_def
      rw [AddSubmonoid.coe_add, Pi.X1_eq hε hle hm] at Xk_def
      rw [AddSubmonoid.coe_add, Pi.Y1_eq hε hle hm] at U_def
      set Zk : Chromosome := Gene.ofRank (m + k - 1) (- ε) + Gene.ofRank (n + k + 1) ε with Zk_def
      set Z : Chromosome := Zk + γ with Z_def
      have hZ : Z ∈ Pi := by
        rw [Z_def, Zk_def]
        refine add_mem (add_mem ?_ ?_) γ.2 <;> rw [mem_Pi_iff]
        · exact IsPolarized_ofRank' <| GeneType.ne_nonPolarized_iff_neg_ne.1 hε
        · exact IsPolarized_ofRank' hε
      refine ⟨Z, hZ, ⟨?_, ?_, ?_⟩⟩
      <;> sorry
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
