import YoungDiagram.Mutations.MixLambdaPi
import YoungDiagram.Mutations.MixPiLambda

open Variety hiding prime
open Chromosome

namespace MixPiLambda

variable {k : ℕ} {X U : Chromosome} (hX : X ∈ Mix (Pi, Lambda))

include hX

/-- For even `k`, `prime^[k] X ∈ Mix (Pi, Lambda)` if `X ∈ Mix (Pi, Lambda)`. -/
private lemma prime_iterate_mem_even (hk : Even k) :
    prime^[k] X ∈ Mix (Pi, Lambda) := by
  have := Variety.prime_mem_Mix_Pi_Lambda_iterate hX k
  rwa [if_pos hk] at this

/-- For odd `k`, `prime^[k] X ∈ Mix (Lambda, Pi)` if `X ∈ Mix (Pi, Lambda)`. -/
private lemma prime_iterate_mem_odd (hk : ¬ Even k) :
    prime^[k] X ∈ Mix (Lambda, Pi) := by
  have := Variety.prime_mem_Mix_Pi_Lambda_iterate hX k
  rwa [if_neg hk] at this

/-- Helper: `lift^[k] γ + X.below k ∈ Mix (Pi, Lambda)` for even `k`
when `γ ∈ Mix (Pi, Lambda)`. -/
private lemma lift_add_below_mem_even (hk : Even k)
    {γ : Chromosome} (hγ : γ ∈ Mix (Pi, Lambda)) :
    lift^[k] γ + X.below k ∈ Mix (Pi, Lambda) :=
  add_mem (Variety.lift_iterate_mem_Mix_Pi_Lambda (by rw [if_pos hk]; exact hγ))
    (Variety.below_mem_Mix_Pi_Lambda hX k)

/-- Helper: `lift^[k] γ + X.below k ∈ Mix (Pi, Lambda)` for odd `k`
when `γ ∈ Mix (Lambda, Pi)`. -/
private lemma lift_add_below_mem_odd (hk : ¬ Even k)
    {γ : Chromosome} (hγ : γ ∈ Mix (Lambda, Pi)) :
    lift^[k] γ + X.below k ∈ Mix (Pi, Lambda) :=
  add_mem (Variety.lift_iterate_mem_Mix_Pi_Lambda (by rw [if_neg hk]; exact hγ))
    (Variety.below_mem_Mix_Pi_Lambda hX k)

variable (hU : U ∈ Mix (Pi, Lambda))

include hU in
lemma mutation_lifting_even (hk : Even k)
    (hMu : MixPiLambda.Step ⟨prime^[k] X, prime_iterate_mem_even hX hk⟩ ⟨U, hU⟩) :
    ∃ (Z : Chromosome) (hZ : Z ∈ Mix (Pi, Lambda)),
      MixPiLambda.Step ⟨X, hX⟩ ⟨Z, hZ⟩ ∧
      prime^[k] Z = U ∧
      ∀ i ≤ k, signature (prime^[i] X) = signature (prime^[i] Z) := by
  -- Decompose `k = 2 * j` for use in the arithmetic.
  obtain ⟨j, hj⟩ : ∃ j, k = 2 * j :=
    ⟨k / 2, by have := Nat.even_iff.mp hk; omega⟩
  subst hj
  generalize X_def : (⟨prime^[2 * j] X, prime_iterate_mem_even hX hk⟩ :
    Mix (Pi, Lambda)) = Xk at hMu
  generalize U_def : (⟨U, hU⟩ : Mix (Pi, Lambda)) = U' at hMu
  cases hMu with
  | mk α β γ h =>
    have mem1 : lift^[2 * j] γ.1 + X.below (2 * j) ∈ Mix (Pi, Lambda) :=
      lift_add_below_mem_even hX hk γ.2
    cases h with
    | @type4 ε hε m n h_le =>
      have h_le' : m + j ≤ n + j := by omega
      have eqX1 : 2 * m + 1 + 2 * j = 2 * (m + j) + 1 := by ring
      have eqX2 : 2 * n + 1 + 2 * j = 2 * (n + j) + 1 := by ring
      rw [← Subtype.val_inj, AddSubmonoid.coe_add, MixPiLambda.X4_eq,
        lift_prime, iterate_map_add, iterate_map_add,
        lift_iterate_ofRank (by omega), lift_iterate_ofRank (by omega),
        eqX1, eqX2, ← MixPiLambda.X4_eq (h_le := h_le'), add_assoc] at X_def
      replace U_def : U = Gene.ofRank (2 * m) ε +
          Gene.ofRank (2 * n + 2) (-ε) + γ.1 := by
        rw [← Subtype.val_inj, AddSubmonoid.coe_add, MixPiLambda.Y4_eq] at U_def
        exact U_def
      set ζ := MixPiLambda.Y4 h_le' hε with ζ_def
      set Z : Chromosome := ζ.1 + (lift^[2 * j] γ.1 + X.below (2 * j)) with Z_def
      have hZ : Z ∈ Mix (Pi, Lambda) := add_mem (SetLike.coe_mem _) mem1
      refine ⟨Z, hZ, ⟨?_, ?_, ?_⟩⟩
      · convert MixPiLambda.Step.mk (MixPiLambda.X4 h_le') ζ
          ⟨lift^[2 * j] γ.1 + X.below (2 * j), mem1⟩
          (MixPiLambda.Primitive.type4 ε hε h_le')
        · nth_rw 1 [X_def, AddSubmonoid.coe_add]
        · nth_rw 1 [Z_def, AddSubmonoid.coe_add]
      · rw [Z_def, iterate_map_add, iterate_map_add,
          prime_lift_leftInverse_iterate (2 * j), prime_below le_rfl, add_zero,
          ζ_def, MixPiLambda.Y4_eq, iterate_map_add,
          prime_iterate_ofRank, prime_iterate_ofRank, U_def, add_left_inj]
        congr 2 <;> omega
      · intro i hi
        rw [X_def, Z_def, iterate_map_add, iterate_map_add (x := ζ.1),
          map_add, map_add, add_left_inj, ζ_def, MixPiLambda.X4_eq, MixPiLambda.Y4_eq,
          ← eqX1, ← eqX2]
        have eq3 : 2 * (m + j) = 2 * m + 2 * j := by ring
        have eq4 : 2 * (n + j) + 2 = 2 * n + 2 + 2 * j := by ring
        rw [eq3, eq4]
        exact mutation_type4_iterate_signature_eq (ε := ε) h_le i (2 * j) hi
    | @type5 ε hε m n h_le =>
      have h_le' : m + j ≤ n + j := by omega
      have eqX1 : 2 * m + 1 + 2 * j = 2 * (m + j) + 1 := by ring
      have eqX2 : 2 * n + 2 + 2 * j = 2 * (n + j) + 2 := by ring
      rw [← Subtype.val_inj, AddSubmonoid.coe_add, MixPiLambda.X5_eq,
        lift_prime, iterate_map_add, iterate_map_add,
        lift_iterate_ofRank (by omega), lift_iterate_ofRank (by omega),
        eqX1, eqX2, ← MixPiLambda.X5_eq (h_le := h_le') hε, add_assoc] at X_def
      replace U_def : U = Gene.ofRank (2 * m) ε +
          Gene.ofRank (2 * n + 3) GeneType.NonPolarized + γ.1 := by
        rw [← Subtype.val_inj, AddSubmonoid.coe_add, MixPiLambda.Y5_eq] at U_def
        exact U_def
      set ζ := MixPiLambda.Y5 h_le' hε with ζ_def
      set Z : Chromosome := ζ.1 + (lift^[2 * j] γ.1 + X.below (2 * j)) with Z_def
      have hZ : Z ∈ Mix (Pi, Lambda) := add_mem (SetLike.coe_mem _) mem1
      refine ⟨Z, hZ, ⟨?_, ?_, ?_⟩⟩
      · convert MixPiLambda.Step.mk (MixPiLambda.X5 h_le' hε) ζ
          ⟨lift^[2 * j] γ.1 + X.below (2 * j), mem1⟩
          (MixPiLambda.Primitive.type5 ε hε h_le')
        · nth_rw 1 [X_def, AddSubmonoid.coe_add]
        · nth_rw 1 [Z_def, AddSubmonoid.coe_add]
      · rw [Z_def, iterate_map_add, iterate_map_add,
          prime_lift_leftInverse_iterate (2 * j), prime_below le_rfl, add_zero,
          ζ_def, MixPiLambda.Y5_eq, iterate_map_add,
          prime_iterate_ofRank, prime_iterate_ofRank, U_def, add_left_inj]
        congr 2 <;> omega
      · intro i hi
        rw [X_def, Z_def, iterate_map_add, iterate_map_add (x := ζ.1),
          map_add, map_add, add_left_inj, ζ_def, MixPiLambda.X5_eq, MixPiLambda.Y5_eq,
          ← eqX1, ← eqX2]
        have eq3 : 2 * (m + j) = 2 * m + 2 * j := by ring
        have eq4 : 2 * (n + j) + 3 = 2 * n + 3 + 2 * j := by ring
        rw [eq3, eq4]
        exact mutation_type5_iterate_signature_eq h_le i (2 * j) hi
    | @type6 ε hε m n h_le =>
      have h_le' : m + j ≤ n + j := by omega
      have eqX1 : 2 * m + 2 + 2 * j = 2 * (m + j) + 2 := by ring
      have eqX2 : 2 * n + 3 + 2 * j = 2 * (n + j) + 3 := by ring
      rw [← Subtype.val_inj, AddSubmonoid.coe_add, MixPiLambda.X6_eq,
        lift_prime, iterate_map_add, iterate_map_add,
        lift_iterate_ofRank (by omega), lift_iterate_ofRank (by omega),
        eqX1, eqX2, ← MixPiLambda.X6_eq (h_le := h_le') hε, add_assoc] at X_def
      replace U_def : U = Gene.ofRank (2 * m + 1) GeneType.NonPolarized +
          Gene.ofRank (2 * n + 4) ε + γ.1 := by
        rw [← Subtype.val_inj, AddSubmonoid.coe_add, MixPiLambda.Y6_eq] at U_def
        exact U_def
      set ζ := MixPiLambda.Y6 h_le' hε with ζ_def
      set Z : Chromosome := ζ.1 + (lift^[2 * j] γ.1 + X.below (2 * j)) with Z_def
      have hZ : Z ∈ Mix (Pi, Lambda) := add_mem (SetLike.coe_mem _) mem1
      refine ⟨Z, hZ, ⟨?_, ?_, ?_⟩⟩
      · convert MixPiLambda.Step.mk (MixPiLambda.X6 h_le' hε) ζ
          ⟨lift^[2 * j] γ.1 + X.below (2 * j), mem1⟩
          (MixPiLambda.Primitive.type6 ε hε h_le')
        · nth_rw 1 [X_def, AddSubmonoid.coe_add]
        · nth_rw 1 [Z_def, AddSubmonoid.coe_add]
      · rw [Z_def, iterate_map_add, iterate_map_add,
          prime_lift_leftInverse_iterate (2 * j), prime_below le_rfl, add_zero,
          ζ_def, MixPiLambda.Y6_eq, iterate_map_add,
          prime_iterate_ofRank, prime_iterate_ofRank, U_def, add_left_inj]
        congr 2 <;> omega
      · intro i hi
        rw [X_def, Z_def, iterate_map_add, iterate_map_add (x := ζ.1),
          map_add, map_add, add_left_inj, ζ_def, MixPiLambda.X6_eq, MixPiLambda.Y6_eq,
          ← eqX1, ← eqX2]
        have eq3 : 2 * (m + j) + 1 = 2 * m + 1 + 2 * j := by ring
        have eq4 : 2 * (n + j) + 4 = 2 * n + 4 + 2 * j := by ring
        rw [eq3, eq4]
        exact mutation_type6_iterate_signature_eq h_le i (2 * j) hi
    | @type7 ε hε m n h_le =>
      have h_le' : m + j ≤ n + j := by omega
      have eqX1 : 2 * m + 2 + 2 * j = 2 * (m + j) + 2 := by ring
      have eqX2 : 2 * n + 2 + 2 * j = 2 * (n + j) + 2 := by ring
      rw [← Subtype.val_inj, AddSubmonoid.coe_add, MixPiLambda.X7_eq,
        lift_prime, iterate_map_add, iterate_map_add,
        lift_iterate_ofRank (by omega), lift_iterate_ofRank (by omega),
        eqX1, eqX2, ← MixPiLambda.X7_eq (h_le := h_le') hε, add_assoc] at X_def
      replace U_def : U = Gene.ofRank (2 * m + 1) GeneType.NonPolarized +
          Gene.ofRank (2 * n + 3) GeneType.NonPolarized + γ.1 := by
        rw [← Subtype.val_inj, AddSubmonoid.coe_add, MixPiLambda.Y7_eq] at U_def
        exact U_def
      set ζ : Mix (Pi, Lambda) := MixPiLambda.Y7 h_le' with ζ_def
      set Z : Chromosome := ζ.1 + (lift^[2 * j] γ.1 + X.below (2 * j)) with Z_def
      have hZ : Z ∈ Mix (Pi, Lambda) := add_mem (SetLike.coe_mem _) mem1
      refine ⟨Z, hZ, ⟨?_, ?_, ?_⟩⟩
      · convert MixPiLambda.Step.mk (MixPiLambda.X7 h_le' hε) ζ
          ⟨lift^[2 * j] γ.1 + X.below (2 * j), mem1⟩
          (MixPiLambda.Primitive.type7 ε hε h_le')
        · nth_rw 1 [X_def, AddSubmonoid.coe_add]
        · nth_rw 1 [Z_def, AddSubmonoid.coe_add]
      · rw [Z_def, iterate_map_add, iterate_map_add,
          prime_lift_leftInverse_iterate (2 * j), prime_below le_rfl, add_zero,
          ζ_def, MixPiLambda.Y7_eq, iterate_map_add,
          prime_iterate_ofRank, prime_iterate_ofRank, U_def, add_left_inj]
        congr 2 <;> omega
      · intro i hi
        rw [X_def, Z_def, iterate_map_add, iterate_map_add (x := ζ.1),
          map_add, map_add, add_left_inj, ζ_def, MixPiLambda.X7_eq, MixPiLambda.Y7_eq,
          ← eqX1, ← eqX2]
        have eq3 : 2 * (m + j) + 1 = 2 * m + 1 + 2 * j := by ring
        have eq4 : 2 * (n + j) + 3 = 2 * n + 3 + 2 * j := by ring
        rw [eq3, eq4]
        exact mutation_type7_iterate_signature_eq (ε := ε) h_le i (2 * j) hi
    | @type8 ε hε m n h_le =>
      have h_le' : m + j ≤ n + j := by omega
      have eqX1 : 2 * m + 2 + 2 * j = 2 * (m + j) + 2 := by ring
      have eqX2 : 2 * n + 2 + 2 * j = 2 * (n + j) + 2 := by ring
      rw [← Subtype.val_inj, AddSubmonoid.coe_add, MixPiLambda.X8_eq,
        lift_prime, iterate_map_add, iterate_map_add,
        lift_iterate_ofRank (by omega), lift_iterate_ofRank (by omega),
        eqX1, eqX2, ← MixPiLambda.X8_eq (h_le := h_le') hε, add_assoc] at X_def
      replace U_def : U = Gene.ofRank (2 * m) ε +
          Gene.ofRank (2 * n + 4) ε + γ.1 := by
        rw [← Subtype.val_inj, AddSubmonoid.coe_add, MixPiLambda.Y8_eq] at U_def
        exact U_def
      set ζ := MixPiLambda.Y8 h_le' hε with ζ_def
      set Z : Chromosome := ζ.1 + (lift^[2 * j] γ.1 + X.below (2 * j)) with Z_def
      have hZ : Z ∈ Mix (Pi, Lambda) := add_mem (SetLike.coe_mem _) mem1
      refine ⟨Z, hZ, ⟨?_, ?_, ?_⟩⟩
      · convert MixPiLambda.Step.mk (MixPiLambda.X8 h_le' hε) ζ
          ⟨lift^[2 * j] γ.1 + X.below (2 * j), mem1⟩
          (MixPiLambda.Primitive.type8 ε hε h_le')
        · nth_rw 1 [X_def, AddSubmonoid.coe_add]
        · nth_rw 1 [Z_def, AddSubmonoid.coe_add]
      · rw [Z_def, iterate_map_add, iterate_map_add,
          prime_lift_leftInverse_iterate (2 * j), prime_below le_rfl, add_zero,
          ζ_def, MixPiLambda.Y8_eq, iterate_map_add,
          prime_iterate_ofRank, prime_iterate_ofRank, U_def, add_left_inj]
        congr 2 <;> omega
      · intro i hi
        rw [X_def, Z_def, iterate_map_add, iterate_map_add (x := ζ.1),
          map_add, map_add, add_left_inj, ζ_def, MixPiLambda.X8_eq, MixPiLambda.Y8_eq,
          ← eqX1, ← eqX2]
        have eq3 : 2 * (m + j) = 2 * m + 2 * j := by ring
        have eq4 : 2 * (n + j) + 4 = 2 * n + 4 + 2 * j := by ring
        rw [eq3, eq4]
        exact mutation_type8_iterate_signature_eq h_le i (2 * j) hi

variable (hU' : U ∈ Mix (Lambda, Pi))

include hU' in
lemma mutation_lifting_odd (hk : ¬ Even k)
    (hMu : MixLambdaPi.Step ⟨prime^[k] X, prime_iterate_mem_odd hX hk⟩ ⟨U, hU'⟩) :
    ∃ (Z : Chromosome) (hZ : Z ∈ Mix (Pi, Lambda)),
      MixPiLambda.Step ⟨X, hX⟩ ⟨Z, hZ⟩ ∧
      prime^[k] Z = U ∧
      ∀ i ≤ k, signature (prime^[i] X) = signature (prime^[i] Z) := by
  -- Decompose `k = 2 * j + 1` for use in the arithmetic.
  obtain ⟨j, hj⟩ : ∃ j, k = 2 * j + 1 :=
    ⟨k / 2, by
      have : Odd k := Nat.not_even_iff_odd.mp hk
      have h2 := Nat.odd_iff.mp this
      omega⟩
  subst hj
  generalize X_def : (⟨prime^[2 * j + 1] X, prime_iterate_mem_odd hX hk⟩ :
    Mix (Lambda, Pi)) = Xk at hMu
  generalize U_def : (⟨U, hU'⟩ : Mix (Lambda, Pi)) = U' at hMu
  cases hMu with
  | mk α β γ h =>
    have mem1 : lift^[2 * j + 1] γ.1 + X.below (2 * j + 1) ∈ Mix (Pi, Lambda) :=
      lift_add_below_mem_odd hX hk γ.2
    cases h with
    | @type4 ε hε m n h_le =>
      -- V_1.X4 = (2m+2)NP + (2n+2)NP. After lift^[2j+1]:
      --   (2m+3+2j)NP + (2n+3+2j)NP = V_2.X4(m+j+1, n+j+1).
      have h_le' : m + j + 1 ≤ n + j + 1 := by omega
      have eqX1 : 2 * m + 2 + (2 * j + 1) = 2 * (m + j + 1) + 1 := by ring
      have eqX2 : 2 * n + 2 + (2 * j + 1) = 2 * (n + j + 1) + 1 := by ring
      rw [← Subtype.val_inj, AddSubmonoid.coe_add, MixLambdaPi.X4_eq,
        lift_prime, iterate_map_add, iterate_map_add,
        lift_iterate_ofRank (by omega), lift_iterate_ofRank (by omega),
        eqX1, eqX2, ← MixPiLambda.X4_eq (h_le := h_le'), add_assoc] at X_def
      replace U_def : U = Gene.ofRank (2 * m + 1) ε +
          Gene.ofRank (2 * n + 3) (-ε) + γ.1 := by
        rw [← Subtype.val_inj, AddSubmonoid.coe_add, MixLambdaPi.Y4_eq] at U_def
        exact U_def
      set ζ := MixPiLambda.Y4 h_le' hε with ζ_def
      set Z : Chromosome := ζ.1 + (lift^[2 * j + 1] γ.1 + X.below (2 * j + 1)) with Z_def
      have hZ : Z ∈ Mix (Pi, Lambda) := add_mem (SetLike.coe_mem _) mem1
      refine ⟨Z, hZ, ⟨?_, ?_, ?_⟩⟩
      · convert MixPiLambda.Step.mk (MixPiLambda.X4 h_le') ζ
          ⟨lift^[2 * j + 1] γ.1 + X.below (2 * j + 1), mem1⟩
          (MixPiLambda.Primitive.type4 ε hε h_le')
        · nth_rw 1 [X_def, AddSubmonoid.coe_add]
        · nth_rw 1 [Z_def, AddSubmonoid.coe_add]
      · rw [Z_def, iterate_map_add, iterate_map_add,
          prime_lift_leftInverse_iterate (2 * j + 1), prime_below le_rfl, add_zero,
          ζ_def, MixPiLambda.Y4_eq, iterate_map_add,
          prime_iterate_ofRank, prime_iterate_ofRank, U_def, add_left_inj]
        congr 2 <;> omega
      · intro i hi
        rw [X_def, Z_def, iterate_map_add, iterate_map_add (x := ζ.1),
          map_add, map_add, add_left_inj, ζ_def, MixPiLambda.X4_eq, MixPiLambda.Y4_eq,
          ← eqX1, ← eqX2]
        have eq3 : 2 * (m + j + 1) = 2 * m + 1 + (2 * j + 1) := by ring
        have eq4 : 2 * (n + j + 1) + 2 = 2 * n + 3 + (2 * j + 1) := by ring
        rw [eq3, eq4]
        exact MixLambdaPi.mutation_type4_iterate_signature_eq (ε := ε) h_le i (2 * j + 1) hi
    | @type5 ε hε m n h_le =>
      -- V_1.X5 = (2m+2)NP + (2n+3)ε. After lift^[2j+1]:
      --   (2m+3+2j)NP + (2n+4+2j)ε = V_2.X5(m+j+1, n+j+1).
      have h_le' : m + j + 1 ≤ n + j + 1 := by omega
      have eqX1 : 2 * m + 2 + (2 * j + 1) = 2 * (m + j + 1) + 1 := by ring
      have eqX2 : 2 * n + 3 + (2 * j + 1) = 2 * (n + j + 1) + 2 := by ring
      rw [← Subtype.val_inj, AddSubmonoid.coe_add, MixLambdaPi.X5_eq,
        lift_prime, iterate_map_add, iterate_map_add,
        lift_iterate_ofRank (by omega), lift_iterate_ofRank (by omega),
        eqX1, eqX2, ← MixPiLambda.X5_eq (h_le := h_le') hε, add_assoc] at X_def
      replace U_def : U = Gene.ofRank (2 * m + 1) ε +
          Gene.ofRank (2 * n + 4) GeneType.NonPolarized + γ.1 := by
        rw [← Subtype.val_inj, AddSubmonoid.coe_add, MixLambdaPi.Y5_eq] at U_def
        exact U_def
      set ζ := MixPiLambda.Y5 h_le' hε with ζ_def
      set Z : Chromosome := ζ.1 + (lift^[2 * j + 1] γ.1 + X.below (2 * j + 1)) with Z_def
      have hZ : Z ∈ Mix (Pi, Lambda) := add_mem (SetLike.coe_mem _) mem1
      refine ⟨Z, hZ, ⟨?_, ?_, ?_⟩⟩
      · convert MixPiLambda.Step.mk (MixPiLambda.X5 h_le' hε) ζ
          ⟨lift^[2 * j + 1] γ.1 + X.below (2 * j + 1), mem1⟩
          (MixPiLambda.Primitive.type5 ε hε h_le')
        · nth_rw 1 [X_def, AddSubmonoid.coe_add]
        · nth_rw 1 [Z_def, AddSubmonoid.coe_add]
      · rw [Z_def, iterate_map_add, iterate_map_add,
          prime_lift_leftInverse_iterate (2 * j + 1), prime_below le_rfl, add_zero,
          ζ_def, MixPiLambda.Y5_eq, iterate_map_add,
          prime_iterate_ofRank, prime_iterate_ofRank, U_def, add_left_inj]
        congr 2 <;> omega
      · intro i hi
        rw [X_def, Z_def, iterate_map_add, iterate_map_add (x := ζ.1),
          map_add, map_add, add_left_inj, ζ_def, MixPiLambda.X5_eq, MixPiLambda.Y5_eq,
          ← eqX1, ← eqX2]
        have eq3 : 2 * (m + j + 1) = 2 * m + 1 + (2 * j + 1) := by ring
        have eq4 : 2 * (n + j + 1) + 3 = 2 * n + 4 + (2 * j + 1) := by ring
        rw [eq3, eq4]
        exact MixLambdaPi.mutation_type5_iterate_signature_eq h_le i (2 * j + 1) hi
    | @type6 ε hε m n h_le =>
      -- V_1.X6 = (2m+1)ε + (2n+2)NP. After lift^[2j+1]:
      --   (2m+2+2j)ε + (2n+3+2j)NP = V_2.X6(m+j, n+j).
      have h_le' : m + j ≤ n + j := by omega
      have eqX1 : 2 * m + 1 + (2 * j + 1) = 2 * (m + j) + 2 := by ring
      have eqX2 : 2 * n + 2 + (2 * j + 1) = 2 * (n + j) + 3 := by ring
      rw [← Subtype.val_inj, AddSubmonoid.coe_add, MixLambdaPi.X6_eq,
        lift_prime, iterate_map_add, iterate_map_add,
        lift_iterate_ofRank (by omega), lift_iterate_ofRank (by omega),
        eqX1, eqX2, ← MixPiLambda.X6_eq (h_le := h_le') hε, add_assoc] at X_def
      replace U_def : U = Gene.ofRank (2 * m) GeneType.NonPolarized +
          Gene.ofRank (2 * n + 3) ε + γ.1 := by
        rw [← Subtype.val_inj, AddSubmonoid.coe_add, MixLambdaPi.Y6_eq] at U_def
        exact U_def
      set ζ := MixPiLambda.Y6 h_le' hε with ζ_def
      set Z : Chromosome := ζ.1 + (lift^[2 * j + 1] γ.1 + X.below (2 * j + 1)) with Z_def
      have hZ : Z ∈ Mix (Pi, Lambda) := add_mem (SetLike.coe_mem _) mem1
      refine ⟨Z, hZ, ⟨?_, ?_, ?_⟩⟩
      · convert MixPiLambda.Step.mk (MixPiLambda.X6 h_le' hε) ζ
          ⟨lift^[2 * j + 1] γ.1 + X.below (2 * j + 1), mem1⟩
          (MixPiLambda.Primitive.type6 ε hε h_le')
        · nth_rw 1 [X_def, AddSubmonoid.coe_add]
        · nth_rw 1 [Z_def, AddSubmonoid.coe_add]
      · rw [Z_def, iterate_map_add, iterate_map_add,
          prime_lift_leftInverse_iterate (2 * j + 1), prime_below le_rfl, add_zero,
          ζ_def, MixPiLambda.Y6_eq, iterate_map_add,
          prime_iterate_ofRank, prime_iterate_ofRank, U_def, add_left_inj]
        congr 2 <;> omega
      · intro i hi
        rw [X_def, Z_def, iterate_map_add, iterate_map_add (x := ζ.1),
          map_add, map_add, add_left_inj, ζ_def, MixPiLambda.X6_eq, MixPiLambda.Y6_eq,
          ← eqX1, ← eqX2]
        have eq3 : 2 * (m + j) + 1 = 2 * m + (2 * j + 1) := by ring
        have eq4 : 2 * (n + j) + 4 = 2 * n + 3 + (2 * j + 1) := by ring
        rw [eq3, eq4]
        exact MixLambdaPi.mutation_type6_iterate_signature_eq h_le i (2 * j + 1) hi
    | @type7 ε hε m n h_le =>
      -- V_1.X7 = (2m+1)ε + (2n+1)(-ε). After lift^[2j+1]:
      --   (2m+2+2j)ε + (2n+2+2j)(-ε) = V_2.X7(m+j, n+j).
      have h_le' : m + j ≤ n + j := by omega
      have eqX1 : 2 * m + 1 + (2 * j + 1) = 2 * (m + j) + 2 := by ring
      have eqX2 : 2 * n + 1 + (2 * j + 1) = 2 * (n + j) + 2 := by ring
      rw [← Subtype.val_inj, AddSubmonoid.coe_add, MixLambdaPi.X7_eq,
        lift_prime, iterate_map_add, iterate_map_add,
        lift_iterate_ofRank (by omega), lift_iterate_ofRank (by omega),
        eqX1, eqX2, ← MixPiLambda.X7_eq (h_le := h_le') hε, add_assoc] at X_def
      replace U_def : U = Gene.ofRank (2 * m) GeneType.NonPolarized +
          Gene.ofRank (2 * n + 2) GeneType.NonPolarized + γ.1 := by
        rw [← Subtype.val_inj, AddSubmonoid.coe_add, MixLambdaPi.Y7_eq] at U_def
        exact U_def
      set ζ : Mix (Pi, Lambda) := MixPiLambda.Y7 h_le' with ζ_def
      set Z : Chromosome := ζ.1 + (lift^[2 * j + 1] γ.1 + X.below (2 * j + 1)) with Z_def
      have hZ : Z ∈ Mix (Pi, Lambda) := add_mem (SetLike.coe_mem _) mem1
      refine ⟨Z, hZ, ⟨?_, ?_, ?_⟩⟩
      · convert MixPiLambda.Step.mk (MixPiLambda.X7 h_le' hε) ζ
          ⟨lift^[2 * j + 1] γ.1 + X.below (2 * j + 1), mem1⟩
          (MixPiLambda.Primitive.type7 ε hε h_le')
        · nth_rw 1 [X_def, AddSubmonoid.coe_add]
        · nth_rw 1 [Z_def, AddSubmonoid.coe_add]
      · rw [Z_def, iterate_map_add, iterate_map_add,
          prime_lift_leftInverse_iterate (2 * j + 1), prime_below le_rfl, add_zero,
          ζ_def, MixPiLambda.Y7_eq, iterate_map_add,
          prime_iterate_ofRank, prime_iterate_ofRank, U_def, add_left_inj]
        congr 2 <;> omega
      · intro i hi
        rw [X_def, Z_def, iterate_map_add, iterate_map_add (x := ζ.1),
          map_add, map_add, add_left_inj, ζ_def, MixPiLambda.X7_eq, MixPiLambda.Y7_eq,
          ← eqX1, ← eqX2]
        have eq3 : 2 * (m + j) + 1 = 2 * m + (2 * j + 1) := by ring
        have eq4 : 2 * (n + j) + 3 = 2 * n + 2 + (2 * j + 1) := by ring
        rw [eq3, eq4]
        exact MixLambdaPi.mutation_type7_iterate_signature_eq (ε := ε) h_le i (2 * j + 1) hi
    | @type8 ε hε m n h_le =>
      -- V_1.X8 = (2m+3)ε + (2n+3)ε. After lift^[2j+1]:
      --   (2m+4+2j)ε + (2n+4+2j)ε = V_2.X8(m+j+1, n+j+1).
      have h_le' : m + j + 1 ≤ n + j + 1 := by omega
      have eqX1 : 2 * m + 3 + (2 * j + 1) = 2 * (m + j + 1) + 2 := by ring
      have eqX2 : 2 * n + 3 + (2 * j + 1) = 2 * (n + j + 1) + 2 := by ring
      rw [← Subtype.val_inj, AddSubmonoid.coe_add, MixLambdaPi.X8_eq,
        lift_prime, iterate_map_add, iterate_map_add,
        lift_iterate_ofRank (by omega), lift_iterate_ofRank (by omega),
        eqX1, eqX2, ← MixPiLambda.X8_eq (h_le := h_le') hε, add_assoc] at X_def
      replace U_def : U = Gene.ofRank (2 * m + 1) ε +
          Gene.ofRank (2 * n + 5) ε + γ.1 := by
        rw [← Subtype.val_inj, AddSubmonoid.coe_add, MixLambdaPi.Y8_eq] at U_def
        exact U_def
      set ζ := MixPiLambda.Y8 h_le' hε with ζ_def
      set Z : Chromosome := ζ.1 + (lift^[2 * j + 1] γ.1 + X.below (2 * j + 1)) with Z_def
      have hZ : Z ∈ Mix (Pi, Lambda) := add_mem (SetLike.coe_mem _) mem1
      refine ⟨Z, hZ, ⟨?_, ?_, ?_⟩⟩
      · convert MixPiLambda.Step.mk (MixPiLambda.X8 h_le' hε) ζ
          ⟨lift^[2 * j + 1] γ.1 + X.below (2 * j + 1), mem1⟩
          (MixPiLambda.Primitive.type8 ε hε h_le')
        · nth_rw 1 [X_def, AddSubmonoid.coe_add]
        · nth_rw 1 [Z_def, AddSubmonoid.coe_add]
      · rw [Z_def, iterate_map_add, iterate_map_add,
          prime_lift_leftInverse_iterate (2 * j + 1), prime_below le_rfl, add_zero,
          ζ_def, MixPiLambda.Y8_eq, iterate_map_add,
          prime_iterate_ofRank, prime_iterate_ofRank, U_def, add_left_inj]
        congr 2 <;> omega
      · intro i hi
        rw [X_def, Z_def, iterate_map_add, iterate_map_add (x := ζ.1),
          map_add, map_add, add_left_inj, ζ_def, MixPiLambda.X8_eq, MixPiLambda.Y8_eq,
          ← eqX1, ← eqX2]
        have eq3 : 2 * (m + j + 1) = 2 * m + 1 + (2 * j + 1) := by ring
        have eq4 : 2 * (n + j + 1) + 4 = 2 * n + 5 + (2 * j + 1) := by ring
        rw [eq3, eq4]
        exact MixLambdaPi.mutation_type8_iterate_signature_eq h_le i (2 * j + 1) hi

end MixPiLambda
