import YoungDiagram.Mutations.Mix2LambdaPi
import YoungDiagram.Mutations.MixPi2Lambda

open Variety hiding prime
open Chromosome Pointwise

namespace MixPi2Lambda

variable {k : ℕ} {X U : Chromosome} (hX : X ∈ Mix (Pi, 2 • Lambda))

include hX

/-- For even `k`, `prime^[k] X ∈ Mix (Pi, 2 • Lambda)` if `X ∈ Mix (Pi, 2 • Lambda)`. -/
private lemma prime_iterate_mem_even (hk : Even k) :
    prime^[k] X ∈ Mix (Pi, 2 • Lambda) := by
  have := Variety.prime_mem_Mix_Pi_2Lambda_iterate hX k
  rwa [if_pos hk] at this

/-- For odd `k`, `prime^[k] X ∈ Mix (2 • Lambda, Pi)` if `X ∈ Mix (Pi, 2 • Lambda)`. -/
private lemma prime_iterate_mem_odd (hk : ¬ Even k) :
    prime^[k] X ∈ Mix (2 • Lambda, Pi) := by
  have := Variety.prime_mem_Mix_Pi_2Lambda_iterate hX k
  rwa [if_neg hk] at this

/-- Helper: `lift^[k] γ + X.below k ∈ Mix (Pi, 2 • Lambda)` for even `k`
when `γ ∈ Mix (Pi, 2 • Lambda)`. -/
private lemma lift_add_below_mem_even (hk : Even k)
    {γ : Chromosome} (hγ : γ ∈ Mix (Pi, 2 • Lambda)) :
    lift^[k] γ + X.below k ∈ Mix (Pi, 2 • Lambda) :=
  add_mem (Variety.lift_iterate_mem_Mix_Pi_2Lambda (by rw [if_pos hk]; exact hγ))
    (Variety.below_mem_Mix_Pi_2Lambda hX k)

/-- Helper: `lift^[k] γ + X.below k ∈ Mix (Pi, 2 • Lambda)` for odd `k`
when `γ ∈ Mix (2 • Lambda, Pi)`. -/
private lemma lift_add_below_mem_odd (hk : ¬ Even k)
    {γ : Chromosome} (hγ : γ ∈ Mix (2 • Lambda, Pi)) :
    lift^[k] γ + X.below k ∈ Mix (Pi, 2 • Lambda) :=
  add_mem (Variety.lift_iterate_mem_Mix_Pi_2Lambda (by rw [if_neg hk]; exact hγ))
    (Variety.below_mem_Mix_Pi_2Lambda hX k)

variable (hU : U ∈ Mix (Pi, 2 • Lambda))

include hU in
lemma mutation_lifting_even (hk : Even k)
    (hMu : MixPi2Lambda.Step ⟨prime^[k] X, prime_iterate_mem_even hX hk⟩ ⟨U, hU⟩) :
    ∃ (Z : Chromosome) (hZ : Z ∈ Mix (Pi, 2 • Lambda)),
      MixPi2Lambda.Step ⟨X, hX⟩ ⟨Z, hZ⟩ ∧
      prime^[k] Z = U ∧
      ∀ i ≤ k, signature (prime^[i] X) = signature (prime^[i] Z) := by
  -- Decompose `k = 2 * j` for use in the arithmetic.
  obtain ⟨j, hj⟩ : ∃ j, k = 2 * j :=
    ⟨k / 2, by have := Nat.even_iff.mp hk; omega⟩
  subst hj
  generalize X_def : (⟨prime^[2 * j] X, prime_iterate_mem_even hX hk⟩ :
    Mix (Pi, 2 • Lambda)) = Xk at hMu
  generalize U_def : (⟨U, hU⟩ : Mix (Pi, 2 • Lambda)) = U' at hMu
  cases hMu with
  | mk α β γ h =>
    have mem1 : lift^[2 * j] γ.1 + X.below (2 * j) ∈ Mix (Pi, 2 • Lambda) :=
      lift_add_below_mem_even hX hk γ.2
    cases h with
    | @type9 ε hε k0 =>
      -- V_4.X9 = (2k0+1)NP + (2k0+1)NP. After lift^[2j]:
      -- (2k0+1+2j)NP + (2k0+1+2j)NP = V_4.X9(k0+j).
      have eqX1 : 2 * k0 + 1 + 2 * j = 2 * (k0 + j) + 1 := by ring
      rw [← Subtype.val_inj, AddSubmonoid.coe_add, MixPi2Lambda.X9_eq,
        lift_prime, iterate_map_add, iterate_map_add,
        lift_iterate_ofRank (by omega),
        eqX1, ← MixPi2Lambda.X9_eq (k := k0 + j), add_assoc] at X_def
      replace U_def : U = Gene.ofRank (2 * k0) ε +
          Gene.ofRank (2 * k0 + 2) (-ε) + γ.1 := by
        rw [← Subtype.val_inj, AddSubmonoid.coe_add, MixPi2Lambda.Y9_eq] at U_def
        exact U_def
      set ζ := MixPi2Lambda.Y9 hε (k0 + j) with ζ_def
      set Z : Chromosome := ζ.1 + (lift^[2 * j] γ.1 + X.below (2 * j)) with Z_def
      have hZ : Z ∈ Mix (Pi, 2 • Lambda) := add_mem (SetLike.coe_mem _) mem1
      refine ⟨Z, hZ, ⟨?_, ?_, ?_⟩⟩
      · convert MixPi2Lambda.Step.mk (MixPi2Lambda.X9 (k0 + j)) ζ
          ⟨lift^[2 * j] γ.1 + X.below (2 * j), mem1⟩
          (MixPi2Lambda.Primitive.type9 ε hε (k0 + j))
        · nth_rw 1 [X_def, AddSubmonoid.coe_add]
        · nth_rw 1 [Z_def, AddSubmonoid.coe_add]
      · rw [Z_def, iterate_map_add, iterate_map_add,
          prime_lift_leftInverse_iterate (2 * j), prime_below le_rfl, add_zero,
          ζ_def, MixPi2Lambda.Y9_eq, iterate_map_add,
          prime_iterate_ofRank, prime_iterate_ofRank, U_def, add_left_inj]
        congr 2 <;> omega
      · intro i hi
        rw [X_def, Z_def, iterate_map_add, iterate_map_add (x := ζ.1),
          map_add, map_add, add_left_inj, ζ_def, MixPi2Lambda.X9_eq, MixPi2Lambda.Y9_eq,
          ← eqX1]
        have eq3 : 2 * (k0 + j) = 2 * k0 + 2 * j := by ring
        have eq4 : 2 * (k0 + j) + 2 = 2 * k0 + 2 + 2 * j := by ring
        rw [eq4, eq3]
        exact MixPi2Lambda.mutation_type9_iterate_signature_eq (ε := ε) (k := k0) i (2 * j) hi
    | @type10 ε ε' hε hε' m n h_le =>
      have h_le' : m + j ≤ n + j := by omega
      have eqX1 : 2 * m + 2 + 2 * j = 2 * (m + j) + 2 := by ring
      have eqX2 : 2 * n + 2 + 2 * j = 2 * (n + j) + 2 := by ring
      rw [← Subtype.val_inj, AddSubmonoid.coe_add, MixPi2Lambda.X10_eq,
        lift_prime, iterate_map_add, iterate_map_add,
        lift_iterate_ofRank (by omega), lift_iterate_ofRank (by omega),
        eqX1, eqX2, ← MixPi2Lambda.X10_eq (h_le := h_le') hε hε', add_assoc] at X_def
      replace U_def : U = Gene.ofRank (2 * m) ε +
          Gene.ofRank (2 * n + 4) ε' + γ.1 := by
        rw [← Subtype.val_inj, AddSubmonoid.coe_add, MixPi2Lambda.Y10_eq] at U_def
        exact U_def
      set ζ := MixPi2Lambda.Y10 h_le' hε hε' with ζ_def
      set Z : Chromosome := ζ.1 + (lift^[2 * j] γ.1 + X.below (2 * j)) with Z_def
      have hZ : Z ∈ Mix (Pi, 2 • Lambda) := add_mem (SetLike.coe_mem _) mem1
      refine ⟨Z, hZ, ⟨?_, ?_, ?_⟩⟩
      · convert MixPi2Lambda.Step.mk (MixPi2Lambda.X10 h_le' hε hε') ζ
          ⟨lift^[2 * j] γ.1 + X.below (2 * j), mem1⟩
          (MixPi2Lambda.Primitive.type10 ε ε' hε hε' h_le')
        · nth_rw 1 [X_def, AddSubmonoid.coe_add]
        · nth_rw 1 [Z_def, AddSubmonoid.coe_add]
      · rw [Z_def, iterate_map_add, iterate_map_add,
          prime_lift_leftInverse_iterate (2 * j), prime_below le_rfl, add_zero,
          ζ_def, MixPi2Lambda.Y10_eq, iterate_map_add,
          prime_iterate_ofRank, prime_iterate_ofRank, U_def, add_left_inj]
        congr 2 <;> omega
      · intro i hi
        rw [X_def, Z_def, iterate_map_add, iterate_map_add (x := ζ.1),
          map_add, map_add, add_left_inj, ζ_def, MixPi2Lambda.X10_eq, MixPi2Lambda.Y10_eq,
          ← eqX1, ← eqX2]
        have eq3 : 2 * (m + j) = 2 * m + 2 * j := by ring
        have eq4 : 2 * (n + j) + 4 = 2 * n + 4 + 2 * j := by ring
        rw [eq3, eq4]
        exact MixPi2Lambda.mutation_type10_iterate_signature_eq h_le i (2 * j) hi
    | @type11 ε hε m n h_le =>
      have h_le' : m + j ≤ n + j := by omega
      have eqX1 : 2 * m + 2 + 2 * j = 2 * (m + j) + 2 := by ring
      have eqX2 : 2 * n + 2 + 2 * j = 2 * (n + j) + 2 := by ring
      rw [← Subtype.val_inj, AddSubmonoid.coe_add, MixPi2Lambda.X11_eq,
        lift_prime, iterate_map_add, iterate_map_add, iterate_map_add,
        lift_iterate_ofRank (by omega), lift_iterate_ofRank (by omega),
        lift_iterate_ofRank (by omega),
        eqX1, eqX2, ← MixPi2Lambda.X11_eq (h_le := h_le') hε, add_assoc] at X_def
      replace U_def : U = Gene.ofRank (2 * m) ε +
          Gene.ofRank (2 * n + 3) GeneType.NonPolarized +
          Gene.ofRank (2 * n + 3) GeneType.NonPolarized + γ.1 := by
        rw [← Subtype.val_inj, AddSubmonoid.coe_add, MixPi2Lambda.Y11_eq] at U_def
        exact U_def
      set ζ := MixPi2Lambda.Y11 h_le' hε with ζ_def
      set Z : Chromosome := ζ.1 + (lift^[2 * j] γ.1 + X.below (2 * j)) with Z_def
      have hZ : Z ∈ Mix (Pi, 2 • Lambda) := add_mem (SetLike.coe_mem _) mem1
      refine ⟨Z, hZ, ⟨?_, ?_, ?_⟩⟩
      · convert MixPi2Lambda.Step.mk (MixPi2Lambda.X11 h_le' hε) ζ
          ⟨lift^[2 * j] γ.1 + X.below (2 * j), mem1⟩
          (MixPi2Lambda.Primitive.type11 ε hε h_le')
        · nth_rw 1 [X_def, AddSubmonoid.coe_add]
        · nth_rw 1 [Z_def, AddSubmonoid.coe_add]
      · rw [Z_def, iterate_map_add, iterate_map_add,
          prime_lift_leftInverse_iterate (2 * j), prime_below le_rfl, add_zero,
          ζ_def, MixPi2Lambda.Y11_eq, iterate_map_add, iterate_map_add,
          prime_iterate_ofRank, prime_iterate_ofRank,
          U_def, add_left_inj]
        congr 3 <;> omega
      · intro i hi
        rw [X_def, Z_def, iterate_map_add, iterate_map_add (x := ζ.1),
          map_add, map_add, add_left_inj, ζ_def, MixPi2Lambda.X11_eq, MixPi2Lambda.Y11_eq,
          ← eqX1, ← eqX2]
        have eq3 : 2 * (m + j) = 2 * m + 2 * j := by ring
        have eq4 : 2 * (n + j) + 3 = 2 * n + 3 + 2 * j := by ring
        rw [eq3, eq4]
        exact MixPi2Lambda.mutation_type11_iterate_signature_eq h_le i (2 * j) hi
    | @type12 ε hε m n h_le =>
      have h_le' : m + j ≤ n + j := by omega
      have eqX1 : 2 * m + 2 + 2 * j = 2 * (m + j) + 2 := by ring
      have eqX2 : 2 * n + 2 + 2 * j = 2 * (n + j) + 2 := by ring
      rw [← Subtype.val_inj, AddSubmonoid.coe_add, MixPi2Lambda.X12_eq,
        lift_prime, iterate_map_add, iterate_map_add, iterate_map_add,
        lift_iterate_ofRank (by omega), lift_iterate_ofRank (by omega),
        lift_iterate_ofRank (by omega),
        eqX1, eqX2, ← MixPi2Lambda.X12_eq (h_le := h_le') hε, add_assoc] at X_def
      replace U_def : U = Gene.ofRank (2 * m + 1) GeneType.NonPolarized +
          Gene.ofRank (2 * m + 1) GeneType.NonPolarized +
          Gene.ofRank (2 * n + 4) ε + γ.1 := by
        rw [← Subtype.val_inj, AddSubmonoid.coe_add, MixPi2Lambda.Y12_eq] at U_def
        exact U_def
      set ζ := MixPi2Lambda.Y12 h_le' hε with ζ_def
      set Z : Chromosome := ζ.1 + (lift^[2 * j] γ.1 + X.below (2 * j)) with Z_def
      have hZ : Z ∈ Mix (Pi, 2 • Lambda) := add_mem (SetLike.coe_mem _) mem1
      refine ⟨Z, hZ, ⟨?_, ?_, ?_⟩⟩
      · convert MixPi2Lambda.Step.mk (MixPi2Lambda.X12 h_le' hε) ζ
          ⟨lift^[2 * j] γ.1 + X.below (2 * j), mem1⟩
          (MixPi2Lambda.Primitive.type12 ε hε h_le')
        · nth_rw 1 [X_def, AddSubmonoid.coe_add]
        · nth_rw 1 [Z_def, AddSubmonoid.coe_add]
      · rw [Z_def, iterate_map_add, iterate_map_add,
          prime_lift_leftInverse_iterate (2 * j), prime_below le_rfl, add_zero,
          ζ_def, MixPi2Lambda.Y12_eq, iterate_map_add, iterate_map_add,
          prime_iterate_ofRank, prime_iterate_ofRank,
          U_def, add_left_inj]
        congr 3 <;> omega
      · intro i hi
        rw [X_def, Z_def, iterate_map_add, iterate_map_add (x := ζ.1),
          map_add, map_add, add_left_inj, ζ_def, MixPi2Lambda.X12_eq, MixPi2Lambda.Y12_eq,
          ← eqX1, ← eqX2]
        have eq3 : 2 * (m + j) + 1 = 2 * m + 1 + 2 * j := by ring
        have eq4 : 2 * (n + j) + 4 = 2 * n + 4 + 2 * j := by ring
        rw [eq3, eq4]
        exact MixPi2Lambda.mutation_type12_iterate_signature_eq (ε := ε) h_le i (2 * j) hi
    | @type13 m n h_le =>
      have h_le' : m + j ≤ n + j := by omega
      have eqX1 : 2 * m + 2 + 2 * j = 2 * (m + j) + 2 := by ring
      have eqX2 : 2 * n + 2 + 2 * j = 2 * (n + j) + 2 := by ring
      rw [← Subtype.val_inj, AddSubmonoid.coe_add, MixPi2Lambda.X13_eq,
        lift_prime, iterate_map_add, iterate_map_add, iterate_map_add, iterate_map_add,
        lift_iterate_ofRank (by omega), lift_iterate_ofRank (by omega),
        lift_iterate_ofRank (by omega), lift_iterate_ofRank (by omega),
        eqX1, eqX2, ← MixPi2Lambda.X13_eq (h_le := h_le'), add_assoc] at X_def
      replace U_def : U = Gene.ofRank (2 * m + 1) GeneType.NonPolarized +
          Gene.ofRank (2 * m + 1) GeneType.NonPolarized +
          Gene.ofRank (2 * n + 3) GeneType.NonPolarized +
          Gene.ofRank (2 * n + 3) GeneType.NonPolarized + γ.1 := by
        rw [← Subtype.val_inj, AddSubmonoid.coe_add, MixPi2Lambda.Y13_eq] at U_def
        exact U_def
      set ζ : Mix (Pi, 2 • Lambda) := MixPi2Lambda.Y13 h_le' with ζ_def
      set Z : Chromosome := ζ.1 + (lift^[2 * j] γ.1 + X.below (2 * j)) with Z_def
      have hZ : Z ∈ Mix (Pi, 2 • Lambda) := add_mem (SetLike.coe_mem _) mem1
      refine ⟨Z, hZ, ⟨?_, ?_, ?_⟩⟩
      · convert MixPi2Lambda.Step.mk (MixPi2Lambda.X13 h_le') ζ
          ⟨lift^[2 * j] γ.1 + X.below (2 * j), mem1⟩
          (MixPi2Lambda.Primitive.type13 h_le')
        · nth_rw 1 [X_def, AddSubmonoid.coe_add]
        · nth_rw 1 [Z_def, AddSubmonoid.coe_add]
      · rw [Z_def, iterate_map_add, iterate_map_add,
          prime_lift_leftInverse_iterate (2 * j), prime_below le_rfl, add_zero,
          ζ_def, MixPi2Lambda.Y13_eq, iterate_map_add, iterate_map_add, iterate_map_add,
          prime_iterate_ofRank, prime_iterate_ofRank,
          U_def, add_left_inj]
        congr 4 <;> omega
      · intro i hi
        rw [X_def, Z_def, iterate_map_add, iterate_map_add (x := ζ.1),
          map_add, map_add, add_left_inj, ζ_def, MixPi2Lambda.X13_eq, MixPi2Lambda.Y13_eq,
          ← eqX1, ← eqX2]
        have eq3 : 2 * (m + j) + 1 = 2 * m + 1 + 2 * j := by ring
        have eq4 : 2 * (n + j) + 3 = 2 * n + 3 + 2 * j := by ring
        rw [eq3, eq4]
        exact MixPi2Lambda.mutation_type13_iterate_signature_eq i (2 * j) hi
    | @type14 ε hε m n h_le =>
      have h_le' : m + j ≤ n + j := by omega
      have eqX1 : 2 * m + 2 + 2 * j = 2 * (m + j) + 2 := by ring
      have eqX2 : 2 * n + 2 + 2 * j = 2 * (n + j) + 2 := by ring
      rw [← Subtype.val_inj, AddSubmonoid.coe_add, MixPi2Lambda.X14_eq,
        lift_prime, iterate_map_add, iterate_map_add, iterate_map_add, iterate_map_add,
        lift_iterate_ofRank (by omega), lift_iterate_ofRank (by omega),
        eqX1, eqX2, ← MixPi2Lambda.X14_eq (h_le := h_le') hε, add_assoc] at X_def
      replace U_def : U = Gene.ofRank (2 * m + 1) GeneType.NonPolarized +
          Gene.ofRank (2 * m + 1) GeneType.NonPolarized +
          Gene.ofRank (2 * n + 3) GeneType.NonPolarized +
          Gene.ofRank (2 * n + 3) GeneType.NonPolarized + γ.1 := by
        rw [← Subtype.val_inj, AddSubmonoid.coe_add, MixPi2Lambda.Y14_eq] at U_def
        exact U_def
      set ζ := MixPi2Lambda.Y14 h_le' hε with ζ_def
      set Z : Chromosome := ζ.1 + (lift^[2 * j] γ.1 + X.below (2 * j)) with Z_def
      have hZ : Z ∈ Mix (Pi, 2 • Lambda) := add_mem (SetLike.coe_mem _) mem1
      refine ⟨Z, hZ, ⟨?_, ?_, ?_⟩⟩
      · convert MixPi2Lambda.Step.mk (MixPi2Lambda.X14 h_le' hε) ζ
          ⟨lift^[2 * j] γ.1 + X.below (2 * j), mem1⟩
          (MixPi2Lambda.Primitive.type14 ε hε h_le')
        · nth_rw 1 [X_def, AddSubmonoid.coe_add]
        · nth_rw 1 [Z_def, AddSubmonoid.coe_add]
      · rw [Z_def, iterate_map_add, iterate_map_add,
          prime_lift_leftInverse_iterate (2 * j), prime_below le_rfl, add_zero,
          ζ_def, MixPi2Lambda.Y14_eq, iterate_map_add, iterate_map_add, iterate_map_add,
          prime_iterate_ofRank, prime_iterate_ofRank,
          U_def, add_left_inj]
        congr 4 <;> omega
      · intro i hi
        rw [X_def, Z_def, iterate_map_add, iterate_map_add (x := ζ.1),
          map_add, map_add, add_left_inj, ζ_def, MixPi2Lambda.X14_eq, MixPi2Lambda.Y14_eq,
          ← eqX1, ← eqX2]
        have eq3 : 2 * (m + j) + 1 = 2 * m + 1 + 2 * j := by ring
        have eq4 : 2 * (n + j) + 3 = 2 * n + 3 + 2 * j := by ring
        rw [eq3, eq4]
        exact MixPi2Lambda.mutation_type14_iterate_signature_eq i (2 * j) hi
    | @type15 ε hε m n h_le =>
      have h_le' : m + j ≤ n + j := by omega
      have eqX1 : 2 * m + 2 + 2 * j = 2 * (m + j) + 2 := by ring
      have eqX2 : 2 * n + 2 + 2 * j = 2 * (n + j) + 2 := by ring
      rw [← Subtype.val_inj, AddSubmonoid.coe_add, MixPi2Lambda.X15_eq,
        lift_prime, iterate_map_add, iterate_map_add,
        lift_iterate_ofRank (by omega), lift_iterate_ofRank (by omega),
        eqX1, eqX2, ← MixPi2Lambda.X15_eq (h_le := h_le') hε, add_assoc] at X_def
      replace U_def : U = Gene.ofRank (2 * m) (-ε) +
          Gene.ofRank (2 * n + 4) ε + γ.1 := by
        rw [← Subtype.val_inj, AddSubmonoid.coe_add, MixPi2Lambda.Y15_eq] at U_def
        exact U_def
      set ζ := MixPi2Lambda.Y15 h_le' hε with ζ_def
      set Z : Chromosome := ζ.1 + (lift^[2 * j] γ.1 + X.below (2 * j)) with Z_def
      have hZ : Z ∈ Mix (Pi, 2 • Lambda) := add_mem (SetLike.coe_mem _) mem1
      refine ⟨Z, hZ, ⟨?_, ?_, ?_⟩⟩
      · convert MixPi2Lambda.Step.mk (MixPi2Lambda.X15 h_le' hε) ζ
          ⟨lift^[2 * j] γ.1 + X.below (2 * j), mem1⟩
          (MixPi2Lambda.Primitive.type15 ε hε h_le')
        · nth_rw 1 [X_def, AddSubmonoid.coe_add]
        · nth_rw 1 [Z_def, AddSubmonoid.coe_add]
      · rw [Z_def, iterate_map_add, iterate_map_add,
          prime_lift_leftInverse_iterate (2 * j), prime_below le_rfl, add_zero,
          ζ_def, MixPi2Lambda.Y15_eq, iterate_map_add,
          prime_iterate_ofRank, prime_iterate_ofRank, U_def, add_left_inj]
        congr 2 <;> omega
      · intro i hi
        rw [X_def, Z_def, iterate_map_add, iterate_map_add (x := ζ.1),
          map_add, map_add, add_left_inj, ζ_def, MixPi2Lambda.X15_eq, MixPi2Lambda.Y15_eq,
          ← eqX1, ← eqX2]
        have eq3 : 2 * (m + j) = 2 * m + 2 * j := by ring
        have eq4 : 2 * (n + j) + 4 = 2 * n + 4 + 2 * j := by ring
        rw [eq3, eq4]
        exact MixPi2Lambda.mutation_type15_iterate_signature_eq h_le i (2 * j) hi
    | @type16 ε hε m n h_le =>
      have h_le' : m + j ≤ n + j := by omega
      have eqX1 : 2 * m + 2 + 2 * j = 2 * (m + j) + 2 := by ring
      have eqX2 : 2 * n + 2 + 2 * j = 2 * (n + j) + 2 := by ring
      rw [← Subtype.val_inj, AddSubmonoid.coe_add, MixPi2Lambda.X16_eq,
        lift_prime, iterate_map_add, iterate_map_add, iterate_map_add,
        lift_iterate_ofRank (by omega), lift_iterate_ofRank (by omega),
        eqX1, eqX2, ← MixPi2Lambda.X16_eq (h_le := h_le') hε, add_assoc] at X_def
      replace U_def : U = Gene.ofRank (2 * m + 1) GeneType.NonPolarized +
          Gene.ofRank (2 * m + 1) GeneType.NonPolarized +
          Gene.ofRank (2 * n + 4) ε + γ.1 := by
        rw [← Subtype.val_inj, AddSubmonoid.coe_add, MixPi2Lambda.Y16_eq] at U_def
        exact U_def
      set ζ := MixPi2Lambda.Y16 h_le' hε with ζ_def
      set Z : Chromosome := ζ.1 + (lift^[2 * j] γ.1 + X.below (2 * j)) with Z_def
      have hZ : Z ∈ Mix (Pi, 2 • Lambda) := add_mem (SetLike.coe_mem _) mem1
      refine ⟨Z, hZ, ⟨?_, ?_, ?_⟩⟩
      · convert MixPi2Lambda.Step.mk (MixPi2Lambda.X16 h_le' hε) ζ
          ⟨lift^[2 * j] γ.1 + X.below (2 * j), mem1⟩
          (MixPi2Lambda.Primitive.type16 ε hε h_le')
        · nth_rw 1 [X_def, AddSubmonoid.coe_add]
        · nth_rw 1 [Z_def, AddSubmonoid.coe_add]
      · rw [Z_def, iterate_map_add, iterate_map_add,
          prime_lift_leftInverse_iterate (2 * j), prime_below le_rfl, add_zero,
          ζ_def, MixPi2Lambda.Y16_eq, iterate_map_add, iterate_map_add,
          prime_iterate_ofRank, prime_iterate_ofRank,
          U_def, add_left_inj]
        congr 3 <;> omega
      · intro i hi
        rw [X_def, Z_def, iterate_map_add, iterate_map_add (x := ζ.1),
          map_add, map_add, add_left_inj, ζ_def, MixPi2Lambda.X16_eq, MixPi2Lambda.Y16_eq,
          ← eqX1, ← eqX2]
        have eq3 : 2 * (m + j) + 1 = 2 * m + 1 + 2 * j := by ring
        have eq4 : 2 * (n + j) + 4 = 2 * n + 4 + 2 * j := by ring
        rw [eq3, eq4]
        exact MixPi2Lambda.mutation_type16_iterate_signature_eq h_le i (2 * j) hi
    | @type17 ε hε m n h_le =>
      have h_le' : m + j ≤ n + j := by omega
      have eqX1 : 2 * m + 2 + 2 * j = 2 * (m + j) + 2 := by ring
      have eqX2 : 2 * n + 2 + 2 * j = 2 * (n + j) + 2 := by ring
      rw [← Subtype.val_inj, AddSubmonoid.coe_add, MixPi2Lambda.X17_eq,
        lift_prime, iterate_map_add, iterate_map_add, iterate_map_add,
        lift_iterate_ofRank (by omega), lift_iterate_ofRank (by omega),
        eqX1, eqX2, ← MixPi2Lambda.X17_eq (h_le := h_le') hε, add_assoc] at X_def
      replace U_def : U = Gene.ofRank (2 * m) (-ε) +
          Gene.ofRank (2 * n + 3) GeneType.NonPolarized +
          Gene.ofRank (2 * n + 3) GeneType.NonPolarized + γ.1 := by
        rw [← Subtype.val_inj, AddSubmonoid.coe_add, MixPi2Lambda.Y17_eq] at U_def
        exact U_def
      set ζ := MixPi2Lambda.Y17 h_le' hε with ζ_def
      set Z : Chromosome := ζ.1 + (lift^[2 * j] γ.1 + X.below (2 * j)) with Z_def
      have hZ : Z ∈ Mix (Pi, 2 • Lambda) := add_mem (SetLike.coe_mem _) mem1
      refine ⟨Z, hZ, ⟨?_, ?_, ?_⟩⟩
      · convert MixPi2Lambda.Step.mk (MixPi2Lambda.X17 h_le' hε) ζ
          ⟨lift^[2 * j] γ.1 + X.below (2 * j), mem1⟩
          (MixPi2Lambda.Primitive.type17 ε hε h_le')
        · nth_rw 1 [X_def, AddSubmonoid.coe_add]
        · nth_rw 1 [Z_def, AddSubmonoid.coe_add]
      · rw [Z_def, iterate_map_add, iterate_map_add,
          prime_lift_leftInverse_iterate (2 * j), prime_below le_rfl, add_zero,
          ζ_def, MixPi2Lambda.Y17_eq, iterate_map_add, iterate_map_add,
          prime_iterate_ofRank, prime_iterate_ofRank,
          U_def, add_left_inj]
        congr 3 <;> omega
      · intro i hi
        rw [X_def, Z_def, iterate_map_add, iterate_map_add (x := ζ.1),
          map_add, map_add, add_left_inj, ζ_def, MixPi2Lambda.X17_eq, MixPi2Lambda.Y17_eq,
          ← eqX1, ← eqX2]
        have eq3 : 2 * (m + j) = 2 * m + 2 * j := by ring
        have eq4 : 2 * (n + j) + 3 = 2 * n + 3 + 2 * j := by ring
        rw [eq3, eq4]
        exact MixPi2Lambda.mutation_type17_iterate_signature_eq h_le i (2 * j) hi

variable (hU' : U ∈ Mix (2 • Lambda, Pi))

include hU' in
lemma mutation_lifting_odd (hk : ¬ Even k)
    (hMu : Mix2LambdaPi.Step ⟨prime^[k] X, prime_iterate_mem_odd hX hk⟩ ⟨U, hU'⟩) :
    ∃ (Z : Chromosome) (hZ : Z ∈ Mix (Pi, 2 • Lambda)),
      MixPi2Lambda.Step ⟨X, hX⟩ ⟨Z, hZ⟩ ∧
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
    Mix (2 • Lambda, Pi)) = Xk at hMu
  generalize U_def : (⟨U, hU'⟩ : Mix (2 • Lambda, Pi)) = U' at hMu
  cases hMu with
  | mk α β γ h =>
    have mem1 : lift^[2 * j + 1] γ.1 + X.below (2 * j + 1) ∈ Mix (Pi, 2 • Lambda) :=
      lift_add_below_mem_odd hX hk γ.2
    cases h with
    | @type9 ε hε k0 =>
      -- V_3.X9 = (2k0+2)NP+(2k0+2)NP. After lift^[2j+1]:
      -- (2k0+2+2j+1)NP+(2k0+2+2j+1)NP = (2(k0+j+1)+1)NP*2 = V_4.X9(k0+j+1).
      have eqX1 : 2 * k0 + 2 + (2 * j + 1) = 2 * (k0 + j + 1) + 1 := by ring
      rw [← Subtype.val_inj, AddSubmonoid.coe_add, Mix2LambdaPi.X9_eq,
        lift_prime, iterate_map_add, iterate_map_add,
        lift_iterate_ofRank (by omega),
        eqX1, ← MixPi2Lambda.X9_eq (k := k0 + j + 1), add_assoc] at X_def
      replace U_def : U = Gene.ofRank (2 * k0 + 1) ε +
          Gene.ofRank (2 * k0 + 3) (-ε) + γ.1 := by
        rw [← Subtype.val_inj, AddSubmonoid.coe_add, Mix2LambdaPi.Y9_eq] at U_def
        exact U_def
      set ζ := MixPi2Lambda.Y9 hε (k0 + j + 1) with ζ_def
      set Z : Chromosome := ζ.1 + (lift^[2 * j + 1] γ.1 + X.below (2 * j + 1)) with Z_def
      have hZ : Z ∈ Mix (Pi, 2 • Lambda) := add_mem (SetLike.coe_mem _) mem1
      refine ⟨Z, hZ, ⟨?_, ?_, ?_⟩⟩
      · convert MixPi2Lambda.Step.mk (MixPi2Lambda.X9 (k0 + j + 1)) ζ
          ⟨lift^[2 * j + 1] γ.1 + X.below (2 * j + 1), mem1⟩
          (MixPi2Lambda.Primitive.type9 ε hε (k0 + j + 1))
        · nth_rw 1 [X_def, AddSubmonoid.coe_add]
        · nth_rw 1 [Z_def, AddSubmonoid.coe_add]
      · rw [Z_def, iterate_map_add, iterate_map_add,
          prime_lift_leftInverse_iterate (2 * j + 1), prime_below le_rfl, add_zero,
          ζ_def, MixPi2Lambda.Y9_eq, iterate_map_add,
          prime_iterate_ofRank, prime_iterate_ofRank, U_def, add_left_inj]
        congr 2 <;> omega
      · intro i hi
        rw [X_def, Z_def, iterate_map_add, iterate_map_add (x := ζ.1),
          map_add, map_add, add_left_inj, ζ_def, MixPi2Lambda.X9_eq, MixPi2Lambda.Y9_eq,
          ← eqX1]
        have eq3 : 2 * (k0 + j + 1) = 2 * k0 + 1 + (2 * j + 1) := by ring
        have eq4 : 2 * (k0 + j + 1) + 2 = 2 * k0 + 3 + (2 * j + 1) := by ring
        rw [eq4, eq3]
        exact Mix2LambdaPi.mutation_type9_iterate_signature_eq (ε := ε) (k := k0) i (2 * j + 1) hi
    | @type10 ε ε' hε hε' m n h_le =>
      -- V_3.X10 = (2m+3)ε + (2n+3)ε'. After lift^[2j+1]:
      -- (2m+3+2j+1)ε + (2n+3+2j+1)ε' = (2(m+j+1)+2)ε + (2(n+j+1)+2)ε' = V_4.X10(m+j+1, n+j+1).
      have h_le' : m + j + 1 ≤ n + j + 1 := by omega
      have eqX1 : 2 * m + 3 + (2 * j + 1) = 2 * (m + j + 1) + 2 := by ring
      have eqX2 : 2 * n + 3 + (2 * j + 1) = 2 * (n + j + 1) + 2 := by ring
      rw [← Subtype.val_inj, AddSubmonoid.coe_add, Mix2LambdaPi.X10_eq,
        lift_prime, iterate_map_add, iterate_map_add,
        lift_iterate_ofRank (by omega), lift_iterate_ofRank (by omega),
        eqX1, eqX2, ← MixPi2Lambda.X10_eq (h_le := h_le') hε hε', add_assoc] at X_def
      replace U_def : U = Gene.ofRank (2 * m + 1) ε +
          Gene.ofRank (2 * n + 5) ε' + γ.1 := by
        rw [← Subtype.val_inj, AddSubmonoid.coe_add, Mix2LambdaPi.Y10_eq] at U_def
        exact U_def
      set ζ := MixPi2Lambda.Y10 h_le' hε hε' with ζ_def
      set Z : Chromosome := ζ.1 + (lift^[2 * j + 1] γ.1 + X.below (2 * j + 1)) with Z_def
      have hZ : Z ∈ Mix (Pi, 2 • Lambda) := add_mem (SetLike.coe_mem _) mem1
      refine ⟨Z, hZ, ⟨?_, ?_, ?_⟩⟩
      · convert MixPi2Lambda.Step.mk (MixPi2Lambda.X10 h_le' hε hε') ζ
          ⟨lift^[2 * j + 1] γ.1 + X.below (2 * j + 1), mem1⟩
          (MixPi2Lambda.Primitive.type10 ε ε' hε hε' h_le')
        · nth_rw 1 [X_def, AddSubmonoid.coe_add]
        · nth_rw 1 [Z_def, AddSubmonoid.coe_add]
      · rw [Z_def, iterate_map_add, iterate_map_add,
          prime_lift_leftInverse_iterate (2 * j + 1), prime_below le_rfl, add_zero,
          ζ_def, MixPi2Lambda.Y10_eq, iterate_map_add,
          prime_iterate_ofRank, prime_iterate_ofRank, U_def, add_left_inj]
        congr 2 <;> omega
      · intro i hi
        rw [X_def, Z_def, iterate_map_add, iterate_map_add (x := ζ.1),
          map_add, map_add, add_left_inj, ζ_def, MixPi2Lambda.X10_eq, MixPi2Lambda.Y10_eq,
          ← eqX1, ← eqX2]
        have eq3 : 2 * (m + j + 1) = 2 * m + 1 + (2 * j + 1) := by ring
        have eq4 : 2 * (n + j + 1) + 4 = 2 * n + 5 + (2 * j + 1) := by ring
        rw [eq3, eq4]
        exact Mix2LambdaPi.mutation_type10_iterate_signature_eq h_le i (2 * j + 1) hi
    | @type11 ε hε m n h_le =>
      -- V_3.X11 = (2m+3)ε+(2n+3)P+(2n+3)N. After lift^[2j+1] to V_4.X11(m+j+1, n+j+1).
      have h_le' : m + j + 1 ≤ n + j + 1 := by omega
      have eqX1 : 2 * m + 3 + (2 * j + 1) = 2 * (m + j + 1) + 2 := by ring
      have eqX2 : 2 * n + 3 + (2 * j + 1) = 2 * (n + j + 1) + 2 := by ring
      rw [← Subtype.val_inj, AddSubmonoid.coe_add, Mix2LambdaPi.X11_eq,
        lift_prime, iterate_map_add, iterate_map_add, iterate_map_add,
        lift_iterate_ofRank (by omega), lift_iterate_ofRank (by omega),
        lift_iterate_ofRank (by omega),
        eqX1, eqX2, ← MixPi2Lambda.X11_eq (h_le := h_le') hε, add_assoc] at X_def
      replace U_def : U = Gene.ofRank (2 * m + 1) ε +
          Gene.ofRank (2 * n + 4) GeneType.NonPolarized +
          Gene.ofRank (2 * n + 4) GeneType.NonPolarized + γ.1 := by
        rw [← Subtype.val_inj, AddSubmonoid.coe_add, Mix2LambdaPi.Y11_eq] at U_def
        exact U_def
      set ζ := MixPi2Lambda.Y11 h_le' hε with ζ_def
      set Z : Chromosome := ζ.1 + (lift^[2 * j + 1] γ.1 + X.below (2 * j + 1)) with Z_def
      have hZ : Z ∈ Mix (Pi, 2 • Lambda) := add_mem (SetLike.coe_mem _) mem1
      refine ⟨Z, hZ, ⟨?_, ?_, ?_⟩⟩
      · convert MixPi2Lambda.Step.mk (MixPi2Lambda.X11 h_le' hε) ζ
          ⟨lift^[2 * j + 1] γ.1 + X.below (2 * j + 1), mem1⟩
          (MixPi2Lambda.Primitive.type11 ε hε h_le')
        · nth_rw 1 [X_def, AddSubmonoid.coe_add]
        · nth_rw 1 [Z_def, AddSubmonoid.coe_add]
      · rw [Z_def, iterate_map_add, iterate_map_add,
          prime_lift_leftInverse_iterate (2 * j + 1), prime_below le_rfl, add_zero,
          ζ_def, MixPi2Lambda.Y11_eq, iterate_map_add, iterate_map_add,
          prime_iterate_ofRank, prime_iterate_ofRank,
          U_def, add_left_inj]
        congr 3 <;> omega
      · intro i hi
        rw [X_def, Z_def, iterate_map_add, iterate_map_add (x := ζ.1),
          map_add, map_add, add_left_inj, ζ_def, MixPi2Lambda.X11_eq, MixPi2Lambda.Y11_eq,
          ← eqX1, ← eqX2]
        have eq3 : 2 * (m + j + 1) = 2 * m + 1 + (2 * j + 1) := by ring
        have eq4 : 2 * (n + j + 1) + 3 = 2 * n + 4 + (2 * j + 1) := by ring
        rw [eq3, eq4]
        exact Mix2LambdaPi.mutation_type11_iterate_signature_eq h_le i (2 * j + 1) hi
    | @type12 ε hε m n h_le =>
      -- V_3.X12 = (2m+1)P+(2m+1)N+(2n+1)ε. After lift^[2j+1] to V_4.X12(m+j, n+j).
      have h_le' : m + j ≤ n + j := by omega
      have eqX1 : 2 * m + 1 + (2 * j + 1) = 2 * (m + j) + 2 := by ring
      have eqX2 : 2 * n + 1 + (2 * j + 1) = 2 * (n + j) + 2 := by ring
      rw [← Subtype.val_inj, AddSubmonoid.coe_add, Mix2LambdaPi.X12_eq,
        lift_prime, iterate_map_add, iterate_map_add, iterate_map_add,
        lift_iterate_ofRank (by omega), lift_iterate_ofRank (by omega),
        lift_iterate_ofRank (by omega),
        eqX1, eqX2, ← MixPi2Lambda.X12_eq (h_le := h_le') hε, add_assoc] at X_def
      replace U_def : U = Gene.ofRank (2 * m) GeneType.NonPolarized +
          Gene.ofRank (2 * m) GeneType.NonPolarized +
          Gene.ofRank (2 * n + 3) ε + γ.1 := by
        rw [← Subtype.val_inj, AddSubmonoid.coe_add, Mix2LambdaPi.Y12_eq] at U_def
        exact U_def
      set ζ := MixPi2Lambda.Y12 h_le' hε with ζ_def
      set Z : Chromosome := ζ.1 + (lift^[2 * j + 1] γ.1 + X.below (2 * j + 1)) with Z_def
      have hZ : Z ∈ Mix (Pi, 2 • Lambda) := add_mem (SetLike.coe_mem _) mem1
      refine ⟨Z, hZ, ⟨?_, ?_, ?_⟩⟩
      · convert MixPi2Lambda.Step.mk (MixPi2Lambda.X12 h_le' hε) ζ
          ⟨lift^[2 * j + 1] γ.1 + X.below (2 * j + 1), mem1⟩
          (MixPi2Lambda.Primitive.type12 ε hε h_le')
        · nth_rw 1 [X_def, AddSubmonoid.coe_add]
        · nth_rw 1 [Z_def, AddSubmonoid.coe_add]
      · rw [Z_def, iterate_map_add, iterate_map_add,
          prime_lift_leftInverse_iterate (2 * j + 1), prime_below le_rfl, add_zero,
          ζ_def, MixPi2Lambda.Y12_eq, iterate_map_add, iterate_map_add,
          prime_iterate_ofRank, prime_iterate_ofRank,
          U_def, add_left_inj]
        congr 3 <;> omega
      · intro i hi
        rw [X_def, Z_def, iterate_map_add, iterate_map_add (x := ζ.1),
          map_add, map_add, add_left_inj, ζ_def, MixPi2Lambda.X12_eq, MixPi2Lambda.Y12_eq,
          ← eqX1, ← eqX2]
        have eq3 : 2 * (m + j) + 1 = 2 * m + (2 * j + 1) := by ring
        have eq4 : 2 * (n + j) + 4 = 2 * n + 3 + (2 * j + 1) := by ring
        rw [eq3, eq4]
        exact Mix2LambdaPi.mutation_type12_iterate_signature_eq (ε := ε) h_le i (2 * j + 1) hi
    | @type13 m n h_le =>
      have h_le' : m + j ≤ n + j := by omega
      have eqX1 : 2 * m + 1 + (2 * j + 1) = 2 * (m + j) + 2 := by ring
      have eqX2 : 2 * n + 1 + (2 * j + 1) = 2 * (n + j) + 2 := by ring
      rw [← Subtype.val_inj, AddSubmonoid.coe_add, Mix2LambdaPi.X13_eq,
        lift_prime, iterate_map_add, iterate_map_add, iterate_map_add, iterate_map_add,
        lift_iterate_ofRank (by omega), lift_iterate_ofRank (by omega),
        lift_iterate_ofRank (by omega), lift_iterate_ofRank (by omega),
        eqX1, eqX2, ← MixPi2Lambda.X13_eq (h_le := h_le'), add_assoc] at X_def
      replace U_def : U = Gene.ofRank (2 * m) GeneType.NonPolarized +
          Gene.ofRank (2 * m) GeneType.NonPolarized +
          Gene.ofRank (2 * n + 2) GeneType.NonPolarized +
          Gene.ofRank (2 * n + 2) GeneType.NonPolarized + γ.1 := by
        rw [← Subtype.val_inj, AddSubmonoid.coe_add, Mix2LambdaPi.Y13_eq] at U_def
        exact U_def
      set ζ : Mix (Pi, 2 • Lambda) := MixPi2Lambda.Y13 h_le' with ζ_def
      set Z : Chromosome := ζ.1 + (lift^[2 * j + 1] γ.1 + X.below (2 * j + 1)) with Z_def
      have hZ : Z ∈ Mix (Pi, 2 • Lambda) := add_mem (SetLike.coe_mem _) mem1
      refine ⟨Z, hZ, ⟨?_, ?_, ?_⟩⟩
      · convert MixPi2Lambda.Step.mk (MixPi2Lambda.X13 h_le') ζ
          ⟨lift^[2 * j + 1] γ.1 + X.below (2 * j + 1), mem1⟩
          (MixPi2Lambda.Primitive.type13 h_le')
        · nth_rw 1 [X_def, AddSubmonoid.coe_add]
        · nth_rw 1 [Z_def, AddSubmonoid.coe_add]
      · rw [Z_def, iterate_map_add, iterate_map_add,
          prime_lift_leftInverse_iterate (2 * j + 1), prime_below le_rfl, add_zero,
          ζ_def, MixPi2Lambda.Y13_eq, iterate_map_add, iterate_map_add, iterate_map_add,
          prime_iterate_ofRank, prime_iterate_ofRank,
          U_def, add_left_inj]
        congr 4 <;> omega
      · intro i hi
        rw [X_def, Z_def, iterate_map_add, iterate_map_add (x := ζ.1),
          map_add, map_add, add_left_inj, ζ_def, MixPi2Lambda.X13_eq, MixPi2Lambda.Y13_eq,
          ← eqX1, ← eqX2]
        have eq3 : 2 * (m + j) + 1 = 2 * m + (2 * j + 1) := by ring
        have eq4 : 2 * (n + j) + 3 = 2 * n + 2 + (2 * j + 1) := by ring
        rw [eq3, eq4]
        exact Mix2LambdaPi.mutation_type13_iterate_signature_eq i (2 * j + 1) hi
    | @type14 ε hε m n h_le =>
      have h_le' : m + j ≤ n + j := by omega
      have eqX1 : 2 * m + 1 + (2 * j + 1) = 2 * (m + j) + 2 := by ring
      have eqX2 : 2 * n + 1 + (2 * j + 1) = 2 * (n + j) + 2 := by ring
      rw [← Subtype.val_inj, AddSubmonoid.coe_add, Mix2LambdaPi.X14_eq,
        lift_prime, iterate_map_add, iterate_map_add, iterate_map_add, iterate_map_add,
        lift_iterate_ofRank (by omega), lift_iterate_ofRank (by omega),
        eqX1, eqX2, ← MixPi2Lambda.X14_eq (h_le := h_le') hε, add_assoc] at X_def
      replace U_def : U = Gene.ofRank (2 * m) GeneType.NonPolarized +
          Gene.ofRank (2 * m) GeneType.NonPolarized +
          Gene.ofRank (2 * n + 2) GeneType.NonPolarized +
          Gene.ofRank (2 * n + 2) GeneType.NonPolarized + γ.1 := by
        rw [← Subtype.val_inj, AddSubmonoid.coe_add, Mix2LambdaPi.Y14_eq] at U_def
        exact U_def
      set ζ := MixPi2Lambda.Y14 h_le' hε with ζ_def
      set Z : Chromosome := ζ.1 + (lift^[2 * j + 1] γ.1 + X.below (2 * j + 1)) with Z_def
      have hZ : Z ∈ Mix (Pi, 2 • Lambda) := add_mem (SetLike.coe_mem _) mem1
      refine ⟨Z, hZ, ⟨?_, ?_, ?_⟩⟩
      · convert MixPi2Lambda.Step.mk (MixPi2Lambda.X14 h_le' hε) ζ
          ⟨lift^[2 * j + 1] γ.1 + X.below (2 * j + 1), mem1⟩
          (MixPi2Lambda.Primitive.type14 ε hε h_le')
        · nth_rw 1 [X_def, AddSubmonoid.coe_add]
        · nth_rw 1 [Z_def, AddSubmonoid.coe_add]
      · rw [Z_def, iterate_map_add, iterate_map_add,
          prime_lift_leftInverse_iterate (2 * j + 1), prime_below le_rfl, add_zero,
          ζ_def, MixPi2Lambda.Y14_eq, iterate_map_add, iterate_map_add, iterate_map_add,
          prime_iterate_ofRank, prime_iterate_ofRank,
          U_def, add_left_inj]
        congr 4 <;> omega
      · intro i hi
        rw [X_def, Z_def, iterate_map_add, iterate_map_add (x := ζ.1),
          map_add, map_add, add_left_inj, ζ_def, MixPi2Lambda.X14_eq, MixPi2Lambda.Y14_eq,
          ← eqX1, ← eqX2]
        have eq3 : 2 * (m + j) + 1 = 2 * m + (2 * j + 1) := by ring
        have eq4 : 2 * (n + j) + 3 = 2 * n + 2 + (2 * j + 1) := by ring
        rw [eq3, eq4]
        exact Mix2LambdaPi.mutation_type14_iterate_signature_eq i (2 * j + 1) hi
    | @type15 ε hε m n h_le =>
      have h_le' : m + j + 1 ≤ n + j + 1 := by omega
      have eqX1 : 2 * m + 3 + (2 * j + 1) = 2 * (m + j + 1) + 2 := by ring
      have eqX2 : 2 * n + 3 + (2 * j + 1) = 2 * (n + j + 1) + 2 := by ring
      rw [← Subtype.val_inj, AddSubmonoid.coe_add, Mix2LambdaPi.X15_eq,
        lift_prime, iterate_map_add, iterate_map_add,
        lift_iterate_ofRank (by omega), lift_iterate_ofRank (by omega),
        eqX1, eqX2, ← MixPi2Lambda.X15_eq (h_le := h_le') hε, add_assoc] at X_def
      replace U_def : U = Gene.ofRank (2 * m + 1) (-ε) +
          Gene.ofRank (2 * n + 5) ε + γ.1 := by
        rw [← Subtype.val_inj, AddSubmonoid.coe_add, Mix2LambdaPi.Y15_eq] at U_def
        exact U_def
      set ζ := MixPi2Lambda.Y15 h_le' hε with ζ_def
      set Z : Chromosome := ζ.1 + (lift^[2 * j + 1] γ.1 + X.below (2 * j + 1)) with Z_def
      have hZ : Z ∈ Mix (Pi, 2 • Lambda) := add_mem (SetLike.coe_mem _) mem1
      refine ⟨Z, hZ, ⟨?_, ?_, ?_⟩⟩
      · convert MixPi2Lambda.Step.mk (MixPi2Lambda.X15 h_le' hε) ζ
          ⟨lift^[2 * j + 1] γ.1 + X.below (2 * j + 1), mem1⟩
          (MixPi2Lambda.Primitive.type15 ε hε h_le')
        · nth_rw 1 [X_def, AddSubmonoid.coe_add]
        · nth_rw 1 [Z_def, AddSubmonoid.coe_add]
      · rw [Z_def, iterate_map_add, iterate_map_add,
          prime_lift_leftInverse_iterate (2 * j + 1), prime_below le_rfl, add_zero,
          ζ_def, MixPi2Lambda.Y15_eq, iterate_map_add,
          prime_iterate_ofRank, prime_iterate_ofRank, U_def, add_left_inj]
        congr 2 <;> omega
      · intro i hi
        rw [X_def, Z_def, iterate_map_add, iterate_map_add (x := ζ.1),
          map_add, map_add, add_left_inj, ζ_def, MixPi2Lambda.X15_eq, MixPi2Lambda.Y15_eq,
          ← eqX1, ← eqX2]
        have eq3 : 2 * (m + j + 1) = 2 * m + 1 + (2 * j + 1) := by ring
        have eq4 : 2 * (n + j + 1) + 4 = 2 * n + 5 + (2 * j + 1) := by ring
        rw [eq3, eq4]
        exact Mix2LambdaPi.mutation_type15_iterate_signature_eq h_le i (2 * j + 1) hi
    | @type16 ε hε m n h_le =>
      have h_le' : m + j ≤ n + j := by omega
      have eqX1 : 2 * m + 1 + (2 * j + 1) = 2 * (m + j) + 2 := by ring
      have eqX2 : 2 * n + 1 + (2 * j + 1) = 2 * (n + j) + 2 := by ring
      rw [← Subtype.val_inj, AddSubmonoid.coe_add, Mix2LambdaPi.X16_eq,
        lift_prime, iterate_map_add, iterate_map_add, iterate_map_add,
        lift_iterate_ofRank (by omega), lift_iterate_ofRank (by omega),
        eqX1, eqX2, ← MixPi2Lambda.X16_eq (h_le := h_le') hε, add_assoc] at X_def
      replace U_def : U = Gene.ofRank (2 * m) GeneType.NonPolarized +
          Gene.ofRank (2 * m) GeneType.NonPolarized +
          Gene.ofRank (2 * n + 3) ε + γ.1 := by
        rw [← Subtype.val_inj, AddSubmonoid.coe_add, Mix2LambdaPi.Y16_eq] at U_def
        exact U_def
      set ζ := MixPi2Lambda.Y16 h_le' hε with ζ_def
      set Z : Chromosome := ζ.1 + (lift^[2 * j + 1] γ.1 + X.below (2 * j + 1)) with Z_def
      have hZ : Z ∈ Mix (Pi, 2 • Lambda) := add_mem (SetLike.coe_mem _) mem1
      refine ⟨Z, hZ, ⟨?_, ?_, ?_⟩⟩
      · convert MixPi2Lambda.Step.mk (MixPi2Lambda.X16 h_le' hε) ζ
          ⟨lift^[2 * j + 1] γ.1 + X.below (2 * j + 1), mem1⟩
          (MixPi2Lambda.Primitive.type16 ε hε h_le')
        · nth_rw 1 [X_def, AddSubmonoid.coe_add]
        · nth_rw 1 [Z_def, AddSubmonoid.coe_add]
      · rw [Z_def, iterate_map_add, iterate_map_add,
          prime_lift_leftInverse_iterate (2 * j + 1), prime_below le_rfl, add_zero,
          ζ_def, MixPi2Lambda.Y16_eq, iterate_map_add, iterate_map_add,
          prime_iterate_ofRank, prime_iterate_ofRank,
          U_def, add_left_inj]
        congr 3 <;> omega
      · intro i hi
        rw [X_def, Z_def, iterate_map_add, iterate_map_add (x := ζ.1),
          map_add, map_add, add_left_inj, ζ_def, MixPi2Lambda.X16_eq, MixPi2Lambda.Y16_eq,
          ← eqX1, ← eqX2]
        have eq3 : 2 * (m + j) + 1 = 2 * m + (2 * j + 1) := by ring
        have eq4 : 2 * (n + j) + 4 = 2 * n + 3 + (2 * j + 1) := by ring
        rw [eq3, eq4]
        exact Mix2LambdaPi.mutation_type16_iterate_signature_eq h_le i (2 * j + 1) hi
    | @type17 ε hε m n h_le =>
      have h_le' : m + j + 1 ≤ n + j + 1 := by omega
      have eqX1 : 2 * m + 3 + (2 * j + 1) = 2 * (m + j + 1) + 2 := by ring
      have eqX2 : 2 * n + 3 + (2 * j + 1) = 2 * (n + j + 1) + 2 := by ring
      rw [← Subtype.val_inj, AddSubmonoid.coe_add, Mix2LambdaPi.X17_eq,
        lift_prime, iterate_map_add, iterate_map_add, iterate_map_add,
        lift_iterate_ofRank (by omega), lift_iterate_ofRank (by omega),
        eqX1, eqX2, ← MixPi2Lambda.X17_eq (h_le := h_le') hε, add_assoc] at X_def
      replace U_def : U = Gene.ofRank (2 * m + 1) (-ε) +
          Gene.ofRank (2 * n + 4) GeneType.NonPolarized +
          Gene.ofRank (2 * n + 4) GeneType.NonPolarized + γ.1 := by
        rw [← Subtype.val_inj, AddSubmonoid.coe_add, Mix2LambdaPi.Y17_eq] at U_def
        exact U_def
      set ζ := MixPi2Lambda.Y17 h_le' hε with ζ_def
      set Z : Chromosome := ζ.1 + (lift^[2 * j + 1] γ.1 + X.below (2 * j + 1)) with Z_def
      have hZ : Z ∈ Mix (Pi, 2 • Lambda) := add_mem (SetLike.coe_mem _) mem1
      refine ⟨Z, hZ, ⟨?_, ?_, ?_⟩⟩
      · convert MixPi2Lambda.Step.mk (MixPi2Lambda.X17 h_le' hε) ζ
          ⟨lift^[2 * j + 1] γ.1 + X.below (2 * j + 1), mem1⟩
          (MixPi2Lambda.Primitive.type17 ε hε h_le')
        · nth_rw 1 [X_def, AddSubmonoid.coe_add]
        · nth_rw 1 [Z_def, AddSubmonoid.coe_add]
      · rw [Z_def, iterate_map_add, iterate_map_add,
          prime_lift_leftInverse_iterate (2 * j + 1), prime_below le_rfl, add_zero,
          ζ_def, MixPi2Lambda.Y17_eq, iterate_map_add, iterate_map_add,
          prime_iterate_ofRank, prime_iterate_ofRank,
          U_def, add_left_inj]
        congr 3 <;> omega
      · intro i hi
        rw [X_def, Z_def, iterate_map_add, iterate_map_add (x := ζ.1),
          map_add, map_add, add_left_inj, ζ_def, MixPi2Lambda.X17_eq, MixPi2Lambda.Y17_eq,
          ← eqX1, ← eqX2]
        have eq3 : 2 * (m + j + 1) = 2 * m + 1 + (2 * j + 1) := by ring
        have eq4 : 2 * (n + j + 1) + 3 = 2 * n + 4 + (2 * j + 1) := by ring
        rw [eq3, eq4]
        exact Mix2LambdaPi.mutation_type17_iterate_signature_eq h_le i (2 * j + 1) hi

end MixPi2Lambda
