import YoungDiagram

open Chromosome

variable {ε : GeneType} {m n : ℕ}

-- Φ = (Π, Λ): g ranks odd, g^ε ranks even.

local notation "type6X" =>
  Gene.ofRank (2 * m + 2) ε +
  Gene.ofRank (2 * n + 3) GeneType.NonPolarized
local notation "type6Y" =>
  Gene.ofRank (2 * m + 1) GeneType.NonPolarized +
  Gene.ofRank (2 * n + 4) ε
