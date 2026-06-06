import YoungDiagram

open Chromosome

variable {ε : GeneType} {m n : ℕ}

-- Φ = (Π, Λ): g ranks odd, g^ε ranks even.

local notation "type5X" =>
  Gene.ofRank (2 * m + 1) GeneType.NonPolarized +
  Gene.ofRank (2 * n + 2) ε
local notation "type5Y" =>
  Gene.ofRank (2 * m) ε +
  Gene.ofRank (2 * n + 3) GeneType.NonPolarized
