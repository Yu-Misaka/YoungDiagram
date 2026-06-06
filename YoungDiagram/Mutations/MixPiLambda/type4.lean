import YoungDiagram

open Chromosome

variable {ε : GeneType} {m n : ℕ}

-- Φ = (Π, Λ): g ranks odd, g^ε ranks even.

local notation "type4X" =>
  Gene.ofRank (2 * m + 1) GeneType.NonPolarized +
  Gene.ofRank (2 * n + 1) GeneType.NonPolarized
local notation "type4Y" =>
  Gene.ofRank (2 * m) ε +
  Gene.ofRank (2 * n + 2) (- ε)
