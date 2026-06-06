import YoungDiagram

open Chromosome

variable {ε : GeneType} {m n : ℕ}

-- Φ = (Π, Λ): g ranks odd, g^ε ranks even.

local notation "type8X" =>
  Gene.ofRank (2 * m + 2) ε +
  Gene.ofRank (2 * n + 2) ε
local notation "type8Y" =>
  Gene.ofRank (2 * m) ε +
  Gene.ofRank (2 * n + 4) ε
