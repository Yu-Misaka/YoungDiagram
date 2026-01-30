import YoungDiagram

#eval [true].isAlt
#eval [true, true].isAlt
#eval [true, false].isAlt
#eval [true, false, true].isAlt
#eval [false, true, false].isAlt

#eval [true].toGene
#eval [true, false].toGene
#eval [true, false, true].toGene
#eval [false, true, false].toGene

#eval [true].toGene.toList
#eval [true, false].toGene.toList
#eval [true, false, true].toGene.toList
#eval [false, true, false].toGene.toList

#eval [true].toGene.signature
#eval [true, false].toGene.signature
#eval [true, false, true].toGene.signature
#eval [false, true, false].toGene.signature

open Chromosome Pointwise

#check Pi
#check Mix (Lambda, Pi)
#check Mix (Pi, Lambda)
#check Mix (2 • Lambda, Pi)
#check Mix (Pi, 2 • Lambda)

#synth SMul ℕ variety

noncomputable section example_of_mutation

abbrev X := Gene.ofRank 5 .Positive +
  Gene.ofRank 4 .Positive + Gene.ofRank 1 .Negative

abbrev Y₁ := Gene.ofRank 6 .Negative +
  Gene.ofRank 4 .Positive

example : IsMutation X Y₁ := by
  rw [X, Y₁, add_comm, ← add_assoc, IsMutation_iff_add]
  have primMut := @Pi.PrimitiveMutation.type_1 .Negative (by decide) 1 5 NeZero.one_le NeZero.one_le
  have := Pi.PrimitiveMutation_isMutation primMut
  simpa [Pi.Y₁, Pi.X₁] using this

end example_of_mutation
