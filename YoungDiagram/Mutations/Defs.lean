import YoungDiagram.Mutations.Pi
import YoungDiagram.Mutations.MixLambdaPi

open Variety

namespace Mutation

def Step : (i : Fin 5) → (Label i) → (Label i) → Prop
  | 0 => Pi.Step
  | 1 => MixLambdaPi.Step
  | 2 => sorry
  | 3 => sorry
  | 4 => sorry

end Mutation
