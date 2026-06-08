import YoungDiagram.Mutations.Pi
import YoungDiagram.Mutations.MixLambdaPi
import YoungDiagram.Mutations.MixPiLambda
import YoungDiagram.Mutations.Mix2LambdaPi
import YoungDiagram.Mutations.MixPi2Lambda

open Variety

namespace Mutation

def Step : (i : Fin 5) → (Label i) → (Label i) → Prop
  | 0 => Pi.Step
  | 1 => MixLambdaPi.Step
  | 2 => MixPiLambda.Step
  | 3 => Mix2LambdaPi.Step
  | 4 => MixPi2Lambda.Step

end Mutation
