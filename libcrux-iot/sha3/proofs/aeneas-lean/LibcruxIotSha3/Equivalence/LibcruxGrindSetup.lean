/- Project-local grind attribute, modelled on `Aeneas.Grind.agrind`. -/
import Aeneas.Tactic.Solver.Grind.Init

namespace libcrux_iot_sha3.Equivalence

open Lean.Meta.Grind in
register_grind_attr' libcruxgrindExt libcruxgrind

open Lean Lean.Meta Lean.Elab.Tactic Aeneas.Grind in
def libcruxgrindCore (config : AGrindConfig) (isOnly : Bool)
    (ps : Array (Lean.TSyntax `Lean.Parser.Tactic.grindParam)) :
    Lean.Elab.Tactic.TacticM Unit := do
  let mvarId ← Lean.Elab.Tactic.getMainGoal
  mvarId.withContext do
    let baseParams ← if isOnly then
        Lean.Meta.Grind.mkOnlyParams config.toConfig
      else
        let env ← Lean.getEnv
        let extensions : Lean.Meta.Grind.ExtensionStateArray := #[libcruxgrindExt.getState env]
        Aeneas.Grind.mkParams config.toConfig extensions true
    let fullParams ← Lean.Elab.Tactic.elabGrindParams baseParams ps (lax := config.lax) («only» := isOnly)
    agrindEval config.toConfig fullParams mvarId
  Lean.Elab.Tactic.replaceMainGoal []

open Lean.Parser.Tactic in
syntax (name := libcruxgrindTactic) "libcruxgrind" optConfig (" only")? (" [" grindParam,* "]")? : tactic

open Lean.Parser.Tactic Aeneas.Grind in
elab_rules : tactic
  | `(tactic| libcruxgrind $config:optConfig only $[ [$params:grindParam,*] ]?) => do
    let ps := if let some ps := params then ps.getElems else #[]
    libcruxgrindCore (← elabAGrindConfig config) (isOnly := true) ps
  | `(tactic| libcruxgrind $config:optConfig $[ [$params:grindParam,*] ]?) => do
    let ps := if let some ps := params then ps.getElems else #[]
    libcruxgrindCore (← elabAGrindConfig config) (isOnly := false) ps

end libcrux_iot_sha3.Equivalence
