import BBFM.Results
import Lean.Util.CollectAxioms

/-! Check the transitive axiom dependencies of every theorem in the repository's
imported BBFM modules. This command fails compilation on any unexpected axiom. -/

open Lean in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut checked : Nat := 0
  for (name, info) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let moduleName := env.header.moduleNames[idx]!
    unless moduleName.toString.startsWith "BBFM." do continue
    match info with
    | .thmInfo _ =>
      let axioms ← collectAxioms name
      for ax in axioms do
        unless allowed.contains ax do
          throwError "Unexpected axiom {ax} in {name}"
      checked := checked + 1
    | .axiomInfo _ => throwError "Repository module declares an axiom: {name}"
    | _ => pure ()
  if checked == 0 then throwError "No repository theorems were audited"
  logInfo m!"BBFM_AXIOM_AUDIT: {checked} theorems checked; only propext, Classical.choice, Quot.sound"
