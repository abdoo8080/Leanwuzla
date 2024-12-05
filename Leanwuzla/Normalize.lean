import Lean.Elab.Tactic.BVDecide.Frontend.Normalize

def IO.printlnAndFlush {α} [ToString α] (a : α) : IO Unit := do
  IO.println a
  (← IO.getStdout).flush

namespace Lean.Elab.Tactic.BVDecide.Frontend.Normalize

namespace Pass

/--
Repeatedly run a list of `Pass` until they either close the goal or an iteration doesn't change
the goal anymore.
-/
partial def fixpointPipeline' (passes : List Pass) (goal : MVarId) : MetaM (Option MVarId) := do
  let runPass (goal? : Option MVarId) (pass : Pass) : MetaM (Option MVarId) := do
    let some goal := goal? | return none
    withTraceNode `bv (fun _ => return s!"Running pass: {pass.name}") do
      let t1 ← IO.monoNanosNow
      let r ← pass.run goal
      let t2 ← IO.monoNanosNow
      IO.printlnAndFlush s!"[time] {pass.name}: {t2 - t1}"
      return r
  let some newGoal := ← passes.foldlM (init := some goal) runPass | return none
  if goal != newGoal then
    trace[Meta.Tactic.bv] m!"Rerunning pipeline on:\n{newGoal}"
    fixpointPipeline' passes newGoal
  else
    trace[Meta.Tactic.bv] "Pipeline reached a fixpoint"
    return newGoal

end Pass

def bvNormalize' (g : MVarId) (cfg : BVDecideConfig) : MetaM (Option MVarId) := do
  withTraceNode `bv (fun _ => return "Normalizing goal") do
    -- Contradiction proof
    let some g ← g.falseOrByContra | return none
    trace[Meta.Tactic.bv] m!"Running preprocessing pipeline on:\n{g}"
    Pass.fixpointPipeline' (Pass.passPipeline cfg) g

end Lean.Elab.Tactic.BVDecide.Frontend.Normalize
