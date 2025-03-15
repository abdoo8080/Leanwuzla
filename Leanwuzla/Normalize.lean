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
partial def fixpointPipeline' (passes : List Pass) (goal : MVarId) : PreProcessM (Option MVarId) := do
  let mut newGoal := goal
  for pass in passes do
    let t1 ← IO.monoNanosNow
    let r ← pass.run newGoal
    let t2 ← IO.monoNanosNow
    IO.printlnAndFlush s!"[time] {pass.name}: {t2 - t1}"
    if let some nextGoal := r then
      newGoal := nextGoal
    else
      trace[Meta.Tactic.bv] "Fixpoint iteration solved the goal"
      return none

  if goal != newGoal then
    trace[Meta.Tactic.bv] m!"Rerunning pipeline on:\n{newGoal}"
    fixpointPipeline' passes newGoal
  else
    trace[Meta.Tactic.bv] "Pipeline reached a fixpoint"
    return newGoal

end Pass

def bvNormalize' (g : MVarId) (cfg : BVDecideConfig) : MetaM (Option MVarId) := do
  withTraceNode `Meta.Tactic.bv (fun _ => return "Preprocessing goal") do
    (go g).run cfg g
where
  go (g : MVarId) : PreProcessM (Option MVarId) := do
    let some g' ← g.falseOrByContra | return none
    let mut g := g'

    trace[Meta.Tactic.bv] m!"Running preprocessing pipeline on:\n{g}"
    let cfg ← PreProcessM.getConfig

    if cfg.structures || cfg.enums then
      g := (← typeAnalysisPass.run g).get!

    /-
    There is a tension between the structures and enums pass at play:
    1. Enums should run before structures as it could convert matches on enums into `cond`
       chains. This in turn can be used by the structures pass to float projections into control
       flow which might be necessary.
    2. Structures should run before enums as it could reveal new facts about enums that we might
       need to handle. For example a structure might contain a field that contains a fact about
       some enum. This fact needs to be processed properly by the enums pass

    To resolve this tension we do the following:
    1. Run the structures pass (if enabled)
    2. Run the enums pass (if enabled)
    3. Within the enums pass we rerun the part of the structures pass that could profit from the
       enums pass as described above. This comes down to adding a few more lemmas to a simp
       invocation that is going to happen in the enums pass anyway and should thus be cheap.
    -/
    if cfg.structures then
      let some g' ← structuresPass.run g | return none
      g := g'

    if cfg.enums then
      let some g' ← enumsPass.run g | return none
      g := g'

    if cfg.fixedInt then
      let some g' ← intToBitVecPass.run g | return none
      g := g'

    trace[Meta.Tactic.bv] m!"Running fixpoint pipeline on:\n{g}"
    let pipeline ← passPipeline
    Pass.fixpointPipeline' pipeline g

end Lean.Elab.Tactic.BVDecide.Frontend.Normalize
