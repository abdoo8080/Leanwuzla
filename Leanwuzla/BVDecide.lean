import Lean.Elab.Tactic.BVDecide.Frontend.BVDecide

import Leanwuzla.Normalize

namespace Lean.Elab.Tactic.BVDecide.Frontend

open Std.Sat
open Std.Tactic.BVDecide.Reflect

def lratBitblaster' (goal : MVarId) (ctx : TacticContext) (reflectionResult : ReflectionResult)
    (atomsAssignment : Std.HashMap Nat (Nat × Expr × Bool)) :
    MetaM (Except CounterExample UnsatProver.Result) := do
  let bvExpr := reflectionResult.bvExpr
  let t1 ← IO.monoNanosNow
  let entry ←
    withTraceNode `Meta.Tactic.bv (fun _ => return "Bitblasting BVLogicalExpr to AIG") do
      -- lazyPure to prevent compiler lifting
      IO.lazyPure (fun _ => bvExpr.bitblast)
  let aigSize := entry.aig.decls.size
  trace[Meta.Tactic.bv] s!"AIG has {aigSize} nodes."

  if ctx.config.graphviz then
    IO.FS.writeFile ("." / "aig.gv") <| AIG.toGraphviz entry

  let (cnf, map) ←
    withTraceNode `Meta.Tactic.sat (fun _ => return "Converting AIG to CNF") do
      -- lazyPure to prevent compiler lifting
      IO.lazyPure (fun _ =>
        let (entry, map) := entry.relabelNat'
        let cnf := AIG.toCNF entry
        (cnf, map)
      )
  let t2 ← IO.monoNanosNow
  IO.printlnAndFlush s!"[time] bitblast: {t2 - t1}"

  let t1 ← IO.monoNanosNow
  let res ←
    withTraceNode `Meta.Tactic.sat (fun _ => return "Obtaining external proof certificate") do
      runExternal
        cnf
        ctx.solver
        ctx.lratPath
        ctx.config.trimProofs
        ctx.config.timeout
        ctx.config.binaryProofs
        ctx.config.solverMode
  let t2 ← IO.monoNanosNow
  IO.printlnAndFlush s!"[time] sat: {t2 - t1}"

  match res with
  | .ok cert =>
    trace[Meta.Tactic.sat] "SAT solver found a proof."
    let t1 ← IO.monoNanosNow
    let proof ← cert.toReflectionProof ctx reflectionResult
    let t2 ← IO.monoNanosNow
    IO.printlnAndFlush s!"[time] lrat: {t2 - t1}"
    return .ok ⟨proof, cert⟩
  | .error assignment =>
    trace[Meta.Tactic.sat] "SAT solver found a counter example."
    let equations := reconstructCounterExample map assignment aigSize atomsAssignment
    return .error { goal, unusedHypotheses := reflectionResult.unusedHypotheses, equations }

def bvUnsat' (g : MVarId) (ctx : TacticContext) : MetaM (Except CounterExample LratCert) := M.run do
  let unsatProver : UnsatProver := fun g reflectionResult atomsAssignment => do
    withTraceNode `Meta.Tactic.bv (fun _ => return "Preparing LRAT reflection term") do
      lratBitblaster' g ctx reflectionResult atomsAssignment
  closeWithBVReflection g unsatProver

/--
Try to close `g` using a bitblaster. Return either a `CounterExample` if one is found or a `Result`
if `g` is proven.
-/
def bvDecide''' (g : MVarId) (ctx : TacticContext) : MetaM (Except CounterExample Result) := do
  let g? ← Normalize.bvNormalize' g ctx.config
  let some g := g? | return .ok ⟨none⟩
  match ← bvUnsat' g ctx with
  | .ok lratCert => return .ok ⟨some lratCert⟩
  | .error counterExample => return .error counterExample

/--
Call `bvDecide'''` and throw a pretty error if a counter example ends up being produced.
-/
def bvDecide'' (g : MVarId) (ctx : TacticContext) : MetaM Result := do
  match ← bvDecide''' g ctx with
  | .ok result => return result
  | .error counterExample =>
    counterExample.goal.withContext do
      let error ← explainCounterExampleQuality counterExample
      throwError (← addMessageContextFull error)

end Lean.Elab.Tactic.BVDecide.Frontend
