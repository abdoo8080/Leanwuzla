module
prelude

public import Lean.Meta.Tactic.BVDecide.Main
public import Leanwuzla.Normalize
import Lean.Meta.Native
import Lean.Meta.Sym.Util


/-!
This module provides the implementation of the `bv_decide` frontend itself.
-/
namespace Lean.Meta.Tactic.BVDecide

open Std.Sat
open Std.Tactic.BVDecide
open Std.Tactic.BVDecide.Reflect

/--
Turn an `LratCert` into a proof that some `reflectedExpr` is UNSAT.
-/
def LratCert.toReflectionProof (cert : LratCert) (ctx : TacticContext)
    (reflectionResult : ReflectionResult) : MetaM Expr := do
  withTraceNode `Meta.Tactic.sat (fun _ => return "Compiling expr term") do
    mkAuxDecl ctx.exprDef reflectionResult.expr (mkConst ``BVLogicalExpr)

  withTraceNode `Meta.Tactic.sat (fun _ => return "Compiling proof certificate term") do
    mkAuxDecl ctx.certDef (toExpr cert) (mkConst ``String)

  let reflectedExpr := mkConst ctx.exprDef
  let certExpr := mkConst ctx.certDef
  let reflectionTerm := mkApp2 (mkConst ``verifyBVExpr) reflectedExpr certExpr

  withTraceNode `Meta.Tactic.sat (fun _ => return "Compiling and evaluating reflection proof term") do
    match (← nativeEqTrue `bv_decide reflectionTerm (axiomDeclRange? := (← getRef))) with
    | .notTrue =>
      throwError m!"Tactic `bv_decide` failed: The LRAT certificate could not be verified; \
        evaluating the following term returned `false`:{indentExpr reflectionTerm}"
    | .success auxProof =>
      return mkApp3 (mkConst ``unsat_of_verifyBVExpr_eq_true) reflectedExpr certExpr auxProof
where
  /--
  Add an auxiliary declaration. Only used to create constants that appear in our reflection proof.
  -/
  mkAuxDecl (name : Name) (value type : Expr) : CoreM Unit :=
    withOptions (fun opt => opt.set `compiler.extract_closed false) do
      addAndCompile <| .defnDecl {
        name := name,
        levelParams := [],
        type := type,
        value := value,
        hints := .abbrev,
        safety := .safe
      }

/--
Run a SAT solver to obtain an LRAT certificate and use it to produce a proof of UNSAT.
-/
public def lratBitblaster' (ctx : TacticContext) : UnsatProver LratCert :=
  fun (goal : MVarId) (reflectionResult : ReflectionResult) (atomsAssignment : Std.HashMap Nat (Nat × Expr × Bool)) => do
  withTraceNode `Meta.Tactic.bv (fun _ => return "Preparing LRAT reflection term") do
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

def bvUnsat' (g : MVarId) (hypotheses : Array Normalize.Hyp) (ctx : TacticContext) :
    Sym.SymM (Except CounterExample LratCert) :=
  M.run (hypotheses := hypotheses) do
    closeWithBVReflection g (lratBitblaster' ctx)

/--
Try to close `g` using a bitblaster. Return either a `CounterExample` if one is found or a `Result`
if `g` is proven.
-/
public def bvDecide'' (target : Normalize.Target) (ctx : TacticContext) :
    Grind.GrindM (Except CounterExample Result) := do
  Normalize.PreProcessM.run' ctx.preProcessContext target do
    let solved ← Normalize.bvNormalize'
    if solved then return .ok ⟨none⟩

    match ← bvUnsat' (← Normalize.PreProcessM.getTargetMVarId) (← Normalize.PreProcessM.getHyps) ctx with
    | .ok lratCert => return .ok ⟨some lratCert⟩
    | .error counterExample => return .error counterExample

end Lean.Meta.Tactic.BVDecide
