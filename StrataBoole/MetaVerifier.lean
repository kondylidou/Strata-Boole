/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.MetaVerifier -- shake: keep
public import StrataBoole.Verify
import Strata.Transform.CallElim -- shake: keep
import Strata.DL.SMT.Translate -- shake: keep
meta import Lean.Meta.Eval
import Lean.Meta.Eval -- shake: keep
import Lean.Meta.Tactic.Rewrite -- shake: keep
meta import Lean.Meta.Tactic.Rewrite
import Lean.Meta.Tactic.Unfold -- shake: keep
meta import Lean.Meta.Tactic.Unfold

/-!
# Boole MetaVerifier

Extends `Strata.MetaVerifier` with Boole dialect support for `genCoreVCs` and
`smtVCsCorrect`. Test files in the `StrataBoole` package should import this
module instead of `Strata.MetaVerifier` directly.
-/

public section

namespace Strata.Boole

open StrataDDM (GlobalContext Program)

def genVCs (program : Strata.Boole.Program) (gctx : GlobalContext) (options : Core.VerifyOptions := .default) : Option Core.coreVCs := do
  let program ← (Strata.Boole.toCoreProgram program gctx).toOption
  Core.genVCs program options

end Strata.Boole

namespace Strata

open StrataDDM (Program)

/--
Generate verification conditions for a `StrataDDM.Program`, with Boole support.
Extends `Strata.genCoreVCs` to handle the Boole dialect.
-/
def genCoreVCsBoole (program : Program)
    (options : MetaVerifier.Options := {}) : Option Core.coreVCs := do
  if program.dialect == "Boole" then
    match Boole.getProgram program with
    | .ok booleProgram =>
      Boole.genVCs booleProgram program.globalContext options.toVerifyOptions
    | .error _ => none
  else
    genCoreVCs program options

/--
Generate SMT verification conditions for a `StrataDDM.Program`, with Boole support.

Marked `@[irreducible]` so that `Meta.unfoldTarget smtVCsCorrectBoole` leaves the
resulting `match genSMTVCsBoole … with …` stuck at the discriminant — preventing
the meta-level kernel from reducing the full VC generation pipeline via whnf.
The `nativeDecide` step in `gen_smt_vcs_boole` then proves the equality using
native compiled code (no heartbeat cost), and `mv.rewrite` resolves the match.
-/
@[irreducible]
def genSMTVCsBoole (program : Program)
    (options : MetaVerifier.Options := {}) : Option SMT.SMTVCs := do
  let coreVCs ← genCoreVCsBoole program options
  toSMTVCs coreVCs options

/--
State semantic correctness of the SMT verification conditions generated for a
program under the given metaverifier options, with Boole dialect support. For
example, `options.useArrayTheory` selects how the SMT encoder treats `Map`
types: under `true` they become SMT-LIB arrays, under `false` an uninterpreted
sort with axiomatized `select`/`update` functions.
-/
def smtVCsCorrectBoole (program : Program)
    (options : MetaVerifier.Options := {}) : Prop :=
  match genSMTVCsBoole program options with
  | some vcs => (denoteQueries vcs).getD False
  | none     => False

end Strata

namespace Strata

open StrataDDM (Program)

/--
Filter core VCs to exclude those belonging to bypassed procedures.
A VC belongs to procedure `p` when its label equals `p` or starts with `p_`.
-/
private def filterBypassedVCs (vcs : Core.coreVCs) (bypassProcs : List String) : Core.coreVCs :=
  if bypassProcs.isEmpty then vcs
  else vcs.filter fun (_, ob) =>
    !bypassProcs.any fun p => ob.label == p || ob.label.startsWith (p ++ "_")

/--
Generate core VCs for a program with bypassed procedures.  `CallElim` is applied
first so that call sites of bypassed procedures use the callee spec (havoc +
ensures assumptions) instead of inlining the body.  For Boole programs, bypassed
procedures are then removed from the Core program before VC generation, so their
bv128 definitions never appear in the shared SMT context.
-/
private def genCoreVCsBooleFiltered (program : Program) (bypassProcs : List String)
    (options : MetaVerifier.Options := {}) : Option Core.coreVCs := do
  if program.dialect == "Boole" then
    match Boole.getProgram program with
    | .ok booleProgram =>
      let coreProgram ← (Strata.Boole.toCoreProgram booleProgram program.globalContext).toOption
      -- Apply CallElim: replaces `call f(...)` with havoc + spec assumptions so
      -- callers see f's spec (not body) in their VCs.
      let (_, callelimProgram) ← (Core.Transform.run coreProgram Core.CallElim.callElim').toOption
      if bypassProcs.isEmpty then
        Core.genVCs callelimProgram options.toVerifyOptions
      else
        -- After CallElim, bypassed procs are no longer transitive callees of other procs.
        -- Remove their declarations so their bv128 definitions don't appear in the shared
        -- SMT context (which would cause toExpr term explosion in the tactic).
        let filteredDecls := callelimProgram.decls.filter fun d =>
          match d with
          | .proc p _ => !bypassProcs.any fun bp =>
              Core.CoreIdent.toPretty p.header.name == bp
          | _ => true
        let filteredProgram : Core.Program := { callelimProgram with decls := filteredDecls }
        Core.genVCs filteredProgram options.toVerifyOptions
    | .error _ => none
  else
    let vcs ← genCoreVCs program options
    some (filterBypassedVCs vcs bypassProcs)

/--
Like `genSMTVCsBoole` but skips VCs for procedures listed in `bypassProcedures`.
`CallElim` is applied first so callers of bypassed procedures get correct modular
VCs (spec contracts, not body substitution).

Marked `@[irreducible]` for the same reason as `genSMTVCsBoole`.
-/
@[irreducible]
def genSMTVCsBooleFiltered (program : Program) (bypassProcedures : List String)
    (options : MetaVerifier.Options := {}) : Option SMT.SMTVCs := do
  let coreVCs ← genCoreVCsBooleFiltered program bypassProcedures options
  toSMTVCs coreVCs options

/--
Like `smtVCsCorrectBoole` but skips VCs for `bypassProcedures`.
Use with `gen_smt_vcs_boole_filtered`.
-/
def smtVCsCorrectBooleFiltered (program : Program) (bypassProcedures : List String)
    (options : MetaVerifier.Options := {}) : Prop :=
  match genSMTVCsBooleFiltered program bypassProcedures options with
  | some vcs => (denoteQueries vcs).getD False
  | none     => False

end Strata

-- Re-enter Strata.SMT so that `translateQuery` and `Translate.symbolToName`
-- resolve the same way as in the upstream Strata.MetaVerifier.
namespace Strata.SMT

open Lean hiding Options

-- Like `createGoal` but skips the `Meta.check` elaboration pass that
-- triggers expensive whnf on each VC's Lean type expression.  Safe because
-- `translateQuery` produces well-typed expressions by construction; any
-- ill-typed goal would surface as a type error when the subgoal is closed.
private def createGoalFast : SMTVC → MetaM MVarId := fun (label, ctx, ts, t) => do
  match translateQuery ctx.toCore ts t with
  | .error e => throwError e
  | .ok e =>
    let .mvar mv ← Meta.mkFreshExprMVar e (userName := Translate.symbolToName label)
      | throwError "Failed to create goal"
    return mv

end Strata.SMT

namespace Strata.Meta

open Lean hiding Options

private unsafe def genSMTVCsBooleUnsafe (mv : MVarId) : MetaM (List MVarId) := do
  let type ← mv.getType
  let some (program, options) := type.app2? ``Strata.smtVCsCorrectBoole
    | throwError "Expected a Strata.smtVCsCorrectBoole goal"
  trace[debug] m!"Generating SMT VCs for {program}"
  let mv ← Meta.unfoldTarget mv ``Strata.smtVCsCorrectBoole
  let ovcs := mkApp2 (.const ``Strata.genSMTVCsBoole []) program options
  let ovcsType := .app (.const ``Option [0]) (.const ``Strata.SMT.SMTVCs [])
  let some evcs ← Meta.evalExpr (Option Strata.SMT.SMTVCs) ovcsType ovcs
    | throwError "Failed to generate VCs"
  trace[debug] m!"Generated {repr evcs}"
  let rhs := toExpr (some evcs)
  let eqVCs := mkApp3 (.const ``Eq [1]) ovcsType ovcs rhs
  let hEQVCs ← nativeDecide eqVCs
  let r ← mv.rewrite (← mv.getType) hEQVCs
  let mv ← mv.replaceTargetEq r.eNew r.eqProof
  let mvs ← evcs.mapM Strata.SMT.createGoalFast
  trace[debug] m!"Created {mvs.length} SMT VC goals: {mvs}"
  let ps ← mvs.mapM MVarId.getType
  let hP := andNIntro (List.zip ps (mvs.map Expr.mvar))
  mv.assign hP
  return mvs

@[implemented_by genSMTVCsBooleUnsafe]
meta opaque genSMTVCsBoole (mv : MVarId) : MetaM (List MVarId)

private unsafe def genSMTVCsBooleFilteredUnsafe (mv : MVarId) : MetaM (List MVarId) := do
  let type ← mv.getType
  -- smtVCsCorrectBooleFiltered has 3 explicit args: program, bypassProcs, options
  -- Internal Lean repr: .app (.app (.app (.const f []) program) bypassProcs) options
  let (program, bypassProcs, options) ←
    match type.consumeMData with
    | .app (.app (.app (.const n _) prog) bypass) opts =>
      if n == ``Strata.smtVCsCorrectBooleFiltered then pure (prog, bypass, opts)
      else throwError "Expected a Strata.smtVCsCorrectBooleFiltered goal"
    | _ => throwError "Expected a Strata.smtVCsCorrectBooleFiltered goal"
  let mv ← Meta.unfoldTarget mv ``Strata.smtVCsCorrectBooleFiltered
  let ovcs := mkApp3 (.const ``Strata.genSMTVCsBooleFiltered []) program bypassProcs options
  let ovcsType := .app (.const ``Option [0]) (.const ``Strata.SMT.SMTVCs [])
  let some evcs ← Meta.evalExpr (Option Strata.SMT.SMTVCs) ovcsType ovcs
    | throwError "Failed to generate VCs"
  let rhs := toExpr (some evcs)
  let eqVCs := mkApp3 (.const ``Eq [1]) ovcsType ovcs rhs
  let hEQVCs ← nativeDecide eqVCs
  let r ← mv.rewrite (← mv.getType) hEQVCs
  let mv ← mv.replaceTargetEq r.eNew r.eqProof
  let mvs ← evcs.mapM Strata.SMT.createGoalFast
  let ps ← mvs.mapM MVarId.getType
  let hP := andNIntro (List.zip ps (mvs.map Expr.mvar))
  mv.assign hP
  return mvs

@[implemented_by genSMTVCsBooleFilteredUnsafe]
meta opaque genSMTVCsBooleFiltered (mv : MVarId) : MetaM (List MVarId)

end Strata.Meta

namespace Strata.Tactic

open Lean Elab Tactic in
/--
Generate one Lean goal per SMT verification condition in a goal of the form
`Strata.smtVCsCorrectBoole program`. Boole-aware variant of `gen_smt_vcs`.
-/
syntax (name := genSMTVCsBoole) "gen_smt_vcs_boole" : tactic

open Lean Elab Tactic in
@[tactic genSMTVCsBoole] meta def evalGenSMTVCsBoole : Tactic := fun stx => do
  match stx with
  | `(tactic| gen_smt_vcs_boole) =>
    let mvs ← Meta.genSMTVCsBoole (← Tactic.getMainGoal)
    Tactic.replaceMainGoal mvs
  | _ => throwUnsupportedSyntax

open Lean Elab Tactic in
/--
Like `gen_smt_vcs_boole` but for goals of the form
`Strata.smtVCsCorrectBooleFiltered program bypassProcedures`.
VCs for the listed procedures are omitted; their specs still act as contracts.
-/
syntax (name := genSMTVCsBooleFiltered) "gen_smt_vcs_boole_filtered" : tactic

open Lean Elab Tactic in
@[tactic genSMTVCsBooleFiltered] meta def evalGenSMTVCsBooleFiltered : Tactic := fun stx => do
  match stx with
  | `(tactic| gen_smt_vcs_boole_filtered) =>
    let mvs ← Meta.genSMTVCsBooleFiltered (← Tactic.getMainGoal)
    Tactic.replaceMainGoal mvs
  | _ => throwUnsupportedSyntax

end Strata.Tactic

end -- public section
