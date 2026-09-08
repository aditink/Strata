/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public meta import Strata.MetaVerifier
public meta import Strata.DL.SMT.DatatypeInductive
public meta import Strata.Languages.Core
public meta import Strata.Languages.Core.DDMTransform.Translate
public meta import Lean.Elab.Command
public meta import Lean.Meta.Eval
import Lean.MetavarContext -- shake: keep
import Lean.Elab.Term.TermElabM -- shake: keep
import Lean.Meta.Eval -- shake: keep

/-! # Commands for generating a program's datatype model

`smtVCsCorrectIn` needs two things declared before it can be stated: a Lean
inductive for each Core datatype, and a `SuppliedInterp` mapping the program's
symbols onto them. Both are produced as source text and elaborated, so both need
to run as commands rather than as part of a tactic.

    strata_gen_datatypes pgm
    strata_gen_interp pgm as pgmInterp only "my_label"

Order matters: the interpretation resolves each Core symbol to the generated
declaration standing for it, so the datatypes must already exist.

The `only` clause must name the same labels the eventual theorem does. The
interpretation has to fit every verification condition it will be used on, and
which symbols appear is label-dependent -- `RealAbstraction` introduces `$Real`
only for an obligation that actually mentions a real.
-/

public section

open Lean Elab Command
open StrataDDM (Program)

namespace Strata.Generate

/-- Evaluate an identifier denoting a `Program`.

`Meta.evalExpr` is unsafe, so this follows the same `implemented_by` shape the
metaverifier's own reflection tactics use. -/
unsafe def evalProgramUnsafe (stx : Syntax) : TermElabM Program := do
  let e ← Term.elabTerm stx (some (mkConst ``Program))
  Meta.evalExpr Program (mkConst ``Program) (← instantiateMVars e)

@[implemented_by evalProgramUnsafe]
meta opaque evalProgram (stx : Syntax) : TermElabM Program

/-- Elaborate one generated declaration from source text. -/
private meta def elabGenerated (src : String) : CommandElabM Unit := do
  match Parser.runParserCategory (← getEnv) `command src "<generated>" with
  | .error e => throwError "generated declaration failed to parse: {e}\n{src}"
  | .ok stx => elabCommand stx

/-- A program's datatypes, as the encoder sees them. -/
meta def programDatatypes (p : Program) :
    List (Lambda.LDatatype Strata.SMT.DatatypeInductive.CoreIDMeta) :=
  let (cp, _) := TransM.run default (translateProgram p)
  match Core.typeCheck Core.VerifyOptions.default cp with
  | .error _ => []
  | .ok tc =>
    match Core.buildEnv Core.VerifyOptions.default tc Core.Factory with
    | .ok (e, _) => e.datatypes.allDatatypes
    | .error _ => []

open Strata.SMT.DatatypeInductive in
/-- Declare a Lean inductive, plus a tag and selectors, for each datatype. -/
meta def emitDatatypes (p : Program) : CommandElabM Unit := do
  let dts := programDatatypes p
  let usable := dts.filter (·.typeArgs.isEmpty)
  let names := usable.map (·.name)
  let params := openBaseTypes names usable
  match blockTexts dts with
  | .error e => throwError "datatype generation refused: {e}"
  | .ok srcs => for src in srcs do elabGenerated src
  for group in dependencyGroups usable do
    match operationTexts names params group with
    | .error e => throwError "operation generation refused: {e}"
    | .ok srcs => for src in srcs do elabGenerated src

/-- Declare a `SuppliedInterp` named `name` interpreting the program's
datatypes. Must run after `emitDatatypes`. -/
meta def emitInterp (p : Program) (name : String)
    (options : Strata.MetaVerifier.Options := {}) : CommandElabM Unit := do
  let some vcs := Strata.genSMTVCs p options
    | throwError "no verification conditions to build an interpretation from"
  let ctxs := vcs.map (fun (_, ctx, _, _) => ctx.toCore)
  let some ctx := ctxs.head? | throwError "no verification conditions"
  -- Every VC must present the same interpreted symbols, since one
  -- interpretation serves them all. They genuinely can differ, so this is
  -- checked rather than assumed: a mismatch would make `denoteQueryIn` return
  -- `none`, the theorem `False`, and any proof of it meaningless.
  let split ← liftTermElabM (Strata.SMT.interpSplit ctx)
  for c in ctxs do
    let other ← liftTermElabM (Strata.SMT.interpSplit c)
    if other != split then
      throwError "verification conditions disagree on which symbols can be \
        interpreted: {repr split} vs {repr other}. Narrow the labels so they agree."
  elabGenerated (← liftTermElabM (Strata.SMT.interpText name ctx))

syntax (name := strataGenDatatypes) "strata_gen_datatypes " ident : command
syntax (name := strataGenInterp)
  "strata_gen_interp " ident " as " ident (" only " str,+)? : command

@[command_elab strataGenDatatypes]
meta def elabGenDatatypes : CommandElab := fun stx => do
  match stx with
  | `(command| strata_gen_datatypes $p:ident) =>
    emitDatatypes (← liftTermElabM (evalProgram p))
  | _ => throwUnsupportedSyntax

@[command_elab strataGenInterp]
meta def elabGenInterp : CommandElab := fun stx => do
  match stx with
  | `(command| strata_gen_interp $p:ident as $n:ident $[only $ls:str,*]?) =>
    let pgm ← liftTermElabM (evalProgram p)
    let labels := ls.map (fun l => (l.getElems.map (·.getString)).toList)
    emitInterp pgm n.getId.toString { onlyLabels := labels }
  | _ => throwUnsupportedSyntax

end Strata.Generate

end -- public section
