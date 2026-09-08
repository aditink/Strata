/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core
import StrataDDM.Integration.Lean.HashCommands
import Strata.MetaVerifier
import Strata.DL.SMT.DatatypeInductive

/-! # Generating a Lean inductive for each Core datatype

The point of the exercise: the datatype laws that the metaverifier used to
*assert* -- and which turned out to be contradictory on the Laurel prelude --
are theorems here, about a type that demonstrably exists.
-/

open StrataDDM (Program)
open Lean Elab Command
namespace Strata

/-- Datatypes of a program, as the encoder sees them. -/
def datatypesOf (p : Program) :
    List (Lambda.LDatatype Strata.SMT.DatatypeInductive.CoreIDMeta) :=
  let (cp, _) := TransM.run default (translateProgram p)
  match Core.typeCheck Core.VerifyOptions.default cp with
  | .error _ => []
  | .ok tc =>
    match Core.buildEnv Core.VerifyOptions.default tc Core.Factory with
    | .ok (e, _) => e.datatypes.allDatatypes
    | .error _ => []

open Strata.SMT.DatatypeInductive in
/-- Emit the types and their operations for a program. -/
def emitDatatypes (p : Program) : CommandElabM Unit := do
  let dts := datatypesOf p
  let usable := dts.filter (·.typeArgs.isEmpty)
  let names := usable.map (·.name)
  let params := openBaseTypes names usable
  let elabText := fun (src : String) => do
    match Parser.runParserCategory (← getEnv) `command src "<generated>" with
    | .error e => throwError "parse failed: {e}\n{src}"
    | .ok stx => elabCommand stx
  match blockTexts dts with
  | .error e => throwError "refused: {e}"
  | .ok srcs => for src in srcs do elabText src
  for group in dependencyGroups usable do
    match operationTexts names params group with
    | .error e => throwError "operations refused: {e}"
    | .ok srcs => for src in srcs do elabText src

private def valPgm : Program :=
#strata
program Core;
datatype Val { VInt(getInt : int), VBool(getBool : bool), VNone() };
procedure p (v : Val, out r : int) { $return: { r := 0; exit $return; } };
#end

/--
info: [Strata.Core] Type checking succeeded.

inductive Strata.Gen.«Val» where
  | «VInt» («getInt» : Int) : Strata.Gen.«Val»
  | «VBool» («getBool» : Prop) : Strata.Gen.«Val»
  | «VNone» : Strata.Gen.«Val»
-/
#guard_msgs in
#eval show IO Unit from do
  match Strata.SMT.DatatypeInductive.blockTexts (datatypesOf valPgm) with
  | .error e => IO.println s!"REFUSED: {e}"
  | .ok srcs => for s in srcs do IO.println s

run_cmd emitDatatypes valPgm

-- Exhaustiveness, disjointness and injectivity, as theorems.
example (v : Strata.Gen.«Val») :
    (∃ x, v = .«VInt» x) ∨ (∃ b, v = .«VBool» b) ∨ v = .«VNone» := by
  cases v with
  | «VInt» x => exact .inl ⟨x, rfl⟩
  | «VBool» b => exact .inr (.inl ⟨b, rfl⟩)
  | «VNone» => exact .inr (.inr rfl)

example (x : Int) (b : Prop) :
    Strata.Gen.«Val».«VInt» x ≠ .«VBool» b := by simp

example (x y : Int) (h : Strata.Gen.«Val».«VInt» x = .«VInt» y) : x = y := by
  simpa using h

-- Tag and selectors compute, so no law has to be assumed about them.
example (x : Int) : (Strata.Gen.«Val».«VInt» x).tag = 0 := rfl
example (x : Int) : (Strata.Gen.«Val».«VInt» x).«getInt» = x := rfl

/-- The capability the uninterpreted encoding cannot provide: deciding a tag on
a *symbolic* value. Every Laurel coercion is a chain of these, which is why the
signature-only encoding cannot verify translated Python. -/
example (v : Strata.Gen.«Val») : v.tag = 0 ∨ v.tag = 1 ∨ v.tag = 2 := by
  cases v <;> simp [Strata.Gen.«Val».tag]

-- Positivity within a group is checked defensively rather than tested here:
-- the only way to trigger it is a datatype keyed by itself, and Core's own type
-- checker rejects such a program before this module sees it. The case that does
-- arise -- Laurel's `Heap` carrying a `Map Composite ..` -- is *handled* by
-- ordering `Composite` into an earlier block, not refused.

end Strata
