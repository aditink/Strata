/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.SMTEncoder

/-! # Generating a Lean inductive for each Core datatype

The metaverifier used to model a datatype by declaring an uninterpreted sort and
*asserting* its laws -- injectivity, disjointness, exhaustiveness,
selector-inverse. That was unsound: on the Laurel prelude the asserted set was
contradictory, and `1 == 2` became provable for a one-line Python function.

The fix is to exhibit a datatype rather than describe one. This module turns a
Core datatype block into a real Lean `inductive`, so those four laws become
theorems about a concrete type instead of assumptions, structural induction is
available, and there is nothing left to be inconsistent.

## Why text rather than syntax quotations

The declaration is built as source text and parsed. Quotations attach macro
scopes to the constructor names, and the names here come from Core as plain
strings, so hygiene has nothing useful to contribute and actively breaks the
mutual-block form. Elaborating the ordinary `inductive` command also yields
`casesOn`, `noConfusion`, the injectivity lemmas and the rest exactly as for a
hand-written type, which hand-rolling `addDecl` does not.

## Names

Laurel mints identifiers Lean will not accept bare -- `$Box`, `Mk$Box`,
`PythonError.response`. Every generated name is therefore wrapped in guillemets,
which lets the Core name through character for character rather than mangling
it, so the generated type still reads against the program it came from. The one
character guillemets cannot carry is `»` itself, which is refused.

## Types with no Lean image

`Any` carries `from_float (as_float : real)`, and `real` has no Lean type --
Strata cannot depend on Mathlib. Rather than refuse the whole prelude for it,
such a type becomes a *parameter* of the generated block, mirroring what
`SMT.RealAbstraction` does on the term side: it is abstract, and no arithmetic
is available on it, but the tag structure around it survives intact.

## What is refused

A datatype is only emitted when every field type maps to a Lean type, and when
its own type does not occur to the left of an arrow. Anything else is refused by
name rather than approximated, since a silently wrong model is the failure mode
this module exists to remove.
-/

public section

namespace Strata.SMT.DatatypeInductive

open Lean Lambda

/-- Metadata parameter of Core identifiers; `Core` alone resolves to the DDM
dialect value of the same name. -/
abbrev CoreIDMeta := _root_.Core.CoreLParams.IDMeta

private opaque RealNonempty : NonemptyType

/-- Carrier for a base type that has no Lean image, `real` being the only one
the Laurel prelude produces.

Opaque on purpose. A generated datatype carrying a `real` has to be applied to
*some* type, and picking a concrete one would be unsound in both directions: it
would let a property be proved that only holds in that model, and it would admit
a counterexample that is not realizable. An opaque type assumes nothing, so it
is exactly as strong as leaving the sort quantified -- which is what
`RealAbstraction` already does to the operations on it.

Modelling `real` faithfully is a separate matter: Python's `float` is IEEE 754
binary64, not a real, so `real` is the wrong target regardless of how it is
denoted. -/
def Real : Type := RealNonempty.type

instance : Nonempty Real := RealNonempty.property

noncomputable instance : Inhabited Real := Classical.inhabited_of_nonempty inferInstance

/-- Namespace for the generated types, keeping them clear of user names.

Relative, not `_root_`-anchored: `_root_` is accepted in a declaration name but
not in the references the block makes to its own types. The declarations
therefore land in whatever namespace the caller elaborates them in, so a caller
inside `namespace Strata` gets `Strata.Strata.Gen.Any`. Placement is the
caller's to control. -/
def genPrefix : String := "Strata.Gen"

/-- A Core name as a Lean identifier, verbatim inside guillemets. -/
def quoted (name : String) : String := s!"«{name}»"

/-- The Lean name for a Core datatype. -/
def typeName (datatype : String) : String := s!"{genPrefix}.{quoted datatype}"

/-- The Lean name for one of its constructors. -/
def ctorName (datatype constr : String) : String :=
  s!"{typeName datatype}.{quoted constr}"

/-- Whether a Core name survives being wrapped in guillemets.

Everything does except a name containing `»`, which would close the quotation
early. Laurel does not produce such names, but emitting one would silently
generate a different declaration than the one intended. -/
def isQuotable (s : String) : Bool := !s.isEmpty && !(s.toList.contains '»')

/-- The parameter name standing for a base type with no Lean image. -/
def paramName (ty : String) : String := s!"«$p_{ty}»"

/-- Render a Core field type as Lean source.

`bool` becomes `Prop` rather than `Bool`, matching how `denotePrimSort`
interprets it, so a generated type lines up with the rest of the denotation.
*params* names base types carried as parameters of the block; a generated
datatype reference is applied to all of them, so the block stays uniform.
`none` means the type has no image and no parameter either. -/
partial def renderTy (known params : List String) : LMonoTy → Option String
  | .tcons "int" [] => some "Int"
  | .tcons "bool" [] => some "Prop"
  | .tcons "string" [] => some "String"
  | .bitvec n => some s!"(BitVec {n})"
  -- A map denotes to a function; whether that is legal depends on where the
  -- datatypes in it sit, which `mentionedNegatively` decides per group.
  | .tcons "Map" [k, v] => do
    let k ← renderTy known params k
    let v ← renderTy known params v
    return s!"({k} → {v})"
  | .tcons name [] =>
    if known.contains name then
      some (applied params (typeName name))
    else if params.contains name then some (paramName name)
    else none
  | _ => none
where
  /-- A generated type applied to the block's parameters. -/
  applied (params : List String) (base : String) : String :=
    if params.isEmpty then base
    else "(" ++ base ++ " " ++ " ".intercalate (params.map paramName) ++ ")"

/-- Base types appearing in the datatypes that have no Lean image.

These become parameters of the generated block. Only nullary constructors
qualify; anything else is a shape we do not know how to abstract. -/
partial def openBaseTypes (known : List String) (datatypes : List (LDatatype CoreIDMeta)) :
    List String :=
  (datatypes.flatMap fun d => d.constrs.flatMap fun c =>
    c.args.flatMap fun (_, ty) => go ty) |>.eraseDups
where
  go : LMonoTy → List String
    | .tcons "int" [] | .tcons "bool" [] | .tcons "string" [] => []
    | .tcons "Map" [k, v] => go k ++ go v
    | .tcons n [] => if known.contains n then [] else [n]
    | .tcons _ args => args.flatMap go
    | _ => []

/-- Datatype names mentioned anywhere in a type. -/
partial def mentioned : LMonoTy → List String
  | .tcons n args => n :: args.flatMap mentioned
  | _ => []

/-- Datatype names mentioned to the left of an arrow.

A `Map k v` denotes to `k → v`, so anything in `k` lands in a negative position.
Lean rejects an inductive that occurs negatively *within its own mutual block*,
which is why this is computed per group rather than globally. -/
partial def mentionedNegatively : LMonoTy → List String
  | .tcons "Map" [k, v] => mentioned k ++ mentionedNegatively v
  | .tcons _ args => args.flatMap mentionedNegatively
  | _ => []

/-- The datatypes one datatype refers to. -/
def dependencies (known : List String) (d : LDatatype CoreIDMeta) : List String :=
  (d.constrs.flatMap fun c => c.args.flatMap fun (_, ty) => mentioned ty)
    |>.filter known.contains |>.eraseDups

/-- Whether two datatypes must share a block: each reachable from the other. -/
def mutuallyRecursive (deps : String → List String) (fuel : Nat) (a b : String) : Bool :=
  a == b || (reaches a b && reaches b a)
where
  reaches (from_ to_ : String) : Bool :=
    let rec go (fuel : Nat) (seen frontier : List String) : Bool :=
      match fuel with
      | 0 => false
      | fuel + 1 =>
        if frontier.contains to_ then true
        else
          let next := (frontier.flatMap deps).filter (fun x => !seen.contains x) |>.eraseDups
          if next.isEmpty then false else go fuel (seen ++ next) next
    go fuel [] (deps from_)

/-- Group the datatypes into mutually recursive blocks, dependencies first.

Emitting every datatype in one `mutual` block does not work. Laurel's `Heap`
carries a `Map Composite ..`, so `Composite` sits in a negative position; if
`Composite` shares `Heap`'s block Lean rejects the whole thing, even though
`Composite` does not depend on `Heap` and could simply be declared first.

Groups are the mutually-reachable components, ordered so a group's dependencies
are already declared. Negative occurrence *within* a group remains fatal and is
reported by `blockText`. -/
def dependencyGroups (datatypes : List (LDatatype CoreIDMeta)) :
    List (List (LDatatype CoreIDMeta)) :=
  let names := datatypes.map (·.name)
  let deps := fun n =>
    match datatypes.find? (·.name == n) with
    | some d => dependencies names d
    | none => []
  let sameGroup := mutuallyRecursive deps names.length
  let rec build (remaining : List (LDatatype CoreIDMeta)) (done : List String)
      (acc : List (List (LDatatype CoreIDMeta))) (fuel : Nat) :
      List (List (LDatatype CoreIDMeta)) :=
    match fuel, remaining with
    | 0, _ => acc.reverse ++ [remaining]
    | _, [] => acc.reverse
    | fuel + 1, _ =>
      let groupOf := fun (e : LDatatype CoreIDMeta) =>
        remaining.filter (fun f => sameGroup e.name f.name)
      -- A group is ready when every dependency outside it is already declared.
      let ready := remaining.find? fun e =>
        let g := groupOf e
        let gn := g.map (·.name)
        g.all fun f =>
          (dependencies names f).all fun x => gn.contains x || done.contains x
      match ready with
      | none => acc.reverse ++ [remaining]
      | some e =>
        let chosen := groupOf e
        let chosenNames := chosen.map (·.name)
        build (remaining.filter fun f => !chosenNames.contains f.name)
          (done ++ chosenNames) (chosen :: acc) fuel
  build datatypes [] [] (datatypes.length + 1)

/-- One constructor, as a line of an `inductive` block. -/
def renderCtor (known params : List String) (dt : String) (c : LConstr CoreIDMeta) :
    Option String := do
  let fields ← c.args.foldlM (init := #[]) fun acc (field, ty) => do
    guard (isQuotable field.name)
    let rendered ← renderTy known params ty
    return acc.push s!"({quoted field.name} : {rendered})"
  let binders := if fields.isEmpty then "" else " " ++ " ".intercalate fields.toList
  let self :=
    if params.isEmpty then typeName dt
    else typeName dt ++ " " ++ " ".intercalate (params.map paramName)
  return s!"  | {quoted c.name.name}{binders} : {self}"

/-- The `inductive` declarations for a program's datatypes, in dependency order.

One string per declaration -- a `mutual` block where the group really is
mutually recursive, a bare `inductive` otherwise. They are returned separately
because a parser call consumes a single command, and they must be elaborated in
the order given so each group's dependencies already exist.

Returns the reason instead when some datatype cannot be represented, so the
caller reports it rather than emitting a partial model. -/
def blockTexts (datatypes : List (LDatatype CoreIDMeta)) : Except String (List String) := do
  let usable := datatypes.filter (fun d => d.typeArgs.isEmpty)
  let names := usable.map (·.name)
  let params := openBaseTypes names usable
  let paramBinder :=
    if params.isEmpty then ""
    else " (" ++ " ".intercalate (params.map paramName) ++ " : Type)"
  for d in datatypes do
    if !d.typeArgs.isEmpty then
      throw s!"datatype {d.name} is polymorphic, which the ground type language cannot express"
    if !isQuotable d.name then
      throw s!"datatype name {d.name} cannot be quoted as a Lean identifier"
    for c in d.constrs do
      if !isQuotable c.name.name then
        throw s!"constructor {c.name.name} of {d.name} cannot be quoted as a Lean identifier"
  let mut out := #[]
  for group in dependencyGroups usable do
    let groupNames := group.map (·.name)
    let mut blocks := #[]
    for d in group do
      -- Only occurrences within this group matter: a type declared in an
      -- earlier block may appear negatively without trouble.
      for c in d.constrs do
        for (_, ty) in c.args do
          for n in mentionedNegatively ty do
            if groupNames.contains n then
              throw s!"{n} occurs negatively in {c.name.name} of {d.name}, which Lean rejects"
      let mut lines := #[s!"inductive {typeName d.name}{paramBinder} where"]
      for c in d.constrs do
        match renderCtor names params d.name c with
        | none => throw s!"a field of {c.name.name} in {d.name} has no Lean type"
        | some line => lines := lines.push line
      blocks := blocks.push ("\n".intercalate lines.toList)
    if blocks.isEmpty then continue
    -- A `mutual` wrapper is only needed when the group really is mutual.
    out := out.push <|
      if blocks.size == 1 then blocks[0]!
      else "mutual\n" ++ "\n".intercalate blocks.toList ++ "\nend"
  if out.isEmpty then throw "no datatypes to generate"
  return out.toList

/-! ## Operations

The type alone is not enough: the obligations talk about a datatype through its
tag, its constructors and its selectors. Generated as ordinary `match`
definitions, those compute, which is the whole point -- `cases v` on a symbolic
value leaves a concrete constructor in each branch and every tag test reduces by
`rfl`. Under the uninterpreted encoding the same dispatch was simply stuck.
-/

/-- Every generated type needs `Inhabited`, since a selector must be total and
returns `default` outside its own constructor. -/
def inhabitedText (group : List (LDatatype CoreIDMeta)) : String :=
  "deriving instance Inhabited for " ++ ", ".intercalate (group.map (typeName ·.name))

/-- Binders carrying the block's parameters into an operation. -/
private def opBinders (params : List String) : String :=
  if params.isEmpty then ""
  else
    let names := " ".intercalate (params.map paramName)
    let inh := " ".intercalate (params.map fun p => "[Inhabited " ++ paramName p ++ "]")
    " {" ++ names ++ " : Type} " ++ inh

/-- The datatype applied to its parameters. -/
private def applyParams (params : List String) (dt : String) : String :=
  if params.isEmpty then typeName dt
  else typeName dt ++ " " ++ " ".intercalate (params.map paramName)

/-- Wildcards for one constructor's fields, for a non-matching branch. -/
private def wildcards (c : LConstr CoreIDMeta) : String :=
  String.join (c.args.map fun _ => " _")

/-- `tag`, mapping a value to the index of the constructor that built it.

The index is the constructor's position, matching what `DatatypeEncoding`
rewrites a tester to, so the two encodings agree on what a tag means. -/
def tagDefText (params : List String) (d : LDatatype CoreIDMeta) : String :=
  let header :=
    "def " ++ typeName d.name ++ ".tag" ++ opBinders params ++ " : " ++
    applyParams params d.name ++ " → Int"
  let arms := d.constrs.zipIdx.map fun (c, i) =>
    "  | ." ++ quoted c.name.name ++ wildcards c ++ " => " ++ toString i
  "\n".intercalate (header :: arms)

/-- One selector, total, returning `default` off its own constructor.

Core selectors are partial in the same way -- `Any..as_int` says nothing about a
value that is not an integer -- so a default loses nothing that was there. -/
def selectorDefText (known params : List String) (d : LDatatype CoreIDMeta)
    (owner : LConstr CoreIDMeta) (field : String) (ty : LMonoTy) : Option String := do
  let rendered ← renderTy known params ty
  let header :=
    "def " ++ typeName d.name ++ "." ++ quoted field ++ opBinders params ++ " : " ++
    applyParams params d.name ++ " → " ++ rendered
  let hit := "  | ." ++ quoted owner.name.name ++
    String.join (owner.args.map fun (f, _) =>
      if f.name == field then " " ++ quoted field else " _") ++
    " => " ++ quoted field
  let miss := if d.constrs.length == 1 then "" else "\n  | _ => default"
  return header ++ "\n" ++ hit ++ miss

/-- Tag and selector definitions for one group, in declaration order.

A field name is taken from the first constructor that declares it: Core keeps
selector names unique within a datatype, so a repeat would be the same selector.
-/
def operationTexts (known params : List String) (group : List (LDatatype CoreIDMeta)) :
    Except String (List String) := do
  let mut out := #[inhabitedText group]
  for d in group do
    out := out.push (tagDefText params d)
    let mut seen : List String := []
    for c in d.constrs do
      for (field, ty) in c.args do
        if seen.contains field.name then continue
        seen := field.name :: seen
        match selectorDefText known params d c field.name ty with
        | none => throw s!"selector {field.name} of {d.name} has no Lean type"
        | some t => out := out.push t
  return out.toList

end Strata.SMT.DatatypeInductive
