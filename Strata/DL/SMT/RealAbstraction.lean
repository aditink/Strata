/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.SMTEncoder

/-! # Abstracting the theory of reals

`denotePrimSort` has no Lean image for `.real`: Strata cannot depend on
Mathlib, so there is no real type to denote into. Any obligation mentioning a
real is therefore undenotable, and `gen_smt_vcs` rejects it.

That is a hard stop for a frontend whose value type merely *has* a floating
point case, even when the code under verification never touches one. The Laurel
encoding of Python is the motivating example: `Any` carries a
`from_float(as_float : real)` constructor, and the coercion `Any_to_bool`
inlines `as_float(v) == 0.0` into the obligation, so `real` reaches the goal of
a procedure that only ever manipulates integers.

This module replaces the theory of reals with an uninterpreted one. `real`
becomes an uninterpreted sort, each real literal becomes an uninterpreted
constant of that sort, and each arithmetic or comparison operator applied at
real type becomes an uninterpreted function. Equality and `ite` are already
sort-polymorphic and need no special handling.

## Soundness and its price

The abstraction only ever *removes* facts, so a proof of the abstracted
obligation is a proof of the original: the abstracted form quantifies over
every interpretation of the new sort and functions, of which the intended reals
are one.

The price is that no arithmetic on reals is provable, and distinct literals are
no longer distinct -- `0.0 = 1.0` is neither provable nor refutable. Anything
genuinely about floating point values stays out of reach. What this does buy is
that integer reasoning is no longer held hostage by an unreachable float branch
sitting elsewhere in the same obligation.
-/

public section

namespace Strata.SMT.RealAbstraction

open Strata.SMT

/-- Name of the sort standing in for `real`.

`$` is not legal in a Core identifier, so this cannot collide with a user sort. -/
def realSortName : String := "$Real"

/-- The uninterpreted sort standing in for `real`. -/
def realTy : TermType := .constr realSortName []

/-- Replace every occurrence of `real` by the uninterpreted sort. -/
partial def abstractTy : TermType → TermType
  | .prim .real => realTy
  | .prim p => .prim p
  | .option ty => .option (abstractTy ty)
  | .constr id args => .constr id (args.map abstractTy)

/-- Whether an already-abstracted type mentions the stand-in sort. -/
partial def mentionsRealSort : TermType → Bool
  | .prim _ => false
  | .option ty => mentionsRealSort ty
  | .constr id args => id == realSortName || args.any mentionsRealSort

/-- Stable name for the constant standing in for a real literal.

Keyed on the decimal's own digits, so equal literals share a constant and
unequal ones do not. They are still not provably distinct -- nothing constrains
these constants -- but they are at least not conflated. -/
def literalName (d : StrataDDM.Decimal) : String :=
  s!"$real.lit.{d.mantissa}e{d.exponent}"

/-- Suffix identifying a numeric operator. -/
def numOpName : Op.Num → String
  | .neg => "neg" | .sub => "sub" | .add => "add" | .mul => "mul"
  | .div => "div" | .rdiv => "rdiv" | .mod => "mod" | .abs => "abs"
  | .le => "le" | .lt => "lt" | .ge => "ge" | .gt => "gt"

/-- The uninterpreted constant standing in for a real literal. -/
def literalUF (d : StrataDDM.Decimal) : UF :=
  { id := literalName d, args := [], out := realTy }

/-- The uninterpreted function standing in for a numeric operator used at real
type. The signature comes from the application site, already abstracted. -/
def numOpUF (k : Op.Num) (argTys : List TermType) (retTy : TermType) : UF :=
  { id := s!"$real.{numOpName k}", args := argTys, out := retTy }

/-- Declarations introduced by abstracting one obligation. -/
structure Abstraction where
  sorts : Array Strata.DL.SMT.Sort := #[]
  ufs : Array UF := #[]
deriving Inhabited

/-- Rewrite a term, replacing real literals and real-typed numeric operators by
applications of uninterpreted functions and abstracting every type it carries. -/
partial def abstractTerm : Term → Term
  | .prim (.real d) => .app (.core (.uf (literalUF d))) [] realTy
  | .prim p => .prim p
  | .var v => .var { v with ty := abstractTy v.ty }
  | .none ty => .none (abstractTy ty)
  | .some t => .some (abstractTerm t)
  | .app (.num k) args retTy =>
    let argTys := args.map (fun a => abstractTy a.typeOf)
    let retTy := abstractTy retTy
    let args := args.map abstractTerm
    -- Only real applications are abstracted; integer arithmetic keeps its
    -- denotation, which is the whole point of doing this per-application
    -- rather than per-operator.
    if argTys.any (· == realTy) || retTy == realTy then
      .app (.core (.uf (numOpUF k argTys retTy))) args retTy
    else
      .app (.num k) args retTy
  | .app (.core (.uf u)) args retTy =>
    .app (.core (.uf { u with args := u.args.map abstractTy, out := abstractTy u.out }))
      (args.map abstractTerm) (abstractTy retTy)
  | .app op args retTy => .app op (args.map abstractTerm) (abstractTy retTy)
  | .quant qk vars tr body =>
    .quant qk (vars.map (fun v => { v with ty := abstractTy v.ty }))
      (abstractTerm tr) (abstractTerm body)

/-- Collect the uninterpreted functions an abstracted term refers to.

Run over the *abstracted* term, so it simply reports the real-standing
functions that `abstractTerm` introduced. -/
partial def collectUFs : Term → Array UF
  | .app (.core (.uf u)) args _ =>
    let rest := args.foldl (fun acc a => acc ++ collectUFs a) #[]
    if u.id.startsWith "$real." then rest.push u else rest
  | .app _ args _ => args.foldl (fun acc a => acc ++ collectUFs a) #[]
  | .some t => collectUFs t
  | .quant _ _ tr body => collectUFs tr ++ collectUFs body
  | _ => #[]

/-- Abstract every term of one obligation, reporting the declarations needed.

`extraUFs` are context-level signatures (uninterpreted functions already
declared for the obligation) whose types must be abstracted in step with the
terms, or an application would disagree with its own declaration. -/
def abstractAll (terms : Array Term) (extraUFs : Array UF) :
    Array Term × Array UF × Abstraction :=
  let terms := terms.map abstractTerm
  let extraUFs := extraUFs.map fun u =>
    { u with args := u.args.map abstractTy, out := abstractTy u.out }
  let introduced := terms.foldl (fun acc t => acc ++ collectUFs t) #[]
  -- Deduplicate: one constant per literal, one function per operator signature.
  let deduped := introduced.foldl (init := #[]) fun acc u =>
    if acc.contains u then acc else acc.push u
  let needsSort :=
    deduped.size != 0
      || extraUFs.any (fun u => u.args.any mentionsRealSort || mentionsRealSort u.out)
  ( terms
  , extraUFs
  , { sorts := if needsSort then #[{ name := realSortName, arity := 0 }] else #[]
      ufs := deduped } )

end Strata.SMT.RealAbstraction
