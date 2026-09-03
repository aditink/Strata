/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.SMTEncoder

/-! # Axiomatic encoding of algebraic datatypes

`Strata.DL.SMT.Denote.denoteQuery` has no interpretation for datatypes: it
refuses any context whose datatype machinery is populated, and `Op.datatype_op`
has no denotation. Solvers get datatypes natively, so nothing else needed this.
The metaverifier does: a frontend that models its values as one tagged union --
Laurel/Python is the motivating case, where every value has type `Any` -- emits
nothing but datatype operations, so `gen_smt_vcs` cannot state a single goal
about it.

This module removes the datatype theory instead of interpreting it. Each
datatype becomes an uninterpreted sort, each constructor, tester, and selector
becomes an uninterpreted function, and the theory's content is recovered as
explicit axioms over those functions. Since `denoteQuery` already interprets
uninterpreted sorts, uninterpreted functions, and axioms, the result needs no
new denotation machinery.

## What is and is not captured

The axioms in `datatypeAxioms` say that the constructors tile the sort: testers
are exhaustive and mutually exclusive, selectors invert their constructor, and a
value satisfying a tester is that constructor applied to its own selectors.
Together these give injectivity and disjointness of constructors.

They deliberately omit any *induction* principle, and with it acyclicity. So a
recursive datatype is modelled as its possibly-infinite completion: for
`ListAny`, the axioms are all satisfied by an infinite list, and a property
provable only by structural induction stays out of reach. This is sound -- every
theorem proved from these axioms holds of the real datatype -- but incomplete.
For a tagged union like `Any` the axioms are complete in practice, since the
interesting facts are about which tag holds and what it carries.

Polymorphic datatypes are skipped: their field types mention type variables that
the ground `TermType` language cannot express. All of the Laurel prelude's
datatypes are monomorphic.
-/

public section

namespace Strata.SMT.DatatypeEncoding

open Strata.SMT Lambda

/-- Metadata parameter of Core identifiers; `Core` alone resolves to the DDM
dialect value of the same name. -/
abbrev CoreIDMeta := _root_.Core.CoreLParams.IDMeta

/-- Encoding context, abbreviated for the same reason. -/
abbrev CoreCtx := _root_.Core.SMT.Context

/-- The uninterpreted function standing for a constructor.

Named after the constructor, matching what `Op.datatype_op .constructor`
carries. Core forbids a function and a constructor sharing a name, so this
cannot capture a user function. -/
def ctorName (constr : String) : String := constr

/-- The uninterpreted predicate standing for a constructor's tester.

`Op.datatype_op .tester` carries the *constructor* name, not the tester name, so
this derives the same name the encoder would have emitted to the solver. `-` is
not legal in a Core identifier, so this cannot collide with a user function. -/
def testerName (constr : String) : String := "is-" ++ constr

/-- The uninterpreted function standing for a selector.

`Op.datatype_op .selector` already carries the qualified `Datatype..field`
form, which is unique and cannot collide with a user function. -/
def selectorName (datatype field : String) : String := datatype ++ ".." ++ field

/-- The declarations and axioms modelling one program's datatypes. -/
structure Encoding where
  sorts : Array Strata.DL.SMT.Sort := #[]
  ufs : Array UF := #[]
  axms : Array Term := #[]
deriving Inhabited

/-- A monomorphic datatype's own sort. -/
def datatypeTy (d : LDatatype CoreIDMeta) : TermType :=
  .constr d.name []

/-- Whether a payload type can be given a denotation, possibly after later
abstraction passes.

Reals count as denotable even though `denotePrimSort` rejects them:
`SMT.RealAbstraction` runs downstream and turns them into an uninterpreted
sort, and it rewrites the signatures produced here in step with the terms.
Regexes and triggers have no such treatment, so a constructor carrying one is
still given a tester and nothing else -- see `constrFuns`. -/
partial def denotableTy : TermType → Bool
  | .prim .regex | .prim .trigger => false
  | .prim _ => true
  | .option ty => denotableTy ty
  | .constr _ args => args.all denotableTy

/-- Field types of one constructor, in declaration order.

Returns `none` when a field's type has no denotable `TermType` image, which is
how a real-carrying or polymorphic constructor drops out. -/
def constrFieldTys (c : LConstr CoreIDMeta) (ctx : CoreCtx) :
    Option (List TermType × CoreCtx) :=
  go c.args ctx []
where
  go (args : List (Identifier CoreIDMeta × LMonoTy)) (ctx : CoreCtx)
      (acc : List TermType) : Option (List TermType × CoreCtx) :=
    match args with
    | [] => some (acc.reverse, ctx)
    | (_, ty) :: rest =>
      match _root_.Core.LMonoTy.toSMTType ty ctx with
      | .error _ => none
      | .ok (ty', ctx') => if denotableTy ty' then go rest ctx' (ty' :: acc) else none

/-- Bound-variable names for one constructor's fields.

Prefixed so they cannot shadow a program variable appearing in the same axiom. -/
def fieldVarNames (c : LConstr CoreIDMeta) : List String :=
  c.args.zipIdx.map (fun (_, i) => s!"$dt_x{i}")

/-- Apply an uninterpreted function to arguments. -/
def applyUF (uf : UF) (args : List Term) : Term :=
  .app (.core (.uf uf)) args uf.out

/-- Universally quantify `body` over `vars`. -/
def forallVars (vars : List (String × TermType)) (body : Term) : Term :=
  vars.foldr
    (fun (name, ty) acc => Factory.quant .all name ty (Factory.mkSimpleTrigger name ty) acc)
    body

/-- The functions modelling one constructor.

`payload` is `none` when a field type is not denotable. Such a constructor keeps
its tester -- a predicate on the datatype's own sort, always denotable -- so it
still participates in exhaustiveness and mutual exclusivity, but gets no
constructor or selector function and no axioms that would mention one. The tag
discipline survives; only the payload becomes unreachable. -/
structure ConstrPayload where
  /-- The constructor function itself. -/
  ctor : UF
  /-- One selector per field, in declaration order. -/
  selectors : List UF
  /-- Bound variable name and type per field, for quantifying the axioms. -/
  fieldVars : List (String × TermType)

structure ConstrFuns where
  tester : UF
  payload : Option ConstrPayload

/-- Resolve one constructor's functions. Always succeeds: a constructor whose
payload is not denotable yields a tester alone. -/
def constrFuns (d : LDatatype CoreIDMeta) (c : LConstr CoreIDMeta)
    (ctx : CoreCtx) : ConstrFuns × CoreCtx :=
  let dTy := datatypeTy d
  let tester : UF :=
    { id := testerName c.name.name, args := [dTy], out := .prim .bool }
  match constrFieldTys c ctx with
  | none => ({ tester, payload := none }, ctx)
  | some (fieldTys, ctx) =>
    let ctor : UF := { id := ctorName c.name.name, args := fieldTys, out := dTy }
    let selectors :=
      (c.args.zip fieldTys).map fun ((field, _), fieldTy) =>
        ({ id := selectorName d.name field.name, args := [dTy], out := fieldTy } : UF)
    ({ tester
       payload := some { ctor, selectors, fieldVars := (fieldVarNames c).zip fieldTys } }, ctx)

/-- Axioms tying one constructor to its tester and selectors.

- `is-C (C x⃗)` -- the tester accepts its own constructor.
- `¬ is-D (C x⃗)` for every other constructor `D` -- and rejects the others.
- `sel_i (C x⃗) = x_i` -- selectors invert the constructor.

Empty for a constructor with no denotable payload: every one of these mentions
the constructor function, which does not exist in that case. -/
def constrAxioms (funs : ConstrFuns) (otherTesters : List UF) : List Term :=
  match funs.payload with
  | none => []
  | some p =>
    let args := p.fieldVars.map (fun (n, ty) => Term.var ⟨n, ty⟩)
    let applied := applyUF p.ctor args
    let ownTester := forallVars p.fieldVars (applyUF funs.tester [applied])
    let otherTesterAxioms :=
      otherTesters.map fun tester =>
        forallVars p.fieldVars (Factory.not (applyUF tester [applied]))
    let selectorAxioms :=
      (p.selectors.zip args).map fun (sel, arg) =>
        forallVars p.fieldVars (Factory.eq (applyUF sel [applied]) arg)
    ownTester :: otherTesterAxioms ++ selectorAxioms

/-- Axioms about an arbitrary value of the datatype.

- Some tester holds -- the constructors are exhaustive.
- At most one tester holds -- they are mutually exclusive.
- `is-C v → v = C (sel₁ v) … (selₖ v)` -- a value accepted by a tester is that
  constructor applied to its own selectors. With exhaustiveness this makes every
  value a constructor application, which is what gives injectivity. -/
def valueAxioms (d : LDatatype CoreIDMeta) (funs : List ConstrFuns) : List Term :=
  let dTy := datatypeTy d
  let v : Term := .var ⟨"$dt_v", dTy⟩
  let quantify (body : Term) : Term := forallVars [("$dt_v", dTy)] body
  let testers := funs.map (fun f => applyUF f.tester [v])
  let exhaustive :=
    match testers with
    | [] => []
    | t :: ts => [quantify (ts.foldl Factory.or t)]
  let exclusive :=
    (testers.zipIdx.flatMap fun (ti, i) =>
      testers.zipIdx.filterMap fun (tj, j) =>
        if i < j then some (quantify (Factory.not (Factory.and ti tj))) else none)
  let shape :=
    funs.filterMap fun f =>
      f.payload.map fun p =>
        let rebuilt := applyUF p.ctor (p.selectors.map (fun sel => applyUF sel [v]))
        quantify (Factory.implies (applyUF f.tester [v]) (Factory.eq v rebuilt))
  exhaustive ++ exclusive ++ shape

/-- Encode every monomorphic datatype in `ctx` as sorts, functions, and axioms.

Threads `ctx` because converting a field type can register further sorts. -/
def encode (ctx : CoreCtx) : Encoding :=
  ctx.datatypes.factory.allDatatypes.foldl (init := {}) fun enc d =>
    if !d.typeArgs.isEmpty then enc else
    let funs := collectConstrs d d.constrs ctx []
    let testers := funs.map (·.tester)
    let perConstr :=
      funs.zipIdx.flatMap fun (f, i) =>
        constrAxioms f (testers.zipIdx.filterMap fun (t, j) =>
          if i == j then none else some t)
    { sorts := enc.sorts.push { name := d.name, arity := 0 }
      ufs := enc.ufs
        ++ (funs.filterMap (fun f => f.payload.map (·.ctor))).toArray
        ++ testers.toArray
        ++ (funs.flatMap (fun f => (f.payload.map (·.selectors)).getD [])).toArray
      axms := enc.axms ++ (perConstr ++ valueAxioms d funs).toArray }
where
  collectConstrs (d : LDatatype CoreIDMeta)
      (cs : List (LConstr CoreIDMeta)) (ctx : CoreCtx)
      (acc : List ConstrFuns) : List ConstrFuns :=
    match cs with
    | [] => acc.reverse
    | c :: rest =>
      let (funs, ctx') := constrFuns d c ctx
      collectConstrs d rest ctx' (funs :: acc)

/-- Look up the uninterpreted function a datatype operation stands for.

`none` for an operation that is not one of `ctx`'s datatypes -- `Option` and set
operations reach here under the same `Op.datatype_op` head and must be left for
their own handling. -/
def resolveOp (enc : Encoding) (kind : Op.DatatypeFuncs) (name : String) : Option UF :=
  let wanted := match kind with
    | .constructor => ctorName name
    | .tester => testerName name
    | .selector => name
  enc.ufs.find? (·.id == wanted)

/-- Replace datatype operations by their uninterpreted functions.

The argument and result types already sit on the term, so the rewrite is purely
a change of head symbol. -/
partial def rewriteTerm (enc : Encoding) (t : Term) : Term :=
  match t with
  | .app (.datatype_op kind name) args retTy =>
    let args := args.map (rewriteTerm enc)
    match resolveOp enc kind name with
    | some uf => .app (.core (.uf uf)) args retTy
    | none => .app (.datatype_op kind name) args retTy
  | .app op args retTy => .app op (args.map (rewriteTerm enc)) retTy
  | .some t => .some (rewriteTerm enc t)
  | .quant qk args tr body => .quant qk args (rewriteTerm enc tr) (rewriteTerm enc body)
  | t => t

end Strata.SMT.DatatypeEncoding
