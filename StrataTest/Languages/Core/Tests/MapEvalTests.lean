/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core.CmdEval
meta import Strata.DL.Imperative

meta section

namespace Core.MapEvalTests

open Lambda
open Imperative

private def call (op : MapOpKind) (args : List Expression.Expr) :
    Expression.Expr :=
  LExpr.mkApp () (.op () (CoreOp.map op).toString none) args

private def constantMap (defaultValue : Int) : Expression.Expr :=
  call .Const [.intConst () defaultValue]

private def update (m : Expression.Expr) (key value : Int) :
    Expression.Expr :=
  call .Update [m, .intConst () key, .intConst () value]

private def select (m : Expression.Expr) (key : Int) : Expression.Expr :=
  call .Select [m, .intConst () key]

private def eval (e : Expression.Expr) : Expression.Expr × LExpr.EvalResult :=
  LExpr.eval 20 Factory (fun _ => none) e

private def updatedMap : Expression.Expr :=
  update (constantMap 0) 4 17

-- An immutable update is a value that can be assigned to a Map variable.
#guard (eval updatedMap).2.isValueTrue
#guard (LExpr.findStuckRedex Factory updatedMap).isNone

-- A read at the updated key returns the new value.
#guard (eval (select updatedMap 4)).1 == LExpr.intConst () 17

-- A read at another key continues through to the previous Map.
#guard (eval (select updatedMap 5)).1 == LExpr.intConst () 0

private def mapCommands : Cmds Expression :=
  [
    .init "m" (.forAll [] (mapTy .int .int))
      (.det (constantMap 0)) .empty,
    .set "m" (.det (call .Update [
      .fvar () "m" none,
      .intConst () 4,
      .intConst () 17
    ])) .empty,
    .init "result" (.forAll [] .int)
      (.det (call .Select [.fvar () "m" none, .intConst () 4])) .empty
  ]

-- Pin the command path that previously got stuck while assigning `update`.
#guard
  let (_, env) := Cmds.eval Env.init mapCommands
  env.error.isNone &&
    (env.exprEnv.state.find? "result").map (·.snd) ==
      some (LExpr.intConst () 17)

end Core.MapEvalTests

end
