/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core
import StrataDDM.Integration.Lean.HashCommands
import Strata.MetaVerifier

/-! # Deductive verification of a program using an algebraic datatype

`gen_smt_vcs` previously could not state a goal about any program declaring a
datatype: `denoteQuery` refused such contexts outright. `SMT.DatatypeEncoding`
replaces the datatype theory with an uninterpreted sort, uninterpreted
constructor/tester/selector functions, and axioms relating them, which the
existing denotation machinery already handles.
-/

open StrataDDM (Program)
namespace Strata

/-- A tagged union, in the shape a dynamic-language frontend produces. -/
private def tagPgm : Program :=
#strata
program Core;
datatype Val {
  VInt(getInt : int),
  VBool(getBool : bool),
  VNone()
};
procedure unwrapOr (v : Val, dflt : int, out r : int)
spec {
  ensures [not_int]: Val..isVBool(v) ==> r == dflt;
  ensures [int_passthrough]: Val..isVInt(v) ==> r == Val..getInt(v);
}
{
  $return: {
    if (Val..isVInt(v)) { r := Val..getInt(v); exit $return; }
    r := dflt;
    exit $return;
  }
};
#end

-- The datatype becomes one uninterpreted sort; its constructors and selectors
-- become uninterpreted functions alongside the program's own variables. There
-- are no tester functions: `Val..isVInt v` is rewritten to `$dt.tag.Val v = 0`.
/--
info: sorts: #[{ name := "Val", arity := 0 }]
functions: #["v@1", "dflt@1", "$dt.tag.Val", "VInt", "VBool", "VNone", "Val..getInt", "Val..getBool"]
-/
#guard_msgs in
#eval show IO Unit from do
  let some vcs := genSMTVCs tagPgm | IO.println "no VCs"
  let (_, ctx, _, _) := vcs[0]!
  IO.println s!"sorts: {repr ctx.sorts}"
  IO.println s!"functions: {repr (ctx.ufs.map (fun u => u.id))}"

/-- Both postconditions follow from the datatype axioms alone -- no solver. -/
theorem tagPgm_correct : smtVCsCorrect tagPgm := by
  gen_smt_vcs
  all_goals grind

/-- Negative control. The same program with a postcondition that is false must
stay unprovable: an inconsistent axiomatization would discharge this too. -/
private def bogusPgm : Program :=
#strata
program Core;
datatype Val {
  VInt(getInt : int),
  VBool(getBool : bool),
  VNone()
};
procedure unwrapOr (v : Val, dflt : int, out r : int)
spec {
  ensures [bogus]: Val..isVInt(v) ==> r == int.add(Val..getInt(v), 1);
}
{
  $return: {
    if (Val..isVInt(v)) { r := Val..getInt(v); exit $return; }
    r := dflt;
    exit $return;
  }
};
#end

example : True := by
  fail_if_success
    (have : smtVCsCorrect bogusPgm := by gen_smt_vcs; all_goals grind)
  trivial

end Strata
