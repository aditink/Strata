/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core
import StrataDDM.Integration.Lean.HashCommands
import Strata.MetaVerifier

/-! # Signature-only encoding of algebraic datatypes

`gen_smt_vcs` previously could not state a goal about any program declaring a
datatype: `denoteQuery` refused such contexts outright. `SMT.DatatypeEncoding`
gives each datatype an uninterpreted sort and uninterpreted functions for its
constructors, selectors, and tag, which the existing denotation already handles.

It asserts nothing. An earlier version emitted the datatype laws as axioms and
that set was contradictory on the Laurel prelude, so `1 == 2` became provable.
The consistency test below is the regression guard for that, and it is the more
important of the two tests here.
-/

open StrataDDM (Program)
namespace Strata

private def tagPgm : Program :=
#strata
program Core;
datatype Val { VInt(getInt : int), VBool(getBool : bool), VNone() };
procedure unwrapOr (v : Val, dflt : int, out r : int)
spec {
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

-- One uninterpreted sort for the datatype, and functions for its constructors,
-- selectors and tag. Testers are not functions: `Val..isVInt v` is rewritten to
-- `$dt.tag.Val v = 0`.
/--
info: sorts: #[{ name := "Val", arity := 0 }]
functions: #["$dt.tag.Val", "VInt", "VBool", "VNone", "Val..getInt", "Val..getBool", "v@1"]
-/
#guard_msgs in
#eval show IO Unit from do
  let some vcs := genSMTVCs tagPgm | IO.println "no VCs"
  let (_, ctx, _, _) := vcs[0]!
  IO.println s!"sorts: {repr ctx.sorts}"
  IO.println s!"functions: {repr (ctx.ufs.map (fun u => u.id))}"

/-- Consistency. Nothing is asserted about the datatype, so a plainly false
postcondition must stay unprovable. This is the test that would have caught the
axiomatic encoding: under it, this goal was provable. -/
private def absurdPgm : Program :=
#strata
program Core;
datatype Val { VInt(getInt : int), VBool(getBool : bool), VNone() };
procedure unwrapOr (v : Val, dflt : int, out r : int)
spec {
  ensures [absurd]: 1 == 2;
}
{
  $return: {
    if (Val..isVInt(v)) { r := Val..getInt(v); exit $return; }
    r := dflt;
    exit $return;
  }
};
#end

set_option maxRecDepth 1000000 in
example : True := by
  fail_if_success
    (have : smtVCsCorrect absurdPgm (options := { onlyLabels := some ["absurd"] }) := by
      gen_smt_vcs
      all_goals (intros; grind (splits := 100) (instances := 100000) (ematch := 100)))
  trivial

-- Control-flow reasoning still works without any datatype laws: on the branch
-- where the guard held, the postcondition is the assignment just made, so it
-- follows by equality alone.
set_option maxRecDepth 1000000 in
theorem tagPgm_passthrough :
    smtVCsCorrect tagPgm (options := { onlyLabels := some ["int_passthrough"] }) := by
  gen_smt_vcs
  all_goals (intros; grind (splits := 100) (instances := 100000) (ematch := 100))

/-- What asserting nothing costs.

Core's own symbolic evaluator resolves a tester applied to a literal
constructor, so `Val..isVInt(VInt(n))` never reaches SMT and needs no law --
which is why the encoding stays useful. What it cannot resolve is a tester on a
*symbolic* scrutinee. Exhaustiveness over an arbitrary `v` needs the tag to be
one of the three, and no such fact exists here.

That is exactly the shape the Laurel coercions take -- a dozen tag tests on a
symbolic value -- so this is the gap that matters in practice, and the reason to
denote `Val` as a real inductive, where exhaustiveness is a theorem. -/
private def exhaustivePgm : Program :=
#strata
program Core;
datatype Val { VInt(getInt : int), VBool(getBool : bool), VNone() };
procedure classify (v : Val, out n : int)
spec {
  ensures [exhaustive]: Val..isVInt(v) || Val..isVBool(v) || Val..isVNone(v);
}
{
  $return: {
    n := 0;
    exit $return;
  }
};
#end

set_option maxRecDepth 1000000 in
example : True := by
  fail_if_success
    (have : smtVCsCorrect exhaustivePgm (options := { onlyLabels := some ["exhaustive"] }) := by
      gen_smt_vcs
      all_goals (intros; grind (splits := 100) (instances := 100000) (ematch := 100)))
  trivial

end Strata
