/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core
import StrataDDM.Integration.Lean.HashCommands
import Strata.MetaVerifier

/-! # Verifying integer code whose obligation mentions reals

`denotePrimSort` has no Lean image for `real`, so any obligation mentioning one
was undenotable and `gen_smt_vcs` rejected it outright -- including obligations
whose actual content is about integers, which is the common case when a
dynamically typed frontend threads a float case through a value type.
`SMT.RealAbstraction` replaces the theory of reals with an uninterpreted sort,
uninterpreted constants for literals, and uninterpreted functions for the
operators, leaving the integer reasoning intact.
-/

open StrataDDM (Program)
namespace Strata

/-- A real-valued branch condition that no theory can decide, guarding a
conclusion purely about integers. Both paths survive symbolic evaluation, so
the real reaches the obligation. -/
private def guardedPgm : Program :=
#strata
program Core;
procedure classify (r : real, out i : int)
spec {
  ensures [in_range]: int.le(0, i) && int.le(i, 1);
}
{
  $return: {
    if (r == 0.0) { i := 0; exit $return; }
    i := 1;
    exit $return;
  }
};
#end

-- `real` becomes an uninterpreted sort and the literal an uninterpreted
-- constant over it.
/--
info: in_range: sorts=#[{ name := "$Real", arity := 0 }] ufs=#["r@1", "$real.lit.0e0"]
in_range: sorts=#[{ name := "$Real", arity := 0 }] ufs=#["r@1", "$real.lit.0e0"]
-/
#guard_msgs in
#eval show IO Unit from do
  let some vcs := genSMTVCs guardedPgm | IO.println "no VCs"
  for (label, ctx, _, _) in vcs do
    IO.println s!"{label}: sorts={repr ctx.sorts} ufs={repr (ctx.ufs.map (fun u => u.id))}"

set_option maxRecDepth 100000 in
theorem guardedPgm_correct : smtVCsCorrect guardedPgm := by
  gen_smt_vcs
  all_goals grind

/-- Negative control. The abstraction knows nothing about real arithmetic, so a
conclusion that genuinely depends on it must stay unprovable. Were it provable,
the abstraction would be unsound rather than merely incomplete. -/
private def realArithPgm : Program :=
#strata
program Core;
procedure addTwice (r : real, out y : real)
spec {
  ensures [same]: y == real.mul(r, 2.0);
}
{
  $return: {
    y := real.add(r, r);
    exit $return;
  }
};
#end

set_option maxRecDepth 100000 in
example : True := by
  fail_if_success
    (have : smtVCsCorrect realArithPgm := by gen_smt_vcs; all_goals grind)
  trivial

end Strata
