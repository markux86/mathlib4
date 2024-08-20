import Mathlib.Util.AssertExists

/-- info: No assertions made. -/
#guard_msgs in
#check_assertions

/-- warning: the module 'Lean.Elab.Command' is (transitively) imported -/
#guard_msgs in
assert_not_imported
  Mathlib.Tactic.Common
  Lean.Elab.Command
  I_do_not_exist

assert_not_exists Nats

theorem Nats : True := .intro

/--
warning: ❌ 'Mathlib.Tactic.Common' (module) asserted in 'test.AssertExists'.
---
warning: ❌ 'I_do_not_exist' (module) asserted in 'test.AssertExists'.
---
info: ✅ 'Nats' (declaration) asserted in 'test.AssertExists'.
---
info: ✅ means the declaration or import exists.
❌ means the declaration or import does not exist.
-/
#guard_msgs in
#check_assertions
