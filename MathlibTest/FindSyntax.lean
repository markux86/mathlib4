import Mathlib.Tactic.FindSyntax

/--
info: Found 1 use among 529 syntax declarations
---

«term_∘_»:
  '∘'

---
-/
#guard_msgs in
#find_syntax "∘"  -- an `infixr`

/--
info: Found 1 use among 529 syntax declarations
---

«term_∣_»:
  '∣'

---
-/
#guard_msgs in
#find_syntax "∣"  -- an `infix`

/--
info: Found 2 uses among 529 syntax declarations
---

«stx_,*»:
  ',*'

---

«stx_,*,?»:
  ',*,?'

---
-/
#guard_msgs in
#find_syntax ",*"  -- generated by a `macro`

/--
info: Found 1 use among 529 syntax declarations
---

«term~~~_»:
  '~~~'

---
-/
#guard_msgs in
#find_syntax "~~~"  -- a `prefix`

/--
info: Found 4 uses among 529 syntax declarations
---

Lean.Parser.Tactic.refine':
  'refine''

---

Lean.Parser.Tactic.tacticRefine_lift'_:
  'refine_lift''

---

Lean.Parser.Tactic.tacticRefine_lift_:
  'refine_lift'

---

Lean.Parser.Tactic.refine:
  'refine'

---
-/
#guard_msgs in
#find_syntax "refine" -- a `nonReservedSymbol`
