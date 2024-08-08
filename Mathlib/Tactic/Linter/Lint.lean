/-
Copyright (c) 2023 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import Lean.Linter.Util
import Batteries.Data.String.Matcher
import Batteries.Tactic.Lint

/-!
# Linters for Mathlib

In this file we define additional linters for mathlib.

Perhaps these should be moved to Batteries in the future.
-/

namespace Std.Tactic.Lint
open Lean Meta

/--
Linter that checks whether a structure should be in Prop.
-/
@[env_linter] def structureInType : Linter where
  noErrorsFound := "no structures that should be in Prop found."
  errorsFound := "FOUND STRUCTURES THAT SHOULD BE IN PROP."
  test declName := do
    unless isStructure (← getEnv) declName do return none
    -- remark: using `Lean.Meta.isProp` doesn't suffice here, because it doesn't (always?)
    -- recognize predicates as propositional.
    let isProp ← forallTelescopeReducing (← inferType (← mkConstWithLevelParams declName))
      fun _ ty => return ty == .sort .zero
    if isProp then return none
    let projs := (getStructureInfo? (← getEnv) declName).get!.fieldNames
    if projs.isEmpty then return none -- don't flag empty structures
    let allProofs ← projs.allM (do isProof <| ← mkConstWithLevelParams <| declName ++ ·)
    unless allProofs do return none
    return m!"all fields are propositional but the structure isn't."

/-- Linter that check that all `deprecated` tags come with `since` dates. -/
@[env_linter] def deprecatedNoSince : Linter where
  noErrorsFound := "no `deprecated` tags without `since` dates."
  errorsFound := "FOUND `deprecated` tags without `since` dates."
  test declName := do
    let some info := Lean.Linter.deprecatedAttr.getParam? (← getEnv) declName | return none
    match info.since? with
    | some _ => return none -- TODO: enforce `YYYY-MM-DD` format
    | none => return m!"`deprecated` attribute without `since` date"

end Std.Tactic.Lint

namespace Mathlib.Linter

/-!
#  `dupNamespace` linter

The `dupNamespace` linter produces a warning when a declaration contains the same namespace
at least twice consecutively.

For instance, `Nat.Nat.foo` and `One.two.two` trigger a warning, while `Nat.One.Nat` does not.
-/

/--
The `dupNamespace` linter is set on by default.  Lean emits a warning on any declaration that
contains the same namespace at least twice consecutively.

For instance, `Nat.Nat.foo` and `One.two.two` trigger a warning, while `Nat.One.Nat` does not.

*Note.*
This linter will not detect duplication in namespaces of autogenerated declarations
(other than the one whose `declId` is present in the source declaration).
-/
register_option linter.dupNamespace : Bool := {
  defValue := true
  descr := "enable the duplicated namespace linter"
}

namespace DupNamespaceLinter

open Lean Parser Elab Command Meta

/-- Gets the value of the `linter.dupNamespace` option. -/
def getLinterDupNamespace (o : Options) : Bool := Linter.getLinterValue linter.dupNamespace o

/-- `getIds stx` extracts the `declId` nodes from the `Syntax` `stx`.
If `stx` is an `alias` or an `export`, then it extracts an `ident`, instead of a `declId`. -/
partial
def getIds : Syntax → Array Syntax
  | .node _ `Batteries.Tactic.Alias.alias args => args[2:3]
  | .node _ ``Lean.Parser.Command.export args => (args[3:4] : Array Syntax).map (·[0])
  | stx@(.node _ _ args) =>
    ((args.attach.map fun ⟨a, _⟩ => getIds a).foldl (· ++ ·) #[stx]).filter (·.getKind == ``declId)
  | _ => default

@[inherit_doc linter.dupNamespace]
def dupNamespace : Linter where run := withSetOptionIn fun stx => do
  if getLinterDupNamespace (← getOptions) then
    match getIds stx with
      | #[id] =>
        let ns := (← getScope).currNamespace
        let declName := ns ++ (if id.getKind == ``declId then id[0].getId else id.getId)
        let nm := declName.components
        let some (dup, _) := nm.zip (nm.tailD []) |>.find? fun (x, y) => x == y
          | return
        Linter.logLint linter.dupNamespace id
          m!"The namespace '{dup}' is duplicated in the declaration '{declName}'"
      | _ => return

initialize addLinter dupNamespace

end DupNamespaceLinter

/-!
# The "missing end" linter

The "missing end" linter emits a warning on non-closed `section`s and `namespace`s.
It allows the "outermost" `noncomputable section` to be left open (whether or not it is named).
-/

open Lean Elab Command

/-- The "missing end" linter emits a warning on non-closed `section`s and `namespace`s.
It allows the "outermost" `noncomputable section` to be left open (whether or not it is named).
-/
register_option linter.missingEnd : Bool := {
  defValue := true
  descr := "enable the missing end linter"
}

namespace MissingEnd

/-- Gets the value of the `linter.missingEnd` option. -/
def getLinterHash (o : Options) : Bool := Linter.getLinterValue linter.missingEnd o

@[inherit_doc Mathlib.Linter.linter.missingEnd]
def missingEndLinter : Linter where run := withSetOptionIn fun stx ↦ do
    -- Only run this linter at the end of a module.
    unless stx.isOfKind ``Lean.Parser.Command.eoi do return
    -- TODO: once mathlib's Lean version includes leanprover/lean4#4741, make this configurable
    unless #[`Mathlib, `test, `Archive, `Counterexamples].contains (← getMainModule).getRoot do
      return
    if getLinterHash (← getOptions) && !(← MonadState.get).messages.hasErrors then
      let sc ← getScopes
      -- The last scope is always the "base scope", corresponding to no active `section`s or
      -- `namespace`s. We are interested in any *other* unclosed scopes.
      if sc.length == 1 then return
      let ends := sc.dropLast.map fun s ↦ (s.header, s.isNoncomputable)
      -- If the outermost scope corresponds to a `noncomputable section`, we ignore it.
      let ends := if ends.getLast!.2 then ends.dropLast else ends
      -- If there are any further un-closed scopes, we emit a warning.
      if !ends.isEmpty then
        let ending := (ends.map Prod.fst).foldl (init := "") fun a b ↦
          a ++ s!"\n\nend{if b == "" then "" else " "}{b}"
        Linter.logLint linter.missingEnd stx
         m!"unclosed sections or namespaces; expected: '{ending}'"

initialize addLinter missingEndLinter

end MissingEnd

/-!
# The `cdot` linter

The `cdot` linter is a syntax-linter that flags uses of the "cdot" `·` that are achieved
by typing a character different from `·`.
For instance, a "plain" dot `.` is allowed syntax, but is flagged by the linter.
-/

/--
The `cdot` linter flags uses of the "cdot" `·` that are achieved by typing a character
different from `·`.
For instance, a "plain" dot `.` is allowed syntax, but is flagged by the linter. -/
register_option linter.cdot : Bool := {
  defValue := true
  descr := "enable the `cdot` linter"
}

/-- `isCDot? stx` checks whether `stx` is a `Syntax` node corresponding to a `cdot` typed with
the character `·`. -/
def isCDot? : Syntax → Bool
  | .node _ ``cdotTk #[.node _ `patternIgnore #[.node _ _ #[.atom _ v]]] => v == "·"
  | .node _ ``Lean.Parser.Term.cdot #[.atom _ v] => v == "·"
  | _ => false

/--
`findCDot stx` extracts from `stx` the syntax nodes of `kind` `Lean.Parser.Term.cdot` or `cdotTk`. -/
partial
def findCDot : Syntax → Array Syntax
  | stx@(.node _ kind args) =>
    let dargs := (args.map findCDot).flatten
    match kind with
      | ``Lean.Parser.Term.cdot | ``cdotTk=> dargs.push stx
      | _ =>  dargs
  |_ => #[]

/-- `unwanted_cdot stx` returns an array of syntax atoms within `stx`
corresponding to `cdot`s that are not written with the character `·`.
This is precisely what the `cdot` linter flags.
-/
def unwanted_cdot (stx : Syntax) : Array Syntax :=
  (findCDot stx).filter (!isCDot? ·)

namespace CDotLinter

/-- Gets the value of the `linter.generic` option. -/
def getLinterHash (o : Options) : Bool := Linter.getLinterValue linter.cdot o

@[inherit_doc linter.cdot]
def cdotLinter : Linter where run := withSetOptionIn fun stx => do
    unless getLinterHash (← getOptions) do
      return
    if (← MonadState.get).messages.hasErrors then
      return
    for s in unwanted_cdot stx do
      Linter.logLint linter.cdot s m!"Please, use '·' (typed as `\\·`) instead of '{s}' as 'cdot'."

initialize addLinter cdotLinter

end CDotLinter

/-! # The "longLine linter" -/

/-- The "longLine" linter emits a warning on lines longer than 100 characters.
We allow lines containing URLs to be longer, though. -/
register_option linter.longLine : Bool := {
  defValue := true
  descr := "enable the longLine linter"
}

namespace LongLine

/-- Gets the value of the `linter.longLine` option. -/
def getLinterHash (o : Options) : Bool := Linter.getLinterValue linter.longLine o

@[inherit_doc Mathlib.Linter.linter.longLine]
def longLineLinter : Linter where run := withSetOptionIn fun stx ↦ do
    unless getLinterHash (← getOptions) do
      return
    if (← MonadState.get).messages.hasErrors then
      return
    -- TODO: once mathlib's Lean version includes leanprover/lean4#4741, make this configurable
    unless #[`Mathlib, `test, `Archive, `Counterexamples].contains (← getMainModule).getRoot do
      return
    -- The linter ignores the `#guard_msgs` command, in particular its doc-string.
    -- The linter still lints the message guarded by `#guard_msgs`.
    if stx.isOfKind ``Lean.guardMsgsCmd then
      return
    -- if the linter reached the end of the file, then we scan the `import` syntax instead
    let stx := ← do
      if stx.isOfKind ``Lean.Parser.Command.eoi then
        let fname ← getFileName
        if !(← System.FilePath.pathExists fname) then return default
        let contents ← IO.FS.readFile fname
        -- `impMods` is the syntax for the modules imported in the current file
        let (impMods, _) ← Parser.parseHeader (Parser.mkInputContext contents fname)
        return impMods
      else return stx
    let sstr := stx.getSubstring?
    let fm ← getFileMap
    let longLines := ((sstr.getD default).splitOn "\n").filter fun line =>
      (100 < (fm.toPosition line.stopPos).column)
    for line in longLines do
      if !(line.containsSubstr "http") then
        Linter.logLint linter.longLine (.ofRange ⟨line.startPos, line.stopPos⟩)
          m!"This line exceeds the 100 character limit, please shorten it!"

initialize addLinter longLineLinter

end LongLine

end Mathlib.Linter
