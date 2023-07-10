/-
Copyright (c) 2023 Thomas Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Murrills
-/
import Lean
import Std

/-!
# Fail if no progress

This implements the `fail_if_no_progress` tactic, which fails if no actual progress is made by the
following tactic sequence.

"Actual progress" means that either the number of goals has changed, that the
number or presence of expressions in the context has changed, or that the type of some expression
in the context or the type of the goal is no longer definitionally equal to what it used to be at
reducible transparency.

This means that, for example, `1 - 1` changing to `0` does not count as actual progress, since
```lean
example : (1 - 1 = 0) := by with_reducible rfl
```

This tactic is useful in situations where we want to stop iterating some tactics if they're not
having any  effect, e.g. `repeat (fail_if_no_progress simp <;> ring_nf)`.





```
structure SubConfig (defaults : SharedProcessConfig) where
  subSubProcessConfig : Option (SubSubProcessConfig defaults) := some {}
```
-/
-/

namespace Mathlib.Tactic

open Lean Meta Elab Tactic Parser.Tactic

/-- Specifies which type of equality check to use. Either `.beq` or `.defEq`. -/
inductive EqKind where | beq | defEq

/-- Returns `true` if its argument is `.beq` and `false` if `.defEq`. -/
def EqKind.isBEq : EqKind → Bool
  | .beq   => true
  | .defEq => false

/-- Config data for comparing expressions. -/
structure ExprComparisonConfig where
  /-- Which kind of equality check to use. -/
  eqKind       : EqKind := .defEq
  /-- What transparency to use for equality checks. -/
  transparency : TransparencyMode := .reducible

/-- Config data for comparing expressions, where the default field values are drawn from
`defaults`. -/
structure ExprComparisonConfigWithDefaults (defaults : ExprComparisonConfig)
  extends ExprComparisonConfig
where
  -- Inherit defaults
  eqKind       := defaults.eqKind
  transparency := defaults.transparency

/-- Config data for comparing local contexts. -/
structure LocalDeclComparisonConfig where
  /-- Whether to compare the indices of two `LocalDecl`s. -/
  checkIndex         : Bool := true
  /-- Whether to compare the `FVarIds` of two `LocalDecl`s. -/
  checkFVarId        : Bool := true
  /-- Whether to compare the userNames of two `LocalDecl`s. -/
  checkUserName      : Bool := true
  /-- Whether to compare the types of two `LocalDecl`s. -/
  checkType          : Bool := true
  /-- Whether to compare the letValues of two `ldecl`s. -/
  checkLetValue      : Bool := true
  /-- Whether to compare the binderInfos of two `cdecl`s. -/
  checkBinderInfo    : Bool := true
  /-- Whether to compare the declKinds of a `LocalDecl`. -/
  checkLocalDeclKind : Bool := true

-- Merge?
/-- Config data for comparing local contexts. -/
structure LocalContextComparisonConfig extends LocalDeclComparisonConfig where
  -- Filtering options
  /-- Whether to include implementation detail decls. -/
  includeImplDetails  : Bool := true
  /-- Whether to include auxiliary decls. -/
  includeAuxDecls     : Bool := true
  /-- Whether to include default decls. -/
  includeDefaultDecls : Bool := true
  /-- Whether to include `ldecls`. -/
  includeLDecls       : Bool := true
  /-- Whether to include `cdecls`. -/
  includeCDecls       : Bool := true
/-- Config data for comparing local instances. Since the `Expr` in the `LocalInstance` is meant to
be an `.fvar`, we always use `BEq`. -/ --!! True?
structure LocalInstanceComparisonConfig where
  checkName : Bool := true
  checkFVar : Bool := true

--!! docs
structure MetavarDeclComparisonConfig (defaults : ExprComparisonConfig)
  extends ExprComparisonConfig
where
  eqKind := defaults.eqKind
  transparency := defaults.transparency
  checkUserName : Bool := true
  compareLocalContexts? : Option (LocalContextComparisonConfig { eqKind, transparency }) := some {}
  compareTarget? : Option (ExprComparisonConfigWithDefaults { eqKind, transparency }) := some {}
  checkLocalInstance? : Option LocalInstanceComparisonConfig := some {}
  checkMetavarKind : Bool := true
  checkIndex : Bool := true -- !! need? shouldn't this persist?

-- !! Generalize with filtering and mustNotLose,mustNotGain list/array config stuff? Generalize into a goal list config?
inductive FailIfNoProgress.Mode where
/-- Compares the goal lists before and after the tactic. -/
| normal
/-- Only checks if the initial metavariables have been assigned or not. -/
| quick




-- allow custom functions for comparing `Expr`s etc.? It'd be cool if every comparison function could be overridden, and really was stored in a structure. It'd be neat to do the custom elaborator thing.
/--
--!! Needs updating

Config data for `failIfNoProgress`, `fail_if_no_progress`, and `runAndFailIfNoProgress`.

This determines which aspects of the goals are checked for "progress" and the nature of the
equality checks made.

* `eqKind : EqKind := .defEq` – either `.beq` or `.defEq`; `.beq` uses the instance of `BEq Expr` to
  compare expressions, and `.defEq` uses `isDefEq`
* `transparency : TransparencyMode := .reducible` – the `TransparencyMode` to compare expressions
at.
* `checkTarget : Bool := true` – compare the targets of goals when comparing goals.
* `onLocalInstances : Option LocalInstanceComparisonConfig` – The configuration for comparing local
instances of goals. If `none`, local instances are not compared.
  * `eqKind : EqKind := eqKind`
  * `transparency : TransparencyMode := transparency`
* `onCtx : Option CtxComparisonConfig` – The configuration for comparing local contexts. By default,
  this inherits the given values of `eqKind` and `transparency`, and only checks indices and
  FVarIds if `eqKind := .beq`. If `none`, local contexts are not compared.
  * `eqKind : EqKind := eqKind`
  * `transparency : TransparencyMode := transparency`
  * `checkIndex : Bool := eqKind.isBEq` – checks if the indices (positions) of fvars have changed;
    amounts to checking if some fvars have been made unavialable
  * `checkFVarIds : Bool := eqKind.isBEq` – compares `FVarId`s directly
  * `checkUserNames : Bool := true` – compares the names of fvars in the local context
  * `checkLetValue  : Bool := true` – compares the values of `ldecls`
-/
structure FailIfNoProgress.Config extends ExprComparisonConfig, MetavarDeclComparisonConfig where
  mode : FailIfNoProgress.Mode := .normal

--!! Does transparency affect BEq or is it only a DefEq thing? I think the latter, but want to be
-- sure.
/-- Compares two expressions according to the given `ComparisonConfig`. -/
  
/-- Compares two lists monadically. -/
def compareListM [Monad m] (l₁ l₂ : List α) (c : α → α → m Bool) : m Bool := do
  let some lZip := zip? l₁ l₂ | return false
  for (a₁, a₂) in lZip do
    unless (← c a₁ a₂) do
      return false
  return true

/-- Compare two `LocalDecl`s according to `config`. -/
def compareLocalDecl (l₁ l₂ : LocalDecl) : (config : DeclComparisonConfig) → MetaM Bool
| { toExprComparisonConfig, checkIndex, checkFVarIds, checkUserNames, checkLetValue } =>
  let b := l₁.kind == l₂.kind
    && (! checkIndex     || l₁.index == l₂.index)
    && (! checkFVarIds   || l₁.fvarId == l₂.fvarId)
    && (! checkUserNames || l₁.userName == l₂.userName)
  andM' b
  (match l₁.isLet && checkLetValue with
    | true => andM
      (compareExpr l₁.value l₂.value toExprComparisonConfig)
      (compareExpr l₁.type l₂.type toExprComparisonConfig)
    | false => compareExpr l₁.type l₂.type toExprComparisonConfig
  )

/-- Compare two `LocalContext`s according to the specifications in `config`. -/
def compareLCtx (lctx₁ lctx₂ : LocalContext) (config : CtxComparisonConfig := {}) : MetaM Bool :=
  let l₁ := lctx₁.decls.toList.reduceOption
  let l₂ := lctx₂.decls.toList.reduceOption
  compareListM l₁ l₂ (compareLocalDecl (config := config.toDeclComparisonConfig))

/-- Compare local instances. -/
def compareLocalInstances (lis₁ lis₂ : LocalInstances)
    (config : LocalInstanceComparisonConfig := {}) : MetaM Bool :=
  compareListM lis₁.toList lis₂.toList (compareExpr ·.fvar ·.fvar config.toExprComparisonConfig)

/-- Compare two `MVarId`s by comparing their types and their local contexts, according to
`config`. -/
def compareGoal (goal₁ goal₂ : MVarId) (config : FailIfNoProgress.Config := {}) : MetaM Bool := do
  let decl₁ ← goal₁.getDecl; let decl₂ ← goal₂.getDecl
  andM
    (impM' config.checkTarget
      (compareExpr decl₁.type decl₂.type config.toExprComparisonConfig))
    <| andM
      (do
        let some cfg := config.onLocalInstances | return true
        compareLocalInstances decl₁.localInstances decl₂.localInstances cfg)
      (do
        let some cfg := config.onCtx | return true
        compareLCtx decl₁.lctx decl₂.lctx cfg)

/-- Compare a list of goals to another list of goals. Return false if the number of goals differs,
and otherwise compare the goals pairwise in order according to `config`. -/
def compareGoals (goals₁ goals₂ : List MVarId) (config : FailIfNoProgress.Config := {}) :
    MetaM Bool :=
  compareListM goals₁ goals₂ (compareGoal (config := config))

/-- Run `tacs : TacticM Unit` on `goal`, and fail if no progress is made. -/
def runAndFailIfNoProgress (goal : MVarId) (tacs : TacticM Unit)
    (config : FailIfNoProgress.Config := {}) : TacticM (List MVarId) := do
  let l ← run goal tacs
  try
    let [newGoal] := l | failure
    guard <|← compareGoal goal newGoal config
  catch _ =>
    return l
  throwError "no progress made on goal:\n{goal}"

/-- Run `tacs`, and fail if no progress is made. -/
def failIfNoProgress [ToMessageData α] (tacs : TacticM α) (config : FailIfNoProgress.Config := {}) :
    TacticM α := do
  let goals₁ ← getGoals
  let result ← tacs
  let goals₂ ← getGoals
  unless (← compareGoals goals₁ goals₂ config) do
    return result
  let goalString := if goals₁.length = 1 then "goal" else "goals"
  throwError "no progress made on {goalString}"

namespace FailIfNoProgress

/-- `fail_if_no_progress tacs` evaluates `tacs`, and fails if no progress is made on the list of
goals. This compares each of their types and local contexts before and after `tacs` is run.

By default, expressions are compared with `isDefEq` at reducible transparency. Any change in the
order or number of goals counts as progress.

`fail_if_no_progress (config := { ... }) tacs` can be used to specify what kind of comparison to
perform. Transparency can be set via the field `transparency`, and the instance for `BEq Expr` can
be used instead of `isDefEq` by specifying `eqKind := .beq`. `BEq` is weaker than `isDefEq`, and
will therefore cause more minor changes to count as "progress". For more configuration options see
`FailIfNoProgress.Config`.
 -/
syntax (name := failIfNoProgress) "fail_if_no_progress " (config)? tacticSeq : tactic

/-- Elaborates `FailIfNoProgress.Config`. -/
declare_config_elab elabConfig Config

elab_rules : tactic
| `(tactic| fail_if_no_progress $[$cfg:config]? $tacs:tacticSeq) => do
  let cfg ← elabConfig (mkOptionalNode cfg)
  Tactic.failIfNoProgress (evalTactic tacs) cfg
