/-
Copyright (c) 2023 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Batteries.Data.MLList.Basic
import Mathlib.Control.Combinators
import Std.Data.HashSet.Basic

/-!
# Depth first search

We perform depth first search of a tree or graph,
where the neighbours of a vertex are provided either by list `α → List α`
or a lazy list `α → MLList MetaM α`.

This is useful in meta code for searching for solutions in the presence of alternatives.
It can be nice to represent the choices via a lazy list,
so the later choices don't need to be evaluated while we do depth first search on earlier choices.

## Deprecation

This material has been moved out of Mathlib to https://github.com/semorrison/lean-monadic-list.
-/

set_option linter.deprecated false

universe u
variable {α : Type u} {m : Type u → Type u}

section

variable [Monad m] [Alternative m]

/-- A generalisation of `depthFirst`, which allows the generation function to know the current
depth, and to count the depth starting from a specified value. -/
@[deprecated "See deprecation note in module documentation." (since := "2024-08-22")]
partial def depthFirst' (f : Nat → α → m α) (n : Nat) (a : α) : m α :=
pure a <|> joinM ((f n a) <&> (depthFirst' f (n+1)))

/--
Depth first search of a graph generated by a function
`f : α → m α`.

Here `m` must be an `Alternative` `Monad`,
and perhaps the only sensible values are `List` and `MLList MetaM`.

The option `maxDepth` limits the search depth.

Note that if the graph is not a tree then elements will be visited multiple times.
(See `depthFirstRemovingDuplicates`)
-/
@[deprecated "See deprecation note in module documentation." (since := "2024-08-22")]
def depthFirst (f : α → m α) (a : α) (maxDepth : Option Nat := none) : m α :=
  match maxDepth with
  | some d => depthFirst' (fun n a => if n ≤ d then f a else failure) 0 a
  | none => depthFirst' (fun _ a => f a) 0 a

end

variable [Monad m]

open Lean in
/--
Variant of `depthFirst`,
using an internal `HashSet` to record and avoid already visited nodes.

This version describes the graph using `α → MLList m α`,
and returns the monadic lazy list of nodes visited in order.

This is potentially very expensive.
If you want to do efficient enumerations from a generation function,
avoiding duplication up to equality or isomorphism,
use Brendan McKay's method of "generation by canonical construction path".
-/
-- TODO can you make this work in `List` and `MLList m` simultaneously, by being tricky with monads?
@[deprecated "See deprecation note in module documentation." (since := "2024-08-22")]
def depthFirstRemovingDuplicates {α : Type u} [BEq α] [Hashable α]
    (f : α → MLList m α) (a : α) (maxDepth : Option Nat := none) : MLList m α :=
let_fun f' : α → MLList (StateT.{u} (Std.HashSet α) m) α := fun a =>
  (f a).liftM >>= fun b => do
    let s ← get
    if s.contains b then failure
    set <| s.insert b
    pure b
(depthFirst f' a maxDepth).runState' (Std.HashSet.empty.insert a)

/--
Variant of `depthFirst`,
using an internal `HashSet` to record and avoid already visited nodes.

This version describes the graph using `α → List α`, and returns the list of nodes visited in order.
-/
@[deprecated "See deprecation note in module documentation." (since := "2024-08-22")]
def depthFirstRemovingDuplicates' [BEq α] [Hashable α]
    (f : α → List α) (a : α) (maxDepth : Option Nat := none) : List α :=
depthFirstRemovingDuplicates
  (fun a => (.ofList (f a) : MLList Option α)) a maxDepth |>.force |>.get!
