/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Jeremy Avigad
-/
import Mathlib.Topology.Defs.Basic
import Mathlib.Order.Filter.Ultrafilter
import Mathlib.Data.Set.Lattice

/-!
# Definitions about filters in topological spaces

In this file we define filters in topological spaces,
as well as other definitions that rely on `Filter`s.

## Main Definitions

### Neighborhoods filter

* `nhds x`: the filter of neighborhoods of a point in a topological space,
  denoted by `𝓝 x` in the `Topology` scope.
  A set is called a neighborhood of `x`, if it includes an open set around `x`.

* `nhdsWithin x s`: the filter of neighborhoods of a point within a set,
  defined as `𝓝 x ⊓ 𝓟 s` and denoted by `𝓝[s] x`.
  We also introduce notation for some special sets `s`, see below.

* `nhdsSet s`: the filter of neighborhoods of a set in a topological space,
  denoted by `𝓝ˢ s` in the `Topology` scope.
  A set `t` is called a neighborhood of `s`, if it includes an open set that includes `s`.

* `exterior s`: The *exterior* of a set is the intersection of all its neighborhoods.
  In an Alexandrov-discrete space, this is the smallest neighborhood of the set.

  Note that this construction is unnamed in the literature.
  We choose the name in analogy to `interior`.

### Continuity at a point

* `ContinuousAt f x`: a function `f` is continuous at a point `x`,
  if it tends to `𝓝 (f x)` along `𝓝 x`.

* `ContinuousWithinAt f s x`: a function `f` is continuous within a set `s` at a point `x`,
  if it tends to `𝓝 (f x)` along `𝓝[s] x`.

* `ContinuousOn f s`: a function `f : X → Y` is continuous on a set `s`,
  if it is continuous within `s` at every point of `s`.

### Limits

* `lim f`: a limit of a filter `f` in a nonempty topological space.
  If there exists `x` such that `f ≤ 𝓝 x`, then `lim f` is one of such points,
  otherwise it is `Classical.choice _`.

  In a Hausdorff topological space, the limit is unique if it exists.

* `Ultrafilter.lim f`: a limit of an ultrafilter `f`,
  defined as the limit of `(f : Filter X)`
  with a proof of `Nonempty X` deduced from existence of an ultrafilter on `X`.

* `limUnder f g`: a limit of a filter `f` along a function `g`, defined as `lim (Filter.map g f)`.

### Cluster points and accumulation points

* `ClusterPt x F`: a point `x` is a *cluster point* of a filter `F`,
  if `𝓝 x` is not disjoint with `F`.

* `MapClusterPt x F u`: a point `x` is a *cluster point* of a function `u` along a filter `F`,
  if it is a cluster point of the filter `Filter.map u F`.

* `AccPt x F`: a point `x` is an *accumulation point* of a filter `F`,
  if `𝓝[≠] x` is not disjoint with `F`.
  Every accumulation point of a filter is its cluster point, but not vice versa.

* `IsCompact s`: a set `s` is compact if for every nontrivial filter `f` that contains `s`,
  there exists `a ∈ s` such that every set of `f` meets every neighborhood of `a`.
  Equivalently, a set `s` is compact if for any cover of `s` by open sets,
  there exists a finite subcover.

* `CompactSpace`, `NoncompactSpace`: typeclasses saying that the whole space
  is a compact set / is not a compact set, respectively.

* `WeaklyLocallyCompactSpace X`: typeclass saying that every point of `X`
  has a compact neighborhood.

* `LocallyCompactSpace X`: typeclass saying that every point of `X`
  has a basis of compact neighborhoods.
  Every locally compact space is a weakly locally compact space.
  The reverse implication is true for R₁ (preregular) spaces.

* `LocallyCompactPair X Y`: an auxiliary typeclass saying that
  for any continuous function `f : X → Y`, a point `x`, and a neighborhood `s` of `f x`,
  there exists a compact neighborhood `K` of `x` such that `f` maps `K` to `s`.

* `Filter.cocompact`, `Filter.coclosedCompact`:
  filters generated by complements to compact and closed compact sets, respectively.

## Notations

* `𝓝 x`: the filter `nhds x` of neighborhoods of a point `x`;
* `𝓟 s`: the principal filter of a set `s`, defined elsewhere;
* `𝓝[s] x`: the filter `nhdsWithin x s` of neighborhoods of a point `x` within a set `s`;
* `𝓝[≤] x`: the filter `nhdsWithin x (Set.Iic x)` of left-neighborhoods of `x`;
* `𝓝[≥] x`: the filter `nhdsWithin x (Set.Ici x)` of right-neighborhoods of `x`;
* `𝓝[<] x`: the filter `nhdsWithin x (Set.Iio x)` of punctured left-neighborhoods of `x`;
* `𝓝[>] x`: the filter `nhdsWithin x (Set.Ioi x)` of punctured right-neighborhoods of `x`;
* `𝓝[≠] x`: the filter `nhdsWithin x {x}ᶜ` of punctured neighborhoods of `x`;
* `𝓝ˢ s`: the filter `nhdsSet s` of neighborhoods of a set.
-/

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

open Filter
open scoped Topology

/-- A set is called a neighborhood of `x` if it contains an open set around `x`. The set of all
neighborhoods of `x` forms a filter, the neighborhood filter at `x`, is here defined as the
infimum over the principal filters of all open sets containing `x`. -/
irreducible_def nhds (x : X) : Filter X :=
  ⨅ s ∈ { s : Set X | x ∈ s ∧ IsOpen s }, 𝓟 s

@[inherit_doc]
scoped[Topology] notation "𝓝" => nhds

/-- The "neighborhood within" filter. Elements of `𝓝[s] x` are sets containing the
intersection of `s` and a neighborhood of `x`. -/
def nhdsWithin (x : X) (s : Set X) : Filter X :=
  𝓝 x ⊓ 𝓟 s

@[inherit_doc]
scoped[Topology] notation "𝓝[" s "] " x:100 => nhdsWithin x s

/-- Notation for the filter of punctured neighborhoods of a point. -/
scoped[Topology] notation3 "𝓝[≠] " x:100 =>
  nhdsWithin x (@singleton _ (Set _) Set.instSingletonSet x)ᶜ

/-- Notation for the filter of right neighborhoods of a point. -/
scoped[Topology] notation3 "𝓝[≥] " x:100 => nhdsWithin x (Set.Ici x)

/-- Notation for the filter of left neighborhoods of a point. -/
scoped[Topology] notation3 "𝓝[≤] " x:100 => nhdsWithin x (Set.Iic x)

/-- Notation for the filter of punctured right neighborhoods of a point. -/
scoped[Topology] notation3 "𝓝[>] " x:100 => nhdsWithin x (Set.Ioi x)

/-- Notation for the filter of punctured left neighborhoods of a point. -/
scoped[Topology] notation3 "𝓝[<] " x:100 => nhdsWithin x (Set.Iio x)

/-- The filter of neighborhoods of a set in a topological space. -/
def nhdsSet (s : Set X) : Filter X :=
  sSup (nhds '' s)

@[inherit_doc] scoped[Topology] notation "𝓝ˢ" => nhdsSet

/-- The *exterior* of a set is the intersection of all its neighborhoods. In an Alexandrov-discrete
space, this is the smallest neighborhood of the set.

Note that this construction is unnamed in the literature. We choose the name in analogy to
`interior`. -/
def exterior (s : Set X) : Set X := (𝓝ˢ s).ker

/-- A function between topological spaces is continuous at a point `x₀`
if `f x` tends to `f x₀` when `x` tends to `x₀`. -/
@[fun_prop]
def ContinuousAt (f : X → Y) (x : X) :=
  Tendsto f (𝓝 x) (𝓝 (f x))

/-- A function between topological spaces is continuous at a point `x₀` within a subset `s`
if `f x` tends to `f x₀` when `x` tends to `x₀` while staying within `s`. -/
@[fun_prop]
def ContinuousWithinAt (f : X → Y) (s : Set X) (x : X) : Prop :=
  Tendsto f (𝓝[s] x) (𝓝 (f x))

/-- A function between topological spaces is continuous on a subset `s`
when it's continuous at every point of `s` within `s`. -/
@[fun_prop]
def ContinuousOn (f : X → Y) (s : Set X) : Prop :=
  ∀ x ∈ s, ContinuousWithinAt f s x

/-- `x` specializes to `y` (notation: `x ⤳ y`) if either of the following equivalent properties
hold:

* `𝓝 x ≤ 𝓝 y`; this property is used as the definition;
* `pure x ≤ 𝓝 y`; in other words, any neighbourhood of `y` contains `x`;
* `y ∈ closure {x}`;
* `closure {y} ⊆ closure {x}`;
* for any closed set `s` we have `x ∈ s → y ∈ s`;
* for any open set `s` we have `y ∈ s → x ∈ s`;
* `y` is a cluster point of the filter `pure x = 𝓟 {x}`.

This relation defines a `Preorder` on `X`. If `X` is a T₀ space, then this preorder is a partial
order. If `X` is a T₁ space, then this partial order is trivial : `x ⤳ y ↔ x = y`. -/
def Specializes (x y : X) : Prop := 𝓝 x ≤ 𝓝 y

@[inherit_doc]
infixl:300 " ⤳ " => Specializes

/-- Two points `x` and `y` in a topological space are `Inseparable` if any of the following
equivalent properties hold:

- `𝓝 x = 𝓝 y`; we use this property as the definition;
- for any open set `s`, `x ∈ s ↔ y ∈ s`, see `inseparable_iff_open`;
- for any closed set `s`, `x ∈ s ↔ y ∈ s`, see `inseparable_iff_closed`;
- `x ∈ closure {y}` and `y ∈ closure {x}`, see `inseparable_iff_mem_closure`;
- `closure {x} = closure {y}`, see `inseparable_iff_closure_eq`.
-/
def Inseparable (x y : X) : Prop :=
  𝓝 x = 𝓝 y

variable (X)

/-- Specialization forms a preorder on the topological space. -/
def specializationPreorder : Preorder X :=
  { Preorder.lift (OrderDual.toDual ∘ 𝓝) with
    le := fun x y => y ⤳ x
    lt := fun x y => y ⤳ x ∧ ¬x ⤳ y }

/-- A `setoid` version of `Inseparable`, used to define the `SeparationQuotient`. -/
def inseparableSetoid : Setoid X := { Setoid.comap 𝓝 ⊥ with r := Inseparable }

/-- The quotient of a topological space by its `inseparableSetoid`.
This quotient is guaranteed to be a T₀ space. -/
def SeparationQuotient := Quotient (inseparableSetoid X)

variable {X}

section Lim


/-- If `f` is a filter, then `Filter.lim f` is a limit of the filter, if it exists. -/
noncomputable def lim [Nonempty X] (f : Filter X) : X :=
  Classical.epsilon fun x => f ≤ 𝓝 x

/--
If `F` is an ultrafilter, then `Filter.Ultrafilter.lim F` is a limit of the filter, if it exists.
Note that dot notation `F.lim` can be used for `F : Filter.Ultrafilter X`.
-/
noncomputable nonrec def Ultrafilter.lim (F : Ultrafilter X) : X :=
  @lim X _ (nonempty_of_neBot F) F

/-- If `f` is a filter in `α` and `g : α → X` is a function, then `limUnder f g` is a limit of `g`
at `f`, if it exists. -/
noncomputable def limUnder {α : Type*} [Nonempty X] (f : Filter α) (g : α → X) : X :=
  lim (f.map g)

end Lim

/-- A point `x` is a cluster point of a filter `F` if `𝓝 x ⊓ F ≠ ⊥`.
Also known as an accumulation point or a limit point, but beware that terminology varies.
This is *not* the same as asking `𝓝[≠] x ⊓ F ≠ ⊥`, which is called `AccPt` in Mathlib.
See `mem_closure_iff_clusterPt` in particular. -/
def ClusterPt (x : X) (F : Filter X) : Prop :=
  NeBot (𝓝 x ⊓ F)

/-- A point `x` is a cluster point of a sequence `u` along a filter `F` if it is a cluster point
of `map u F`. -/
def MapClusterPt {ι : Type*} (x : X) (F : Filter ι) (u : ι → X) : Prop :=
  ClusterPt x (map u F)

/-- A point `x` is an accumulation point of a filter `F` if `𝓝[≠] x ⊓ F ≠ ⊥`.
See also `ClusterPt`. -/
def AccPt (x : X) (F : Filter X) : Prop :=
  NeBot (𝓝[≠] x ⊓ F)

/-- A set `s` is compact if for every nontrivial filter `f` that contains `s`,
    there exists `a ∈ s` such that every set of `f` meets every neighborhood of `a`. -/
def IsCompact (s : Set X) :=
  ∀ ⦃f⦄ [NeBot f], f ≤ 𝓟 s → ∃ x ∈ s, ClusterPt x f

variable (X) in
/-- Type class for compact spaces. Separation is sometimes included in the definition, especially
in the French literature, but we do not include it here. -/
class CompactSpace : Prop where
  /-- In a compact space, `Set.univ` is a compact set. -/
  isCompact_univ : IsCompact (Set.univ : Set X)

variable (X) in
/-- `X` is a noncompact topological space if it is not a compact space. -/
class NoncompactSpace : Prop where
  /-- In a noncompact space, `Set.univ` is not a compact set. -/
  noncompact_univ : ¬IsCompact (Set.univ : Set X)

/-- We say that a topological space is a *weakly locally compact space*,
if each point of this space admits a compact neighborhood. -/
class WeaklyLocallyCompactSpace (X : Type*) [TopologicalSpace X] : Prop where
  /-- Every point of a weakly locally compact space admits a compact neighborhood. -/
  exists_compact_mem_nhds (x : X) : ∃ s, IsCompact s ∧ s ∈ 𝓝 x

export WeaklyLocallyCompactSpace (exists_compact_mem_nhds)

/-- There are various definitions of "locally compact space" in the literature,
which agree for Hausdorff spaces but not in general.
This one is the precise condition on X needed
for the evaluation map `C(X, Y) × X → Y` to be continuous for all `Y`
when `C(X, Y)` is given the compact-open topology.

See also `WeaklyLocallyCompactSpace`, a typeclass that only assumes
that each point has a compact neighborhood. -/
class LocallyCompactSpace (X : Type*) [TopologicalSpace X] : Prop where
  /-- In a locally compact space,
    every neighbourhood of every point contains a compact neighbourhood of that same point. -/
  local_compact_nhds : ∀ (x : X), ∀ n ∈ 𝓝 x, ∃ s ∈ 𝓝 x, s ⊆ n ∧ IsCompact s

/-- We say that `X` and `Y` are a locally compact pair of topological spaces,
if for any continuous map `f : X → Y`, a point `x : X`, and a neighbourhood `s ∈ 𝓝 (f x)`,
there exists a compact neighbourhood `K ∈ 𝓝 x` such that `f` maps `K` to `s`.

This is a technical assumption that appears in several theorems,
most notably in `ContinuousMap.continuous_comp'` and `ContinuousMap.continuous_eval`.
It is satisfied in two cases:

- if `X` is a locally compact topological space, for obvious reasons;
- if `X` is a weakly locally compact topological space and `Y` is an R₁ space;
  this fact is a simple generalization of the theorem
  saying that a weakly locally compact R₁ topological space is locally compact.
-/
class LocallyCompactPair (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y] : Prop where
  /-- If `f : X → Y` is a continuous map in a locally compact pair of topological spaces
  and `s : Set Y` is a neighbourhood of `f x`, `x : X`,
  then there exists a compact neighbourhood `K` of `x` such that `f` maps `K` to `s`. -/
  exists_mem_nhds_isCompact_mapsTo : ∀ {f : X → Y} {x : X} {s : Set Y},
    Continuous f → s ∈ 𝓝 (f x) → ∃ K ∈ 𝓝 x, IsCompact K ∧ Set.MapsTo f K s

export LocallyCompactPair (exists_mem_nhds_isCompact_mapsTo)

variable (X) in
/-- `Filter.cocompact` is the filter generated by complements to compact sets. -/
def Filter.cocompact : Filter X :=
  ⨅ (s : Set X) (_ : IsCompact s), 𝓟 sᶜ

variable (X) in
/-- `Filter.coclosedCompact` is the filter generated by complements to closed compact sets.
In a Hausdorff space, this is the same as `Filter.cocompact`. -/
def Filter.coclosedCompact : Filter X :=
  ⨅ (s : Set X) (_ : IsClosed s) (_ : IsCompact s), 𝓟 sᶜ
