/-
Copyright (c) 2023 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
import Mathlib.Algebra.Homology.ConcreteCategory
import Mathlib.Algebra.Homology.Opposite
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.RepresentationTheory.Homological.Resolution
import Mathlib.Tactic.CategoryTheory.Slice

/-!
# The group cohomology of a `k`-linear `G`-representation

Let `k` be a commutative ring and `G` a group. This file defines the group cohomology of
`A : Rep k G` to be the cohomology of the complex
$$0 \to \mathrm{Fun}(G^0, A) \to \mathrm{Fun}(G^1, A) \to \mathrm{Fun}(G^2, A) \to \dots$$
with differential $d^n$ sending $f: G^n \to A$ to the function mapping $(g_0, \dots, g_n)$ to
$$\rho(g_0)(f(g_1, \dots, g_n))$$
$$+ \sum_{i = 0}^{n - 1} (-1)^{i + 1}\cdot f(g_0, \dots, g_ig_{i + 1}, \dots, g_n)$$
$$+ (-1)^{n + 1}\cdot f(g_0, \dots, g_{n - 1})$$ (where `ρ` is the representation attached to `A`).

We have a `k`-linear isomorphism $\mathrm{Fun}(G^n, A) \cong \mathrm{Hom}(k[G^{n + 1}], A)$, where
the righthand side is morphisms in `Rep k G`, and the representation on $k[G^{n + 1}]$
is induced by the diagonal action of `G`. If we conjugate the $n$th differential in
$\mathrm{Hom}(P, A)$ by this isomorphism, where `P` is the standard resolution of `k` as a trivial
`k`-linear `G`-representation, then the resulting map agrees with the differential $d^n$ defined
above, a fact we prove.

This gives us for free a proof that our $d^n$ squares to zero. It also gives us an isomorphism
$\mathrm{H}^n(G, A) \cong \mathrm{Ext}^n(k, A),$ where $\mathrm{Ext}$ is taken in the category
`Rep k G`.

To talk about cohomology in low degree, please see the file
`Mathlib.RepresentationTheory.GroupCohomology.LowDegree`, which gives simpler expressions for
`H⁰`, `H¹`, `H²` than the definition `groupCohomology` in this file.

## Main definitions

* `groupCohomology.linearYonedaObjResolution A`: a complex whose objects are the representation
morphisms $\mathrm{Hom}(k[G^{n + 1}], A)$ and whose cohomology is the group cohomology
$\mathrm{H}^n(G, A)$.
* `groupCohomology.inhomogeneousCochains A`: a complex whose objects are
$\mathrm{Fun}(G^n, A)$ and whose cohomology is the group cohomology $\mathrm{H}^n(G, A).$
* `groupCohomology.inhomogeneousCochainsIso A`: an isomorphism between the above two complexes.
* `groupCohomology A n`: this is $\mathrm{H}^n(G, A),$ defined as the $n$th cohomology of the
second complex, `inhomogeneousCochains A`.
* `groupCohomologyIsoExt A n`: an isomorphism $\mathrm{H}^n(G, A) \cong \mathrm{Ext}^n(k, A)$
(where $\mathrm{Ext}$ is taken in the category `Rep k G`) induced by `inhomogeneousCochainsIso A`.

## Implementation notes

Group cohomology is typically stated for `G`-modules, or equivalently modules over the group ring
`ℤ[G].` However, `ℤ` can be generalized to any commutative ring `k`, which is what we use.
Moreover, we express `k[G]`-module structures on a module `k`-module `A` using the `Rep`
definition. We avoid using instances `Module (MonoidAlgebra k G) A` so that we do not run into
possible scalar action diamonds.

## TODO

* API for cohomology in low degree: $\mathrm{H}^0, \mathrm{H}^1$ and $\mathrm{H}^2.$ For example,
the inflation-restriction exact sequence.
* The long exact sequence in cohomology attached to a short exact sequence of representations.
* Upgrading `groupCohomologyIsoExt` to an isomorphism of derived functors.
* Profinite cohomology.

Longer term:
* The Hochschild-Serre spectral sequence (this is perhaps a good toy example for the theory of
spectral sequences in general).
-/


noncomputable section

universe u

variable {k G : Type u} [CommRing k]

open CategoryTheory Limits
namespace ModuleCat

variable {R : Type u} [Ring R] {M : Type*} [AddCommGroup M] [Module R M] (S : Submodule R M)

instance : Mono (ModuleCat.asHom S.subtype) :=
  (ModuleCat.mono_iff_injective _).2 fun _ _ h => Subtype.ext_iff.2 h

instance : Epi (ModuleCat.asHom S.mkQ) :=
  (ModuleCat.epi_iff_surjective _).2 S.mkQ_surjective

end ModuleCat
open Rep

namespace inhomogeneousCochains

/-- The differential in the complex of inhomogeneous cochains used to
calculate group cohomology. -/
@[simps]
def d [Monoid G] (A : Rep k G) (n : ℕ) : ((Fin n → G) → A) →ₗ[k] (Fin (n + 1) → G) → A where
  toFun f g :=
    A.ρ (g 0) (f fun i => g i.succ) +
      Finset.univ.sum fun j : Fin (n + 1) =>
        (-1 : k) ^ ((j : ℕ) + 1) • f (Fin.contractNth j (· * ·) g)
  map_add' f g := by
    ext x
    simp [Finset.sum_add_distrib, add_add_add_comm]
  map_smul' r f := by
    ext x
    simp [Finset.smul_sum, ← smul_assoc, mul_comm r]

variable [Group G] (A : Rep k G) (n : ℕ)

@[nolint checkType] theorem d_eq :
    d A n =
      (freeLiftEquiv (Fin n → G) A).toModuleIso.inv ≫
        ((barResolution k G).linearYonedaObj k A).d n (n + 1) ≫
          (freeLiftEquiv (Fin (n + 1) → G) A).toModuleIso.hom := by
  ext f g
  show _ = Finsupp.linearCombination _ _ _
  have h := barResolution.d_single (k := k) _ g
  simp_all [coe_V]

end inhomogeneousCochains

namespace groupCohomology

variable [Group G] (A : Rep k G) (n : ℕ)

open inhomogeneousCochains

/-- Given a `k`-linear `G`-representation `A`, this is the complex of inhomogeneous cochains
$$0 \to \mathrm{Fun}(G^0, A) \to \mathrm{Fun}(G^1, A) \to \mathrm{Fun}(G^2, A) \to \dots$$
which calculates the group cohomology of `A`. -/
noncomputable abbrev inhomogeneousCochains : CochainComplex (ModuleCat k) ℕ :=
  CochainComplex.of (fun n => ModuleCat.of k ((Fin n → G) → A))
    (fun n => inhomogeneousCochains.d A n) fun n => by
    simp only [d_eq]
    slice_lhs 3 4 => { rw [Iso.hom_inv_id] }
    slice_lhs 2 4 => { rw [Category.id_comp, ((barResolution k G).linearYonedaObj k A).d_comp_d] }
    simp

theorem inhomogeneousCochains.d_comp_d :
    d A (n + 1) ∘ₗ d A n = 0 := by
  simpa [CochainComplex.of] using (inhomogeneousCochains A).d_comp_d n (n + 1) (n + 2)

@[simp]
theorem inhomogeneousCochains.d_def :
    (inhomogeneousCochains A).d n (n + 1) = inhomogeneousCochains.d A n :=
  CochainComplex.of_d _ _ _ _

/-- Given a `k`-linear `G`-representation `A`, the complex of inhomogeneous cochains is isomorphic
to `Hom(P, A)`, where `P` is the bar resolution of `k` as a trivial `G`-representation. -/
def inhomogeneousCochainsIso :
    inhomogeneousCochains A ≅ (barResolution k G).linearYonedaObj k A := by
  refine HomologicalComplex.Hom.isoOfComponents
    (fun i => (Rep.freeLiftEquiv (Fin i → G) A).toModuleIso.symm) ?_
  rintro i j (h : i + 1 = j)
  subst h
  simp only [Iso.symm_hom, inhomogeneousCochains.d_def, d_eq, Category.assoc]
  slice_rhs 2 4 => { rw [Iso.hom_inv_id, Category.comp_id] }

/-- The `n`-cocycles `Zⁿ(G, A)` of a `k`-linear `G`-representation `A`, i.e. the kernel of the
`n`th differential in the complex of inhomogeneous cochains. -/
abbrev cocycles (n : ℕ) : ModuleCat k := (inhomogeneousCochains A).cycles n

open HomologicalComplex

/-- `Zⁿ(G, A)` is isomorphic to the kernel of the explicit map
`inhomogeneousCochains.d A n : Fun(Gⁿ, A) →ₗ[k] Fun(Gⁿ⁺¹, A)`. -/
def cocyclesIso (n : ℕ) :
    cocycles A n ≅ ModuleCat.of k (LinearMap.ker (inhomogeneousCochains.d A n)) :=
  (inhomogeneousCochains A).cyclesIsoSc' _ _ _ (by aesop) (by aesop) ≪≫
    ShortComplex.moduleCatCyclesIso _ ≪≫ (LinearEquiv.ofEq _ _ <| by simp).toModuleIso

theorem cocyclesIso_inv_eq {n : ℕ} (x : (inhomogeneousCochains A).X n)
    (hx : inhomogeneousCochains.d A n x = 0) :
    (cocyclesIso A n).inv ⟨x, hx⟩ =
      (inhomogeneousCochains A).cyclesMk x (n + 1) (CochainComplex.next _ _) (by simpa using hx) :=
  congr(((inhomogeneousCochains A).cyclesIsoSc' _ _ _ (by aesop) (by aesop)).inv
    $(ShortComplex.moduleCatCyclesIso_inv_apply x (by simpa using hx))).trans
    ((inhomogeneousCochains A).cyclesIsoSc'_inv_cyclesMk x rfl (CochainComplex.next _ _) _)

/-- The natural inclusion of the `n`-cocycles `Zⁿ(G, A)` into the `n`-cochains `Cⁿ(G, A).` -/
abbrev iCocycles (n : ℕ) : cocycles A n ⟶ ModuleCat.of k ((Fin n → G) → A) :=
  (inhomogeneousCochains A).iCycles n

@[reassoc (attr := simp, elementwise)]
theorem cocyclesIso_inv_comp_iCocycles (n : ℕ) :
    (cocyclesIso A n).inv ≫ iCocycles A n = Submodule.subtype _ := by
  ext
  simp only [cocyclesIso, Iso.trans_inv, Category.assoc, cyclesIsoSc'_inv_iCycles,
    ShortComplex.moduleCatCyclesIso_inv_iCycles]
  simp [moduleCat_simps]

@[reassoc (attr := simp, elementwise)]
theorem cocyclesIso_hom_comp_subtype :
    (cocyclesIso A n).hom ≫ Submodule.subtype _ = iCocycles _ _ := by
  simp only [← Iso.eq_inv_comp, cocyclesIso_inv_comp_iCocycles]

/-- This is the map from `i`-cochains to `j`-cocycles induced by the differential in the complex of
inhomogeneous cochains. -/
abbrev toCocycles (i j : ℕ) : ModuleCat.of k ((Fin i → G) → A) ⟶ cocycles A j :=
  (inhomogeneousCochains A).toCycles i j

end groupCohomology

open groupCohomology

/-- The group cohomology of a `k`-linear `G`-representation `A`, as the cohomology of its complex
of inhomogeneous cochains. -/
def groupCohomology [Group G] (A : Rep k G) (n : ℕ) : ModuleCat k :=
  (inhomogeneousCochains A).homology n

/-- The natural map from `n`-cocycles to `n`th group cohomology for a `k`-linear
`G`-representation `A`. -/
abbrev groupCohomologyπ [Group G] (A : Rep k G) (n : ℕ) :
    groupCohomology.cocycles A n ⟶ groupCohomology A n :=
  (inhomogeneousCochains A).homologyπ n

/-- The `n`th group cohomology of a `k`-linear `G`-representation `A` is isomorphic to
`Extⁿ(k, A)` (taken in `Rep k G`), where `k` is a trivial `k`-linear `G`-representation. -/
def groupCohomologyIsoExt [Group G] (A : Rep k G) (n : ℕ) :
    groupCohomology A n ≅ ((Ext k (Rep k G) n).obj (Opposite.op <| Rep.trivial k G k)).obj A :=
  isoOfQuasiIsoAt (HomotopyEquiv.ofIso (inhomogeneousCochainsIso A)).hom n ≪≫
    (Rep.barResolution.extIso k G A n).symm
