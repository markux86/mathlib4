import Mathlib.RingTheory.Kaehler
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.Algebra.Module.Projective

universe u

open TensorProduct

section

variable (R S T) [CommRing R] [CommRing S] [CommRing T]
variable [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]

open KaehlerDifferential (D)

@[simps]
noncomputable
def kerToTensor :
    RingHom.ker (algebraMap S T) →ₗ[S] T ⊗[S] Ω[S⁄R] where
  toFun x := 1 ⊗ₜ D R S x
  map_add' x y := by simp only [AddSubmonoid.coe_add, Submodule.coe_toAddSubmonoid, map_add,
    tmul_add]
  map_smul' r x := by simp only [SetLike.val_smul, smul_eq_mul, Derivation.leibniz, tmul_add,
    tmul_smul, smul_tmul', ← Algebra.algebraMap_eq_smul_one, (RingHom.mem_ker _).mp x.prop,
    zero_tmul, add_zero, RingHom.id_apply]

noncomputable
def kerCotangentToTensor :
    (RingHom.ker (algebraMap S T)).Cotangent →ₗ[S] T ⊗[S] Ω[S⁄R] := by
  refine Submodule.liftQ _ (kerToTensor R S T) (iSup_le_iff.mpr ?_)
  simp only [Submodule.map_le_iff_le_comap, Subtype.forall]
  rintro x hx y -
  simp only [Submodule.mem_comap, LinearMap.lsmul_apply, LinearMap.mem_ker, map_smul, zero_tmul,
    kerToTensor_apply, ← Algebra.algebraMap_eq_smul_one, (RingHom.mem_ker _).mp hx, smul_tmul']

lemma kerCotangentToTensor_apply (x) :
  kerCotangentToTensor R S T (Ideal.toCotangent _ x) = 1 ⊗ₜ D _ _ x.1 := rfl

end

open Function (Surjective)

variable {R P S : Type u} [CommRing R] [CommRing P] [CommRing S]
variable [Algebra R S] [Algebra R P] [Algebra P S] [IsScalarTower R P S]
variable (hf : Surjective (algebraMap P S)) (hf' : (RingHom.ker (algebraMap P S)) ^ 2 = ⊥)

section ofSection

variable (g : S →ₐ[R] P) (hg : (IsScalarTower.toAlgHom R P S).comp g = AlgHom.id R S)

@[simps]
def derivationOfSectionOfKerSqZero : Derivation R P (RingHom.ker (algebraMap P S)) where
  toFun x := ⟨x - g (algebraMap _ _ x), by
    simpa [RingHom.mem_ker, sub_eq_zero] using AlgHom.congr_fun hg.symm (algebraMap _ _ x)⟩
  map_add' x y := by simp only [map_add, AddSubmonoid.mk_add_mk, Subtype.mk.injEq]; ring
  map_smul' x y := by
    ext
    simp only [Algebra.smul_def, _root_.map_mul, ← IsScalarTower.algebraMap_apply,
      AlgHom.commutes, RingHom.id_apply, Submodule.coe_smul_of_tower]
    ring
  map_one_eq_zero' := by simp only [LinearMap.coe_mk, AddHom.coe_mk, _root_.map_one, sub_self,
    AddSubmonoid.mk_eq_zero]
  leibniz' a b := by
    have : (a - g (algebraMap _ _ a)) * (b - g (algebraMap _ _ b)) = 0 := by
      rw [← Ideal.mem_bot, ← hf', pow_two]
      apply Ideal.mul_mem_mul
      · simpa [RingHom.mem_ker, sub_eq_zero] using AlgHom.congr_fun hg.symm (algebraMap P S a)
      · simpa [RingHom.mem_ker, sub_eq_zero] using AlgHom.congr_fun hg.symm (algebraMap P S b)
    ext
    rw [← sub_eq_zero]
    conv_rhs => rw [← neg_zero, ← this]
    simp only [LinearMap.coe_mk, AddHom.coe_mk, _root_.map_mul, SetLike.mk_smul_mk, smul_eq_mul,
      mul_sub, AddSubmonoid.mk_add_mk, sub_mul, neg_sub]
    ring

instance isScalarTower_of_section_of_ker_sqZero :
    letI := g.toRingHom.toAlgebra; IsScalarTower P S (RingHom.ker (algebraMap P S)) := by
  letI := g.toRingHom.toAlgebra
  constructor
  intro p s m
  ext
  show g (p • s) * m = p * (g s * m)
  simp only [Algebra.smul_def, _root_.map_mul, mul_assoc, mul_left_comm _ (g s)]
  congr 1
  rw [← sub_eq_zero, ← Ideal.mem_bot, ← hf', pow_two, ← sub_mul]
  refine Ideal.mul_mem_mul ?_ m.2
  simpa [RingHom.mem_ker, sub_eq_zero] using AlgHom.congr_fun hg (algebraMap P S p)

noncomputable
def retractionOfSectionOfKerSqZero : S ⊗[P] Ω[P⁄R] →ₗ[P] RingHom.ker (algebraMap P S) :=
    letI := g.toRingHom.toAlgebra
    haveI := isScalarTower_of_section_of_ker_sqZero hf' g hg
    letI f := (derivationOfSectionOfKerSqZero hf' g hg).liftKaehlerDifferential
    (AlgebraTensorModule.lift ((LinearMap.ringLmapEquivSelf S S _).symm f)).restrictScalars P

@[simp]
lemma retractionOfSectionOfKerSqZero_tmul_D (s : S) (t : P) :
    retractionOfSectionOfKerSqZero hf' g hg (s ⊗ₜ .D _ _ t) =
      g s * t - g s * g (algebraMap _ _ t) := by
  letI := g.toRingHom.toAlgebra
  haveI := isScalarTower_of_section_of_ker_sqZero hf' g hg
  simpa [retractionOfSectionOfKerSqZero] using (mul_sub (g s) t (g (algebraMap P S t)))

lemma retractionOfSectionOfKerSqZero_comp_kerToTensor :
    (retractionOfSectionOfKerSqZero hf' g hg).comp (kerToTensor R P S) = LinearMap.id := by
  ext x; simp [(RingHom.mem_ker _).mp x.2]

end ofSection

section ofRetraction

variable (l : S ⊗[P] Ω[P⁄R] →ₗ[P] RingHom.ker (algebraMap P S))
variable (hl : l.comp (kerToTensor R P S) = LinearMap.id)

-- suppose we have a (set-theoretic) section
variable (σ : S → P) (hσ : ∀ x, algebraMap P S (σ x) = x)

lemma sectionOfRetractionKerToTensorAux_prop (x y) (h : algebraMap P S x = algebraMap P S y) :
    x - l (1 ⊗ₜ .D _ _ x) = y - l (1 ⊗ₜ .D _ _ y) := by
  rw [sub_eq_iff_eq_add, sub_add_comm, ← sub_eq_iff_eq_add, ← Submodule.coe_sub,
    ← map_sub, ← tmul_sub, ← map_sub]
  exact congr_arg Subtype.val (LinearMap.congr_fun hl.symm ⟨x - y, by simp [RingHom.mem_ker, h]⟩)

noncomputable
def sectionOfRetractionKerToTensorAux : S →ₐ[R] P where
  toFun x := σ x - l (1 ⊗ₜ .D _ _ (σ x))
  map_one' := by simp [sectionOfRetractionKerToTensorAux_prop l hl (σ 1) 1 (by simp [hσ])]
  map_mul' a b := by
    have (x y) : (l x).1 * (l y).1 = 0 := by
      rw [← Ideal.mem_bot, ← hf', pow_two]; exact Ideal.mul_mem_mul (l x).2 (l y).2
    simp only [sectionOfRetractionKerToTensorAux_prop l hl (σ (a * b)) (σ a * σ b) (by simp [hσ]),
      Derivation.leibniz, tmul_add, tmul_smul, map_add, map_smul, AddSubmonoid.coe_add, this,
      Submodule.coe_toAddSubmonoid, SetLike.val_smul, smul_eq_mul, mul_sub, sub_mul, sub_zero]
    ring
  map_add' a b := by
    simp only [sectionOfRetractionKerToTensorAux_prop l hl (σ (a + b)) (σ a + σ b) (by simp [hσ]),
      map_add, tmul_add, AddSubmonoid.coe_add, Submodule.coe_toAddSubmonoid, add_sub_add_comm]
  map_zero' := by simp [sectionOfRetractionKerToTensorAux_prop l hl (σ 0) 0 (by simp [hσ])]
  commutes' r := by
    simp [sectionOfRetractionKerToTensorAux_prop l hl
      (σ (algebraMap R S r)) (algebraMap R P r) (by simp [hσ, ← IsScalarTower.algebraMap_apply])]

lemma sectionOfRetractionKerToTensorAux_algebraMap (x : P) :
    sectionOfRetractionKerToTensorAux hf' l hl σ hσ (algebraMap P S x) = x - l (1 ⊗ₜ .D _ _ x) :=
  sectionOfRetractionKerToTensorAux_prop l hl _ x (by simp [hσ])

noncomputable def sectionOfRetractionKerToTensor : S →ₐ[R] P :=
  sectionOfRetractionKerToTensorAux hf' l hl _ (fun x ↦ (hf x).choose_spec)

@[simp]
lemma sectionOfRetractionKerToTensor_algebraMap (x : P) :
    sectionOfRetractionKerToTensor hf hf' l hl (algebraMap P S x) = x - l (1 ⊗ₜ .D _ _ x) :=
  sectionOfRetractionKerToTensorAux_algebraMap hf' l hl _ _ x

@[simp]
lemma toAlgHom_comp_sectionOfRetractionKerToTensor :
    (IsScalarTower.toAlgHom R P S).comp
      (sectionOfRetractionKerToTensor hf hf' l hl) = AlgHom.id _ _ := by
  ext x
  obtain ⟨x, rfl⟩ := hf x
  simp [(RingHom.mem_ker _).mp]

end ofRetraction

noncomputable
def retractionEquivSectionKerToTensor :
    { l // l ∘ₗ (kerToTensor R P S) = LinearMap.id } ≃
      { g // (IsScalarTower.toAlgHom R P S).comp g = AlgHom.id R S } where
  toFun l := ⟨_, toAlgHom_comp_sectionOfRetractionKerToTensor hf hf' _ l.2⟩
  invFun g := ⟨_, retractionOfSectionOfKerSqZero_comp_kerToTensor hf' _ g.2⟩
  left_inv l := by
    ext s p
    obtain ⟨s, rfl⟩ := hf s
    have (x y) : (l.1 x).1 * (l.1 y).1 = 0 := by
      rw [← Ideal.mem_bot, ← hf', pow_two]; exact Ideal.mul_mem_mul (l.1 x).2 (l.1 y).2
    simp only [AlgebraTensorModule.curry_apply,
      Derivation.coe_comp, LinearMap.coe_comp, LinearMap.coe_restrictScalars, Derivation.coeFn_coe,
      Function.comp_apply, curry_apply, retractionOfSectionOfKerSqZero_tmul_D,
      sectionOfRetractionKerToTensor_algebraMap, ← mul_sub, sub_sub_cancel]
    rw [sub_mul]
    simp only [this, Algebra.algebraMap_eq_smul_one, ← smul_tmul', LinearMapClass.map_smul,
      SetLike.val_smul, smul_eq_mul, sub_zero]
  right_inv g := by ext s; obtain ⟨s, rfl⟩ := hf s; simp

attribute [local instance 99999] IsScalarTower.right

instance : Algebra (P ⧸ (RingHom.ker (algebraMap P S) ^ 2)) S :=
  (Algebra.ofId P S).kerSquareLift.toAlgebra

instance : IsScalarTower R (P ⧸ (RingHom.ker (algebraMap P S) ^ 2)) S :=
  IsScalarTower.of_algebraMap_eq'
    (IsScalarTower.toAlgHom R P S).kerSquareLift.comp_algebraMap.symm

variable (R P S) in
noncomputable
def derivationQuotKerSq :
    Derivation R (P ⧸ (RingHom.ker (algebraMap P S) ^ 2)) (S ⊗[P] Ω[P⁄R]) := by
  letI := Submodule.liftQ ((RingHom.ker (algebraMap P S) ^ 2).restrictScalars R)
    (((mk P S _ 1).restrictScalars R).comp (KaehlerDifferential.D R P).toLinearMap)
  refine ⟨this ?_, ?_, ?_⟩
  · rintro x hx
    simp only [Submodule.restrictScalars_mem, pow_two] at hx
    simp only [LinearMap.mem_ker, LinearMap.coe_comp, LinearMap.coe_restrictScalars,
      Derivation.coeFn_coe, Function.comp_apply, mk_apply]
    refine Submodule.smul_induction_on hx ?_ ?_
    · intro x hx y hy
      simp only [smul_eq_mul, Derivation.leibniz, tmul_add, ← smul_tmul, Algebra.smul_def,
        mul_one, (RingHom.mem_ker _).mp hx, (RingHom.mem_ker _).mp hy, zero_tmul, zero_add]
    · intro x y hx hy; simp only [map_add, hx, hy, tmul_add, zero_add]
  · show (1 : S) ⊗ₜ[P] KaehlerDifferential.D R P 1 = 0; simp
  · intro a b
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ a
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ b
    show (1 : S) ⊗ₜ[P] KaehlerDifferential.D R P (a * b) =
      Ideal.Quotient.mk _ a • ((1 : S) ⊗ₜ[P] KaehlerDifferential.D R P b) +
      Ideal.Quotient.mk _ b • ((1 : S) ⊗ₜ[P] KaehlerDifferential.D R P a)
    simp only [← Ideal.Quotient.algebraMap_eq, IsScalarTower.algebraMap_smul,
      Derivation.leibniz, tmul_add, tmul_smul]

@[simp]
lemma derivationQuotKerSq_mk (x) :
    derivationQuotKerSq R P S (Ideal.Quotient.mk _ x) = 1 ⊗ₜ .D R P x := rfl

variable (R P S) in
noncomputable
def tensorKaehlerQuotKerSqEquiv :
    S ⊗[P ⧸ (RingHom.ker (algebraMap P S) ^ 2)] Ω[(P ⧸ (RingHom.ker (algebraMap P S) ^ 2))⁄R]
      ≃ₗ[S] S ⊗[P] Ω[P⁄R] := by
  letI f₁ := (derivationQuotKerSq R P S).liftKaehlerDifferential
  letI f₂ := AlgebraTensorModule.lift ((LinearMap.ringLmapEquivSelf S S _).symm f₁)
  letI f₃ := KaehlerDifferential.map R R P (P ⧸ (RingHom.ker (algebraMap P S) ^ 2))
  letI f₄ := ((mk (P ⧸ RingHom.ker (algebraMap P S) ^ 2) S _ 1).restrictScalars P).comp f₃
  letI f₅ := AlgebraTensorModule.lift ((LinearMap.ringLmapEquivSelf S S _).symm f₄)
  refine { __ := f₂, invFun := f₅, left_inv := ?_, right_inv := ?_ }
  · suffices f₅.comp f₂ = LinearMap.id from LinearMap.congr_fun this
    ext a
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    simp [f₁, f₂, f₃, f₄, f₅]
  · suffices f₂.comp f₅ = LinearMap.id from LinearMap.congr_fun this
    ext a
    simp [f₁, f₂, f₃, f₄, f₅]

@[simp]
lemma tensorKaehlerQuotKerSqEquiv_tmul_D (s t) :
    tensorKaehlerQuotKerSqEquiv R P S (s ⊗ₜ .D _ _ (Ideal.Quotient.mk _ t)) = s ⊗ₜ .D _ _ t := by
  show s • (derivationQuotKerSq R P S).liftKaehlerDifferential (.D _ _ (Ideal.Quotient.mk _ t)) = _
  simp [smul_tmul']

@[simp]
lemma tensorKaehlerQuotKerSqEquiv_symm_tmul_D (s t) :
    (tensorKaehlerQuotKerSqEquiv R P S).symm (s ⊗ₜ .D _ _ t) =
      s ⊗ₜ .D _ _ (Ideal.Quotient.mk _ t) := by
  apply (tensorKaehlerQuotKerSqEquiv R P S).injective
  simp

noncomputable
def retractionEquivSectionKerCotangentToTensor :
    { l // l ∘ₗ (kerCotangentToTensor R P S) = LinearMap.id } ≃
      { g // (IsScalarTower.toAlgHom R P S).kerSquareLift.comp g = AlgHom.id R S } := by
  let P' := P ⧸ (RingHom.ker (algebraMap P S) ^ 2)
  have h₁ : Surjective (algebraMap P' S) := Function.Surjective.of_comp (g := algebraMap P P') hf
  have h₂ : RingHom.ker (algebraMap P' S) ^ 2 = ⊥ := by
    rw [RingHom.algebraMap_toAlgebra, AlgHom.ker_kerSquareLift, Ideal.cotangentIdeal_square]
  let e₁ : (RingHom.ker (algebraMap P S)).Cotangent ≃ₗ[P] (RingHom.ker (algebraMap P' S)) := by
    refine (Ideal.cotangentEquivIdeal _).trans ((LinearEquiv.ofEq _ _
      (IsScalarTower.toAlgHom R P S).ker_kerSquareLift.symm).restrictScalars P)
  let e₂ : S ⊗[P'] Ω[P'⁄R] ≃ₗ[P] S ⊗[P] Ω[P⁄R] :=
    (tensorKaehlerQuotKerSqEquiv R P S).restrictScalars P
  have H : kerCotangentToTensor R P S =
      e₂.toLinearMap ∘ₗ (kerToTensor R P' S ).restrictScalars P ∘ₗ e₁.toLinearMap := by
    ext x
    obtain ⟨x, rfl⟩ := Ideal.toCotangent_surjective _ x
    exact (tensorKaehlerQuotKerSqEquiv_tmul_D 1 x.1).symm
  refine Equiv.trans ?_ (retractionEquivSectionKerToTensor (R := R) h₁ h₂)
  refine ⟨fun ⟨l, hl⟩ ↦ ⟨⟨(e₁.toLinearMap ∘ₗ l ∘ₗ e₂.toLinearMap).toAddMonoidHom, ?_⟩, ?_⟩,
    fun ⟨l, hl⟩ ↦ ⟨e₁.symm.toLinearMap ∘ₗ l.restrictScalars P ∘ₗ e₂.symm.toLinearMap, ?_⟩, ?_, ?_⟩
  · rintro x y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp only [← Ideal.Quotient.algebraMap_eq, IsScalarTower.algebraMap_smul]
    exact (e₁.toLinearMap ∘ₗ l ∘ₗ e₂.toLinearMap).map_smul x y
  · ext1 x
    rw [H] at hl
    obtain ⟨x, rfl⟩ := e₁.surjective x
    exact DFunLike.congr_arg e₁ (LinearMap.congr_fun hl x)
  · ext x
    rw [H]
    apply e₁.injective
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, LinearMap.coe_restrictScalars,
      Function.comp_apply, LinearEquiv.symm_apply_apply, LinearMap.id_coe, id_eq,
      LinearEquiv.apply_symm_apply]
    exact LinearMap.congr_fun hl (e₁ x)
  · intro f
    ext x
    simp only [AlgebraTensorModule.curry_apply, Derivation.coe_comp, LinearMap.coe_comp,
      LinearMap.coe_restrictScalars, Derivation.coeFn_coe, Function.comp_apply, curry_apply,
      LinearEquiv.coe_coe, LinearMap.coe_mk, AddHom.coe_coe, LinearMap.toAddMonoidHom_coe,
      LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply]
  · intro f
    ext x
    simp only [AlgebraTensorModule.curry_apply, Derivation.coe_comp, LinearMap.coe_comp,
      LinearMap.coe_restrictScalars, Derivation.coeFn_coe, Function.comp_apply, curry_apply,
      LinearMap.coe_mk, AddHom.coe_coe, LinearMap.toAddMonoidHom_coe, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply]

variable [Algebra.FormallySmooth R P]

theorem Algebra.FormallySmooth.iff_split_injection :
    Algebra.FormallySmooth R S ↔ ∃ l, l ∘ₗ (kerCotangentToTensor R P S) = LinearMap.id := by
  have := (retractionEquivSectionKerCotangentToTensor (R := R) hf).nonempty_congr
  simp only [nonempty_subtype] at this
  rw [this, ← Algebra.FormallySmooth.iff_split_surjection _ hf]

attribute [local instance 99999] KaehlerDifferential.module'

open LinearMap in
noncomputable
def Function.Exact.splitSurjectiveEquiv
    {R M N P} [Semiring R] [AddCommGroup M] [AddCommGroup N]
    [AddCommGroup P] [Module R M] [Module R N] [Module R P] {f : M →ₗ[R] N} {g : N →ₗ[R] P}
    (h : Function.Exact f g) (hf : Function.Injective f) :
    { l // g ∘ₗ l = .id } ≃
      { e : N ≃ₗ[R] M × P // f = e.symm ∘ₗ inl R M P ∧ g = snd R M P ∘ₗ e } := by
  refine
  { toFun := fun l ↦ ⟨(LinearEquiv.ofBijective (f ∘ₗ fst R M P + l.1 ∘ₗ snd R M P) ?_).symm, ?_⟩
    invFun := fun e ↦ ⟨e.1.symm ∘ₗ inr R M P, ?_⟩
    left_inv := ?_
    right_inv := ?_ }
  · have h₁ : ∀ x, g (l.1 x) = x := LinearMap.congr_fun l.2
    have h₂ : ∀ x, g (f x) = 0 := congr_fun h.comp_eq_zero
    constructor
    · intros x y e
      simp only [add_apply, coe_comp, comp_apply, fst_apply, snd_apply] at e
      suffices x.2 = y.2 from Prod.ext (hf (by rwa [this, add_left_inj] at e)) this
      simpa [h₁, h₂] using DFunLike.congr_arg g e
    · intro x
      obtain ⟨y, hy⟩ := (h (x - l.1 (g x))).mp (by simp [h₁, g.map_sub])
      exact ⟨⟨y, g x⟩, by simp [hy]⟩
  · have h₁ : ∀ x, g (l.1 x) = x := LinearMap.congr_fun l.2
    have h₂ : ∀ x, g (f x) = 0 := congr_fun h.comp_eq_zero
    constructor
    · ext; simp
    · rw [LinearEquiv.eq_comp_toLinearMap_symm]
      ext <;> simp [h₁, h₂]
  · rw [← LinearMap.comp_assoc, (LinearEquiv.eq_comp_toLinearMap_symm _ _).mp e.2.2]; rfl
  · intro; ext; simp
  · rintro ⟨e, rfl, rfl⟩
    ext1
    apply LinearEquiv.symm_bijective.injective
    ext
    apply e.injective
    ext <;> simp

open LinearMap in
noncomputable
def Function.Exact.splitInjectiveEquiv
    {R M N P} [Semiring R] [AddCommGroup M] [AddCommGroup N]
    [AddCommGroup P] [Module R M] [Module R N] [Module R P] {f : M →ₗ[R] N} {g : N →ₗ[R] P}
    (h : Function.Exact f g) (hg : Function.Surjective g) :
    { l // l ∘ₗ f = .id } ≃
      { e : N ≃ₗ[R] M × P // f = e.symm ∘ₗ inl R M P ∧ g = snd R M P ∘ₗ e } := by
  refine
  { toFun := fun l ↦ ⟨(LinearEquiv.ofBijective (l.1.prod g) ?_), ?_⟩
    invFun := fun e ↦ ⟨fst R M P ∘ₗ e.1, ?_⟩
    left_inv := ?_
    right_inv := ?_ }
  · have h₁ : ∀ x, l.1 (f x) = x := LinearMap.congr_fun l.2
    have h₂ : ∀ x, g (f x) = 0 := congr_fun h.comp_eq_zero
    constructor
    · intros x y e
      simp only [prod_apply, Pi.prod, Prod.mk.injEq] at e
      obtain ⟨z, hz⟩ := (h (x - y)).mp (by simpa [sub_eq_zero] using e.2)
      suffices z = 0 by rw [← sub_eq_zero, ← hz, this, map_zero]
      rw [← h₁ z, hz, map_sub, e.1, sub_self]
    · rintro ⟨x, y⟩
      obtain ⟨y, rfl⟩ := hg y
      refine ⟨f x + y - f (l.1 y), by ext <;> simp [h₁, h₂]⟩
  · have h₁ : ∀ x, l.1 (f x) = x := LinearMap.congr_fun l.2
    have h₂ : ∀ x, g (f x) = 0 := congr_fun h.comp_eq_zero
    constructor
    · rw [LinearEquiv.eq_toLinearMap_symm_comp]
      ext <;> simp [h₁, h₂]
    · ext; simp
  · rw [LinearMap.comp_assoc, (LinearEquiv.eq_toLinearMap_symm_comp _ _).mp e.2.1]; rfl
  · intro; ext; simp
  · rintro ⟨e, rfl, rfl⟩
    ext x <;> simp

theorem Function.Exact.split_tfae'
    {R M N P} [Semiring R] [AddCommGroup M] [AddCommGroup N]
    [AddCommGroup P] [Module R M] [Module R N] [Module R P] {f : M →ₗ[R] N} {g : N →ₗ[R] P}
    (h : Function.Exact f g) :
    List.TFAE [
      Function.Injective f ∧ ∃ l, g ∘ₗ l = LinearMap.id,
      Function.Surjective g ∧ ∃ l, l ∘ₗ f = LinearMap.id,
      ∃ e : N ≃ₗ[R] M × P, f = e.symm ∘ₗ LinearMap.inl R M P ∧ g = LinearMap.snd R M P ∘ₗ e] := by
  tfae_have 1 → 3
  · rintro ⟨hf, l, hl⟩
    exact ⟨_, (h.splitSurjectiveEquiv hf ⟨l, hl⟩).2⟩
  tfae_have 2 → 3
  · rintro ⟨hg, l, hl⟩
    exact ⟨_, (h.splitInjectiveEquiv hg ⟨l, hl⟩).2⟩
  tfae_have 3 → 1
  · rintro ⟨e, e₁, e₂⟩
    have : Function.Injective f := e₁ ▸ e.symm.injective.comp LinearMap.inl_injective
    refine ⟨this, ⟨_, ((h.splitSurjectiveEquiv this).symm ⟨e, e₁, e₂⟩).2⟩⟩
  tfae_have 3 → 2
  · rintro ⟨e, e₁, e₂⟩
    have : Function.Surjective g := e₂ ▸ Prod.snd_surjective.comp e.surjective
    refine ⟨this, ⟨_, ((h.splitInjectiveEquiv this).symm ⟨e, e₁, e₂⟩).2⟩⟩
  tfae_finish

theorem Function.Exact.split_tfae
    {R M N P} [Semiring R] [AddCommGroup M] [AddCommGroup N]
    [AddCommGroup P] [Module R M] [Module R N] [Module R P] {f : M →ₗ[R] N} {g : N →ₗ[R] P}
    (h : Function.Exact f g) (hf : Function.Injective f) (hg : Function.Surjective g) :
    List.TFAE [
      ∃ l, g ∘ₗ l = LinearMap.id,
      ∃ l, l ∘ₗ f = LinearMap.id,
      ∃ e : N ≃ₗ[R] M × P, f = e.symm ∘ₗ LinearMap.inl R M P ∧ g = LinearMap.snd R M P ∘ₗ e] := by
  tfae_have 1 ↔ 3
  · simpa using (h.splitSurjectiveEquiv hf).nonempty_congr
  tfae_have 2 ↔ 3
  · simpa using (h.splitInjectiveEquiv hg).nonempty_congr
  tfae_finish

local macro "finsupp_map" : term =>
  `((Finsupp.mapRange.linearMap (Algebra.linearMap P S)).comp
    (Finsupp.lmapDomain P P (algebraMap P S)))

lemma KaehlerDifferential.ker_map_of_surjective (h : Function.Surjective (algebraMap P S)) :
    LinearMap.ker (map R R P S) =
      (LinearMap.ker finsupp_map).map (Finsupp.total P _ P (D R P)) := by
  rw [ker_map, ← kerTotal_map' R P S h, Submodule.comap_map_eq, Submodule.map_sup,
    Submodule.map_sup, ← kerTotal_eq, ← Submodule.comap_bot, Submodule.map_comap_eq_of_surjective,
    bot_sup_eq, Submodule.map_span, ← Set.range_comp]
  convert bot_sup_eq _
  rw [Submodule.span_eq_bot]; simp
  exact total_surjective _ _

theorem range_kerCotangentToTensor :
    LinearMap.range (kerCotangentToTensor R P S) =
      (LinearMap.ker (KaehlerDifferential.mapBaseChange R P S)).restrictScalars P := by
  classical
  ext x
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨x, rfl⟩ := Ideal.toCotangent_surjective _ x
    simp [kerCotangentToTensor_apply, (RingHom.mem_ker _).mp x.2]
  · intro hx
    obtain ⟨x, rfl⟩ := LinearMap.rTensor_surjective (Ω[P⁄R]) (g := Algebra.linearMap P S) hf x
    obtain ⟨x, rfl⟩ := (TensorProduct.lid _ _).symm.surjective x
    replace hx : x ∈ LinearMap.ker (KaehlerDifferential.map R R P S) := by simpa using hx
    rw [KaehlerDifferential.ker_map_of_surjective hf] at hx
    obtain ⟨x, hx, rfl⟩ := hx
    simp only [lid_symm_apply, LinearMap.rTensor_tmul, Algebra.linearMap_apply, _root_.map_one]
    rw [← Finsupp.sum_single x, Finsupp.sum, ← Finset.sum_fiberwise_of_maps_to
      (fun _ ↦ Finset.mem_image_of_mem (algebraMap P S))]
    simp only [Function.comp_apply, map_sum (s := x.support.image (algebraMap P S)), tmul_sum]
    apply sum_mem
    intro c _
    simp only [Finset.filter_congr_decidable, TensorProduct.lid_symm_apply, LinearMap.rTensor_tmul,
      AlgHom.toLinearMap_apply, _root_.map_one, LinearMap.mem_range]
    simp only [map_sum, Finsupp.total_single]
    have : (x.support.filter (algebraMap P S · = c)).sum x ∈ RingHom.ker (algebraMap P S) := by
      simpa [Finsupp.mapDomain, Finsupp.sum, Finsupp.finset_sum_apply, RingHom.mem_ker,
        Finsupp.single_apply, ← Finset.sum_filter] using DFunLike.congr_fun hx c
    obtain ⟨a, ha⟩ := hf c
    use (x.support.filter (algebraMap P S · = c)).attach.sum
        fun i ↦ x i • Ideal.toCotangent _ ⟨i - a, ?_⟩; swap
    · have : x i ≠ 0 ∧ algebraMap P S i = c := by simpa using i.prop
      simp [RingHom.mem_ker, ha, this.2]
    · simp only [map_sum, LinearMapClass.map_smul, kerCotangentToTensor_apply, map_sub]
      simp_rw [← TensorProduct.tmul_smul]
      simp only [smul_sub, TensorProduct.tmul_sub, Finset.sum_sub_distrib, ← TensorProduct.tmul_sum,
        ← Finset.sum_smul, Finset.sum_attach, sub_eq_self,
        Finset.sum_attach (f := fun i ↦ x i • KaehlerDifferential.D R P i)]
      rw [← TensorProduct.smul_tmul, ← Algebra.algebraMap_eq_smul_one, (RingHom.mem_ker _).mp this,
        TensorProduct.zero_tmul]

theorem exact_kerCotangentToTensor_mapBaseChange :
    Function.Exact (kerCotangentToTensor R P S) (KaehlerDifferential.mapBaseChange R P S) :=
  SetLike.ext_iff.mp (range_kerCotangentToTensor hf).symm

lemma KaehlerDifferential.subsingleton_of_surjective :
    Subsingleton (Ω[S⁄P]) := by
  suffices (⊤ : Submodule S (Ω[S⁄P])) ≤ ⊥ from
    (subsingleton_iff_forall_eq 0).mpr fun y ↦ this trivial
  rw [← KaehlerDifferential.span_range_derivation, Submodule.span_le]
  rintro _ ⟨x, rfl⟩; obtain ⟨x, rfl⟩ := hf x; simp

lemma KaehlerDifferential.mapBaseChange_surjective :
    Function.Surjective (KaehlerDifferential.mapBaseChange R P S) := by
  have := subsingleton_of_surjective hf
  rw [← LinearMap.range_eq_top, KaehlerDifferential.range_mapBaseChange, ← top_le_iff]
  exact fun x _ ↦ Subsingleton.elim _ _

@[simps!]
def LinearMap.restrictScalarsEquiv {R S M N} [CommSemiring R] [Semiring S] [AddCommMonoid M]
    [AddCommMonoid N] [Algebra R S] [Module R M] [Module S M] [IsScalarTower R S M]
    [Module R N] [Module S N] [IsScalarTower R S N]
    (h : Function.Surjective (algebraMap R S)) : (M →ₗ[S] N) ≃ₗ[R] (M →ₗ[R] N) where
  toFun := restrictScalars R
  map_add' f g := rfl
  map_smul' r f := rfl
  invFun f := ⟨f.toAddMonoidHom, h.forall.mpr (by simp)⟩
  left_inv f := rfl
  right_inv f := rfl

theorem Algebra.FormallySmooth.iff_injective_and_split :
    Algebra.FormallySmooth R S ↔ Function.Injective (kerCotangentToTensor R P S) ∧
      ∃ l, (KaehlerDifferential.mapBaseChange R P S) ∘ₗ l = LinearMap.id := by
  rw [Algebra.FormallySmooth.iff_split_injection hf]
  refine (and_iff_right (KaehlerDifferential.mapBaseChange_surjective (R := R) hf)).symm.trans ?_
  refine Iff.trans (((exact_kerCotangentToTensor_mapBaseChange hf).split_tfae'
    (g := (KaehlerDifferential.mapBaseChange R P S).restrictScalars P)).out 1 0)
    (and_congr Iff.rfl ?_)
  rw [(LinearMap.restrictScalarsEquiv hf).surjective.exists]
  simp only [LinearMap.ext_iff, LinearMap.coe_comp, LinearMap.coe_restrictScalars,
    Function.comp_apply, LinearMap.restrictScalarsEquiv_apply_apply, LinearMap.id_coe, id_eq]

theorem Algebra.FormallySmooth.iff_injective_and_projective' :
    letI : Algebra (MvPolynomial S R) S := (MvPolynomial.aeval _root_.id).toAlgebra
    Algebra.FormallySmooth R S ↔
        Function.Injective (kerCotangentToTensor R (MvPolynomial S R) S) ∧
        Module.Projective S (Ω[S⁄R]) := by sorry
  -- letI : Algebra (MvPolynomial S R) S := (MvPolynomial.aeval _root_.id).toAlgebra
  -- have : Function.Surjective (algebraMap (MvPolynomial S R) S) :=
  --   fun x ↦ ⟨.X x, MvPolynomial.aeval_X _ _⟩
  -- rw [Algebra.FormallySmooth.iff_injective_and_split this,
  --   ← Module.Projective.iff_split_of_projective]
  -- exact KaehlerDifferential.mapBaseChange_surjective this

instance : Module.Projective P (Ω[P⁄R]) :=
  (Algebra.FormallySmooth.iff_injective_and_projective'.mp ‹_›).2

theorem Algebra.FormallySmooth.iff_injective_and_projective :
    Algebra.FormallySmooth R S ↔
        Function.Injective (kerCotangentToTensor R P S) ∧ Module.Projective S (Ω[S⁄R]) := by sorry
  -- rw [Algebra.FormallySmooth.iff_injective_and_split hf,
  --   ← Module.Projective.iff_split_of_projective]
  -- exact KaehlerDifferential.mapBaseChange_surjective hf
