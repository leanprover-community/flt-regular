import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.DedekindDomain.Ideal
import Mathlib.RingTheory.Discriminant
import Mathlib.RingTheory.Localization.FractionRing
import FltRegular.NumberTheory.QuotientTrace
import Mathlib.NumberTheory.KummerDedekind
/-!
# The different ideal

## Main definition
- `traceFormDualSubmodule`: The dual `B`-submodule of `L` under the trace form.
- `FractionalIdeal.dual`: The dual fractional ideal under the trace form.
- `differentIdeal`: The different ideal.

## Main result
- `pow_sub_one_dvd_differentIdeal`:
  If `P ^ e ∣ p.map (algebraMap A B)`, then `P ^ (e - 1) ∣ differentIdeal A B`.
- `conductor_mul_differentIdeal`:
  If `L = K[x]`, with `x` integral over `A`, then `𝔣 * 𝔇 = (f'(x))`
    with `f` being the minimal polynomial of `x`.
- `aeval_derivative_mem_differentIdeal`:
  If `L = K[x]`, with `x` integral over `A`, then `f'(x) ∈ differentIdeal A B`
    with `f` being the minimal polynomial of `x`.

-/
universe u

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

variable (A K) {B} {L : Type u} [CommRing A] [Field K] [CommRing B] [Field L]
variable [Algebra A K] [Algebra B L] [Algebra A B] [Algebra K L] [Algebra A L]
variable [IsScalarTower A K L] [IsScalarTower A B L]
variable [IsDomain A] [IsDomain B]
variable [IsFractionRing A K] [IsIntegralClosure B A L] [IsFractionRing B L]
variable [FiniteDimensional K L] [IsSeparable K L]

open nonZeroDivisors IsLocalization Matrix Algebra

def traceFormDualSubmodule (I : Submodule B L) : Submodule B L where
  carrier := { s | ∀ a ∈ I, Algebra.traceForm K L s a ∈ (algebraMap A K).range }
  add_mem' := fun hx hy a ha ↦
    BilinForm.add_left (B := Algebra.traceForm K L) _ _ _ ▸ add_mem (hx a ha) (hy a ha)
  zero_mem' := fun a _ ↦ BilinForm.zero_left (B := Algebra.traceForm K L) a ▸ zero_mem _
  smul_mem' := fun c {x} hx a ha ↦ by
    rw [Algebra.traceForm_apply, smul_mul_assoc, mul_comm, ← smul_mul_assoc, mul_comm]
    exact hx _ (Submodule.smul_mem _ c ha)

variable {A K}

lemma mem_traceFormDualSubmodule {I : Submodule B L} {x} :
    x ∈ traceFormDualSubmodule A K I ↔
      ∀ a ∈ I, Algebra.traceForm K L x a ∈ (algebraMap A K).range :=
  Iff.rfl

lemma le_traceFormDualSubmodule {I J : Submodule B L} :
  I ≤ traceFormDualSubmodule A K J ↔ ((I * J : Submodule B L).restrictScalars A).map
    ((Algebra.trace K L).restrictScalars A) ≤ 1 := by
  rw [Submodule.map_le_iff_le_comap, Submodule.restrictScalars_mul, Submodule.mul_le]
  simp [SetLike.le_def, traceFormDualSubmodule]

lemma mem_traceFormDualSubmodule_iff_isIntegral [IsIntegrallyClosed A] {I : Submodule B L} {x} :
    x ∈ traceFormDualSubmodule A K I ↔ ∀ a ∈ I, IsIntegral A (Algebra.traceForm K L x a) :=
  forall₂_congr (fun _ _ ↦ IsIntegrallyClosed.isIntegral_iff.symm)

variable (A K)

lemma map_equiv_traceFormDualSubmodule [NoZeroSMulDivisors A B] (I : Submodule B (FractionRing B)) :
    (traceFormDualSubmodule A (FractionRing A) I).map (FractionRing.algEquiv B L) =
      traceFormDualSubmodule A K (I.map (FractionRing.algEquiv B L)) := by
  show Submodule.map (FractionRing.algEquiv B L).toLinearEquiv.toLinearMap _ =
    traceFormDualSubmodule A K (I.map (FractionRing.algEquiv B L).toLinearEquiv.toLinearMap)
  rw [Submodule.map_equiv_eq_comap_symm, Submodule.map_equiv_eq_comap_symm]
  ext x
  simp only [AlgEquiv.toLinearEquiv_symm, AlgEquiv.toLinearEquiv_toLinearMap,
    traceFormDualSubmodule, traceForm_apply, Submodule.mem_comap, AlgEquiv.toLinearMap_apply,
    Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_setOf_eq]
  apply (FractionRing.algEquiv B L).forall_congr
  simp only [AlgEquiv.toEquiv_eq_coe, EquivLike.coe_coe, AlgEquiv.symm_apply_apply]
  letI := ((algebraMap (FractionRing A) (FractionRing B)).comp
    (FractionRing.algEquiv A K).symm.toRingEquiv.toRingHom).toAlgebra
  have : IsScalarTower A K (FractionRing B)
  · apply IsScalarTower.of_algebraMap_eq'
    ext
    rw [RingHom.algebraMap_toAlgebra]
    simp only [AlgEquiv.toRingEquiv_eq_coe, AlgEquiv.coe_ringEquiv, RingEquiv.toRingHom_eq_coe,
      RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply, AlgEquiv.commutes,
      ← IsScalarTower.algebraMap_apply]
  let f' := AlgHom.ofLinearMap (((FractionRing.algEquiv B L).restrictScalars
    A).toLinearMap.extendScalarsOfIsLocalization A⁰ K) (FractionRing.algEquiv B L).map_one
    (FractionRing.algEquiv B L).map_mul
  let f : FractionRing B ≃ₐ[K] L := { FractionRing.algEquiv B L with commutes' := f'.commutes' }
  have hf : ∀ x, f x = FractionRing.algEquiv B L x := fun _ ↦ rfl
  refine fun {y} ↦ (forall_congr' $ fun hy ↦ ?_)
  rw [← trace_eq_of_ringEquiv (C := FractionRing B)
    (FractionRing.algEquiv A K).symm.toRingEquiv rfl,
    ← trace_eq_of_algEquiv f, hf]
  simp only [AlgEquiv.toRingEquiv_eq_coe, _root_.map_mul,
    AlgEquiv.apply_symm_apply, AlgEquiv.coe_ringEquiv]
  rw [← (FractionRing.algEquiv A K).toAlgHom.comp_algebraMap, ← RingHom.map_range,
    AlgEquiv.toAlgHom_eq_coe, AlgEquiv.coe_ringHom_commutes, Subring.mem_map_equiv]
  rfl

variable {A K}
variable [IsIntegrallyClosed A]

lemma isIntegral_discr_mul_of_mem_traceFormDualSubmodule
    (I : Submodule B L) {ι} [DecidableEq ι] [Fintype ι]
    (b : Basis ι K L) (hb : ∀ i, IsIntegral A (b i))
    (a x : L) (ha : a ∈ I) (hx : x ∈ traceFormDualSubmodule A K I) :
    IsIntegral A ((Algebra.discr K b) • a * x) := by
  have hinv : IsUnit (traceMatrix K b).det := by
    simpa [← discr_def] using discr_isUnit_of_basis _ b
  have H := mulVec_cramer (traceMatrix K b) fun i => Algebra.trace K L (x * a * b i)
  rw [← traceMatrix_of_basis_mulVec, ← mulVec_smul, (Matrix.mulVec_injective _ hinv).eq_iff,
    traceMatrix_of_basis_mulVec] at H
  rw [← b.equivFun.symm_apply_apply (_ * _), b.equivFun_symm_apply]
  apply IsIntegral.sum
  intro i _
  rw [smul_mul_assoc, b.equivFun.map_smul, discr_def, mul_comm, ← H, Algebra.smul_def]
  refine RingHom.IsIntegralElem.mul _ ?_ (hb _)
  apply IsIntegral.algebraMap
  rw [cramer_apply]
  apply IsIntegral.det
  intros j k
  rw [updateColumn_apply]
  split
  · rw [mul_assoc]
    rw [mem_traceFormDualSubmodule_iff_isIntegral] at hx
    apply hx
    have ⟨y, hy⟩ := (IsIntegralClosure.isIntegral_iff (A := B)).mp (hb j)
    rw [mul_comm, ← hy, ← Algebra.smul_def]
    exact I.smul_mem _ (ha)
  · exact isIntegral_trace (RingHom.IsIntegralElem.mul _ (hb j) (hb k))

variable (A K)

-- TODO: merge with FractionalIdeal.dual
def FractionalIdeal.dual₂ (I : FractionalIdeal B⁰ L) (hI : I ≠ 0) :
    FractionalIdeal B⁰ L :=
  ⟨traceFormDualSubmodule A K I, by
    classical
    have ⟨s, b, hb⟩ := FiniteDimensional.exists_is_basis_integral A K L
    have := IsIntegralClosure.isFractionRing_of_finite_extension A K L B
    obtain ⟨x, hx, hx'⟩ := exists_ne_zero_mem_isInteger hI
    have ⟨y, hy⟩ := (IsIntegralClosure.isIntegral_iff (A := B)).mp
      (IsIntegral.algebraMap (B := L) (discr_isIntegral K hb))
    refine ⟨y * x, mem_nonZeroDivisors_iff_ne_zero.mpr (mul_ne_zero ?_ hx), ?_⟩
    · rw [← (IsIntegralClosure.algebraMap_injective B A L).ne_iff, hy, RingHom.map_zero,
        ← (algebraMap K L).map_zero, (algebraMap K L).injective.ne_iff]
      exact discr_not_zero_of_basis K b
    · intros z hz
      convert isIntegral_discr_mul_of_mem_traceFormDualSubmodule I b hb _ z hx' hz using 1
      · ext w
        exact (IsIntegralClosure.isIntegral_iff (A := B)).symm
      · rw [Algebra.smul_def, RingHom.map_mul, hy, ← Algebra.smul_def]⟩

variable {A K}

lemma FractionalIdeal.mem_dual₂ {I : FractionalIdeal B⁰ L} {hI : I ≠ 0} {x} :
  x ∈ dual₂ A K I hI ↔ ∀ a ∈ I, Algebra.traceForm K L x a ∈ (algebraMap A K).range := Iff.rfl

lemma FractionalIdeal.dual₂_ne_zero {I : FractionalIdeal B⁰ L} {hI : I ≠ 0} :
    dual₂ A K I hI ≠ 0 := by
  obtain ⟨b, hb, hb'⟩ := I.prop
  suffices algebraMap B L b ∈ dual₂ A K I hI by
    intro e
    rw [e, mem_zero_iff, ← (algebraMap B L).map_zero,
      (IsIntegralClosure.algebraMap_injective B A L).eq_iff] at this
    exact mem_nonZeroDivisors_iff_ne_zero.mp hb this
  intro a ha
  apply IsIntegrallyClosed.isIntegral_iff.mp
  apply isIntegral_trace
  dsimp
  convert hb' a ha using 1
  · ext w
    exact IsIntegralClosure.isIntegral_iff (A := B)
  · exact (Algebra.smul_def _ _).symm

lemma FractionalIdeal.le_dual₂_inv_aux (I J: FractionalIdeal B⁰ L) (hI) (hIJ : I * J ≤ 1) :
    J ≤ dual₂ A K I hI := by
  intro x hx y hy
  apply IsIntegrallyClosed.isIntegral_iff.mp
  apply isIntegral_trace
  rw [IsIntegralClosure.isIntegral_iff (A := B)]
  have ⟨z, _, hz⟩ := hIJ (FractionalIdeal.mul_mem_mul hy hx)
  rw [mul_comm] at hz
  exact ⟨z, hz⟩

variable [IsDedekindDomain B] [IsFractionRing B L]

variable (A K)
variable (B)
variable (L)

lemma pow_sub_one_dvd_differentIdeal_aux
    [IsDedekindDomain A] [NoZeroSMulDivisors A B] [Module.Finite A B]
    {p : Ideal A} [p.IsMaximal] (P : Ideal B) (e : ℕ) (he : 0 < e) (hp : p ≠ ⊥)
    (hP : P ^ e ∣ p.map (algebraMap A B)) : P ^ (e - 1) ∣ differentIdeal A B := by
  obtain ⟨a, ha⟩ := (pow_dvd_pow _ (Nat.sub_le e 1)).trans hP
  have hp' := (Ideal.map_eq_bot_iff_of_injective
    (NoZeroSMulDivisors.algebraMap_injective A B)).not.mpr hp
  have habot : a ≠ ⊥ := fun ha' ↦ hp' (by simpa [ha'] using ha)
  have hPbot : P ≠ ⊥
  · rintro rfl; apply hp'
    rwa [← Ideal.zero_eq_bot, zero_pow he, zero_dvd_iff, Ideal.zero_eq_bot] at hP
  have : p.map (algebraMap A B) ∣ a ^ e
  · obtain ⟨b, hb⟩ := hP
    apply_fun (· ^ e : Ideal B → _) at ha
    apply_fun (· ^ (e - 1) : Ideal B → _) at hb
    simp only [mul_pow, ← pow_mul, mul_comm e] at ha hb
    conv_lhs at ha => rw [← Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr he.ne.symm)]
    rw [pow_add, hb, mul_assoc, mul_right_inj' (pow_ne_zero _ hPbot), pow_one, mul_comm] at ha
    exact ⟨_, ha.symm⟩
  suffices : ∀ x ∈ a, Algebra.intTrace A B x ∈ p
  · have hP : ((P ^ (e - 1) : _)⁻¹ : FractionalIdeal B⁰ L) = a / p.map (algebraMap A B)
    · apply inv_involutive.injective
      simp only [inv_inv, ha, FractionalIdeal.coeIdeal_mul, inv_div, ne_eq,
        FractionalIdeal.coeIdeal_eq_zero, mul_div_assoc]
      rw [div_self (by simpa), mul_one]
    rw [Ideal.dvd_iff_le, differentialIdeal_le_iff (K := K) (L := L) (pow_ne_zero _ hPbot), hP,
      Submodule.map_le_iff_le_comap]
    intro x hx
    rw [Submodule.restrictScalars_mem, FractionalIdeal.mem_coe,
      FractionalIdeal.mem_div_iff_of_nonzero (by simpa using hp')] at hx
    rw [Submodule.mem_comap, LinearMap.coe_restrictScalars, ← FractionalIdeal.coe_one,
      ← div_self (G₀ := FractionalIdeal A⁰ K) (a := p) (by simpa using hp),
      FractionalIdeal.mem_coe, FractionalIdeal.mem_div_iff_of_nonzero (by simpa using hp)]
    simp only [FractionalIdeal.mem_coeIdeal, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂] at hx
    intro y hy'
    obtain ⟨y, hy, rfl : algebraMap A K _ = _⟩ := (FractionalIdeal.mem_coeIdeal _).mp hy'
    obtain ⟨z, hz, hz'⟩ := hx _ (Ideal.mem_map_of_mem _ hy)
    have : Algebra.trace K L (algebraMap B L z) ∈ (p : FractionalIdeal A⁰ K)
    · rw [← Algebra.algebraMap_intTrace (R := A)]
      exact Submodule.mem_map_of_mem (this z hz)
    rwa [mul_comm, ← smul_eq_mul, ← LinearMap.map_smul, Algebra.smul_def, mul_comm,
      ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply A B L, ← hz']
  intros x hx
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← Algebra.trace_quotient_eq_of_isDedekindDomain,
    ← isNilpotent_iff_eq_zero]
  apply Algebra.isNilpotent_trace_of_isNilpotent
  use e
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  apply (Ideal.dvd_iff_le.mp this)
  exact Ideal.pow_mem_pow hx _

lemma pow_sub_one_dvd_differentIdeal
    [IsDedekindDomain A] [NoZeroSMulDivisors A B] [Module.Finite A B]
    [IsSeparable (FractionRing A) (FractionRing B)]
    {p : Ideal A} [p.IsMaximal] (P : Ideal B) (e : ℕ) (hp : p ≠ ⊥)
    (hP : P ^ e ∣ p.map (algebraMap A B)) : P ^ (e - 1) ∣ differentIdeal A B := by
  have : IsIntegralClosure B A (FractionRing B) :=
    isIntegralClosure_of_isIntegrallyClosed _ _ _ (Algebra.IsIntegral.of_finite (R := A) (B := B))
  have : IsLocalization (algebraMapSubmonoid B A⁰) (FractionRing B) :=
    IsIntegralClosure.isLocalization' _ (FractionRing A) _ _
      (isAlgebraic_of_isFractionRing _ _ (Algebra.IsIntegral.of_finite (R := A) (B := B)))
  have : FiniteDimensional (FractionRing A) (FractionRing B) :=
    Module.Finite_of_isLocalization A B _ _ A⁰
  by_cases he : e = 0
  · rw [he, pow_zero]; exact one_dvd _
  rw [← Ne.def, ← Nat.pos_iff_ne_zero] at he
  exact pow_sub_one_dvd_differentIdeal_aux A (FractionRing A) B (FractionRing B) P e he hp hP

lemma traceFormDualSubmodule_eq_span_dualBasis {ι} [Fintype ι] [DecidableEq ι]
    (b : Basis ι K L) :
    traceFormDualSubmodule A K (Submodule.span A (Set.range b)) =
      Submodule.span A (Set.range ((Algebra.traceForm K L).dualBasis
        (traceForm_nondegenerate K L) b)) := by
  apply le_antisymm
  · intros x hx
    rw [← ((Algebra.traceForm K L).dualBasis (traceForm_nondegenerate K L) b).sum_repr x]
    apply sum_mem
    rintro i -
    obtain ⟨a, ha : _ = Algebra.trace K L (x * b i)⟩ :=
      hx (b i) (Submodule.subset_span (Set.mem_range_self _))
    simp only [BilinForm.dualBasis_repr_apply, traceForm_apply, ← ha, algebraMap_smul]
    apply Submodule.smul_mem _ a (Submodule.subset_span (Set.mem_range_self _))
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩ a ha
    rw [← Fintype.range_total (S := A) A] at ha
    obtain ⟨v, rfl⟩ := ha
    rw [Fintype.total_apply, traceForm_apply, Finset.mul_sum, map_sum]
    apply sum_mem
    rintro i -
    rw [mul_comm, smul_mul_assoc, LinearMap.map_smul_of_tower, mul_comm, ← traceForm_apply,
      BilinForm.apply_dualBasis_left, ← SetLike.mem_coe, RingHom.coe_range, ← Algebra.coe_bot]
    refine (⊥ : Subalgebra A K).smul_mem ?_ (v i)
    split; exact one_mem _; exact zero_mem _

open Pointwise Polynomial in
lemma traceFormDualSubmodule_span_adjoin
    (x : L) (hx : Algebra.adjoin K {x} = ⊤) (hAx : IsIntegral A x) :
    traceFormDualSubmodule A K (Subalgebra.toSubmodule (Algebra.adjoin A {x})) =
      (aeval x (derivative <| minpoly K x) : L)⁻¹ •
        (Subalgebra.toSubmodule (Algebra.adjoin A {x})) := by
  classical
  have hKx : IsIntegral K x := Algebra.IsIntegral.of_finite (R := K) (B := L) x
  let pb := (Algebra.adjoin.powerBasis' hKx).map
    ((Subalgebra.equivOfEq _ _ hx).trans (Subalgebra.topEquiv))
  have pbgen : pb.gen = x := by simp
  have hpb : ⇑(BilinForm.dualBasis (traceForm K L) _ pb.basis) = _ :=
    _root_.funext (traceForm_dualBasis_powerBasis_eq pb)
  have : (Subalgebra.toSubmodule (Algebra.adjoin A {x})) = Submodule.span A (Set.range pb.basis)
  · rw [← span_range_natDegree_eq_adjoin _ hAx]
    congr; ext y
    have : natDegree (minpoly A x) = natDegree (minpoly K x)
    · rw [minpoly.isIntegrallyClosed_eq_field_fractions' K hAx, (minpoly.monic hAx).natDegree_map]
    simp only [Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio, Set.mem_range,
      pb.basis_eq_pow, pbgen]
    simp only [PowerBasis.map_dim, adjoin.powerBasis'_dim, this]
    exact ⟨fun ⟨a, b, c⟩ ↦ ⟨⟨a, b⟩, c⟩, fun ⟨⟨a, b⟩, c⟩ ↦ ⟨a, b, c⟩⟩
  clear_value pb
  conv_lhs => rw [this]
  rw [← span_coeff_minpolyDiv hAx, traceFormDualSubmodule_eq_span_dualBasis A K L pb.basis,
    Submodule.smul_span, hpb]
  show _ = Submodule.span A (_ '' _)
  simp only [← Set.range_comp, smul_eq_mul, div_eq_inv_mul, pbgen,
    minpolyDiv_eq_of_isIntegrallyClosed K hAx]
  apply le_antisymm <;> rw [Submodule.span_le]
  · rintro _ ⟨i, rfl⟩; exact Submodule.subset_span ⟨i, rfl⟩
  · rintro _ ⟨i, rfl⟩
    by_cases hi : i < pb.dim
    · exact Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩
    · rw [Function.comp_apply, coeff_eq_zero_of_natDegree_lt, mul_zero]; exact zero_mem _
      rw [← pb.natDegree_minpoly, pbgen, ← natDegree_minpolyDiv_succ hKx,
        ← Nat.succ_eq_add_one] at hi
      exact le_of_not_lt hi

open Polynomial Pointwise in
lemma conductor_mul_differentIdeal [NoZeroSMulDivisors A B]
    (x : B) (hx : Algebra.adjoin K {algebraMap B L x} = ⊤) :
    (conductor A x) * differentIdeal A B = Ideal.span {aeval x (derivative (minpoly A x))} := by
  classical
  have onz := one_ne_zero (α := FractionalIdeal B⁰ L)
  have hAx : IsIntegral A x := IsIntegralClosure.isIntegral A L x
  haveI := IsIntegralClosure.isFractionRing_of_finite_extension A K L B
  apply FractionalIdeal.coeIdeal_injective (K := L)
  simp only [FractionalIdeal.coeIdeal_mul, FractionalIdeal.coeIdeal_span_singleton]
  rw [coeIdeal_differentIdeal A K L B,
    mul_inv_eq_iff_eq_mul₀ (FractionalIdeal.dual_ne_zero A K onz)]
  apply FractionalIdeal.coeToSubmodule_injective
  simp only [FractionalIdeal.coe_coeIdeal, FractionalIdeal.coe_mul,
    FractionalIdeal.coe_spanSingleton, Submodule.span_singleton_mul]
  ext y
  have hne₁ : aeval (algebraMap B L x) (derivative (minpoly K (algebraMap B L x))) ≠ 0
  · exact aeval_derivative_minpoly_ne_zero _ (IsSeparable.separable _ _)
  have : algebraMap B L (aeval x (derivative (minpoly A x))) ≠ 0
  · rwa [minpoly.isIntegrallyClosed_eq_field_fractions K L hAx, derivative_map,
      aeval_map_algebraMap, aeval_algebraMap_apply] at hne₁
  rw [Submodule.mem_smul_iff_inv this, FractionalIdeal.mem_coe, FractionalIdeal.mem_dual onz,
    mem_coeIdeal_conductor]
  have hne₂ : (aeval (algebraMap B L x) (derivative (minpoly K (algebraMap B L x))))⁻¹ ≠ 0
  · rwa [ne_eq, inv_eq_zero]
  have : IsIntegral A (algebraMap B L x) := IsIntegral.map (IsScalarTower.toAlgHom A B L) hAx
  simp_rw [← Subalgebra.mem_toSubmodule, ← Submodule.mul_mem_smul_iff (y := y * _)
    (mem_nonZeroDivisors_of_ne_zero hne₂)]
  rw [← traceFormDualSubmodule_span_adjoin A K L _ hx this]
  simp only [mem_traceFormDualSubmodule, traceForm_apply, Subalgebra.mem_toSubmodule,
    minpoly.isIntegrallyClosed_eq_field_fractions K L hAx,
    derivative_map, aeval_map_algebraMap, aeval_algebraMap_apply, mul_assoc,
    FractionalIdeal.mem_one_iff, forall_exists_index, forall_apply_eq_imp_iff]
  simp_rw [← IsScalarTower.toAlgHom_apply A B L x, ← Algebra.map_adjoin_singleton]
  simp only [Subalgebra.mem_map, IsScalarTower.coe_toAlgHom',
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, ← _root_.map_mul]
  exact ⟨fun H b ↦ (mul_one b) ▸ H b 1 (one_mem _), fun H _ _ _ ↦ H _⟩

open Polynomial Pointwise in
lemma aeval_derivative_mem_differentIdeal [NoZeroSMulDivisors A B]
    (x : B) (hx : Algebra.adjoin K {algebraMap B L x} = ⊤) :
    aeval x (derivative (minpoly A x)) ∈ differentIdeal A B := by
  refine SetLike.le_def.mp ?_ (Ideal.mem_span_singleton_self _)
  rw [← conductor_mul_differentIdeal A K B L x hx]
  exact Ideal.mul_le_left
