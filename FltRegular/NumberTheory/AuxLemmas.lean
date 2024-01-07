import Mathlib.NumberTheory.RamificationInertia
import Mathlib.RingTheory.Trace
import Mathlib.Data.Polynomial.Taylor
import Mathlib.RingTheory.Valuation.ValuationRing

/-!

This file contains lemmas that should go somewhere in a file in mathlib.

-/
open BigOperators UniqueFactorizationMonoid

-- Mathlib/RingTheory/DedekindDomain/Ideal.lean
lemma Ideal.mem_normalizedFactors_iff {R} [CommRing R] [IsDedekindDomain R] [DecidableEq (Ideal R)]
      {p I : Ideal R} (hI : I ≠ ⊥) :
    p ∈ normalizedFactors I ↔ p.IsPrime ∧ I ≤ p := by
  rw [← Ideal.dvd_iff_le]
  by_cases hp : p = 0
  · simp only [hp, zero_not_mem_normalizedFactors, isUnit_zero_iff, one_eq_top, zero_dvd_iff,
      false_iff, not_and]
    exact fun _ ↦ hI
  · rwa [UniqueFactorizationMonoid.mem_normalizedFactors_iff hI, prime_iff_isPrime]

-- Mathlib/RingTheory/Ideal/Operations.lean
lemma Ideal.comap_coe {R S F : Type*} [Semiring R] [Semiring S] [RingHomClass F R S]
  (f : F) (I : Ideal S) : I.comap (f : R →+* S) = I.comap f := rfl

-- Mathlib/RingTheory/IntegralClosure.lean
lemma isIntegralClosure_self {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (hRS : Algebra.IsIntegral R S) : IsIntegralClosure S R S where
  algebraMap_injective' := Function.injective_id
  isIntegral_iff := fun {x} ↦ ⟨fun _ ↦ ⟨x, rfl⟩, fun _ ↦ hRS _⟩

-- Mathlib/Algebra/Group/Units.lean
lemma isUnit_iff_eq_one {M : Type*} [Monoid M] [Unique Mˣ] {x : M} : IsUnit x ↔ x = 1 :=
  ⟨fun h ↦ congr_arg Units.val (Subsingleton.elim (h.unit) 1), fun h ↦ h ▸ isUnit_one⟩

-- Mathlib/NumberTheory/RamificationInertia.lean
section RamificationInertia

variable {R S₁ S₂} [CommRing R] [CommRing S₁] [CommRing S₂] [Algebra R S₁] [Algebra R S₂]

lemma Ideal.ramificationIdx_comap_eq (e : S₁ ≃ₐ[R] S₂) (p : Ideal R) (P : Ideal S₂) :
    Ideal.ramificationIdx (algebraMap R S₁) p (P.comap e) =
      Ideal.ramificationIdx (algebraMap R S₂) p P := by
  show sSup _ = sSup _
  congr
  ext n
  simp only [Set.mem_setOf_eq, Ideal.map_le_iff_le_comap]
  rw [← Ideal.comap_coe e, ← e.toRingEquiv_toRingHom, Ideal.comap_coe,
    ← RingEquiv.symm_symm (e : S₁ ≃+* S₂), ← Ideal.map_comap_of_equiv, ← Ideal.map_pow,
    Ideal.map_comap_of_equiv, ← Ideal.comap_coe (RingEquiv.symm _), Ideal.comap_comap,
    RingEquiv.symm_symm, e.toRingEquiv_toRingHom, ← e.toAlgHom_toRingHom, AlgHom.comp_algebraMap]

lemma Ideal.inertiaDeg_comap_eq (e : S₁ ≃ₐ[R] S₂) (p : Ideal R) (P : Ideal S₂) [p.IsMaximal] :
    Ideal.inertiaDeg (algebraMap R S₁) p (P.comap e) =
      Ideal.inertiaDeg (algebraMap R S₂) p P := by
  delta Ideal.inertiaDeg
  have : (P.comap e).comap (algebraMap R S₁) = p ↔ P.comap (algebraMap R S₂) = p
  · rw [← Ideal.comap_coe e, Ideal.comap_comap, ← e.toAlgHom_toRingHom, AlgHom.comp_algebraMap]
  split
  swap
  · rw [dif_neg]; rwa [← this]
  rw [dif_pos (this.mp ‹_›)]
  apply (config := {allowSynthFailures := true }) LinearEquiv.finrank_eq
  have E := quotientEquivAlg (R₁ := R) (P.comap e) P e
    (Ideal.map_comap_of_surjective _ e.surjective P).symm
  apply (config := {allowSynthFailures := true }) LinearEquiv.mk
  case toLinearMap =>
    apply (config := {allowSynthFailures := true }) LinearMap.mk
    swap
    · exact E.toLinearMap.toAddHom
    · intro r x
      show E (_ * _) = _ * (E x)
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
      simp only [Quotient.mk_comp_algebraMap, Quotient.lift_mk, _root_.map_mul, AlgEquiv.commutes,
        RingHomCompTriple.comp_apply]
  exact E.left_inv
  exact E.right_inv

end RamificationInertia

open Polynomial IntermediateField

-- Mathlib/FieldTheory/Adjoin.lean
theorem IntermediateField.adjoin_adjoinRoot_root_eq_top {K : Type*} [Field K]
    (p : K[X]) [Fact (Irreducible p)] : K⟮AdjoinRoot.root p⟯ = ⊤ :=
  (IntermediateField.eq_adjoin_of_eq_algebra_adjoin K _ ⊤
    (AdjoinRoot.adjoinRoot_eq_top (f := p)).symm).symm

-- Mathlib/Data/Polynomial/Degree/Lemmas.lean
-- maybe generalize to `of_natDegree_le`?
theorem Polynomial.associated_of_dvd_of_natDegree_eq {K : Type*} [Field K]
    {P₁ P₂ : K[X]} (h₁ : P₁ ∣ P₂) (h₂ : P₁.natDegree = P₂.natDegree) (hP₂ : P₂ ≠ 0) :
    Associated P₁ P₂ := by
  obtain ⟨u, rfl⟩ := h₁
  rw [mul_ne_zero_iff] at hP₂
  rw [natDegree_mul hP₂.1 hP₂.2, self_eq_add_right, natDegree_eq_zero_iff_degree_le_zero,
    le_iff_eq_or_lt, ← not_le, zero_le_degree_iff, not_ne_iff, or_iff_left hP₂.2,
    ← isUnit_iff_degree_eq_zero] at h₂
  exact associated_mul_unit_right P₁ u h₂

-- Mathlib/Data/Polynomial/Degree/Lemmas.lean
-- maybe generalize to `of_degree_le`?
theorem Polynomial.associated_of_dvd_of_degree_eq {K : Type*} [Field K]
    {P₁ P₂ : K[X]} (h₁ : P₁ ∣ P₂) (h₂ : P₁.degree = P₂.degree) :
    Associated P₁ P₂ := by
  by_cases h : P₂ = 0
  · subst h
    rw [degree_zero, degree_eq_bot] at h₂
    exact h₂ ▸ Associated.refl _
  · exact Polynomial.associated_of_dvd_of_natDegree_eq h₁ (natDegree_eq_of_degree_eq h₂) h

-- Mathlib/Algebra/GroupWithZero/Power.lean
theorem mem_range_pow_of_coprime_of_pow_mem_range_pow {G₀} [CommGroupWithZero G₀] {m n : ℕ}
    (hmn : m.Coprime n) (a : G₀) (ha : a ^ m ∈ Set.range (· ^ n : G₀ → G₀)) :
    a ∈ Set.range (· ^ n : G₀ → G₀) := by
  obtain ⟨k, l, e⟩ := Nat.isCoprime_iff_coprime.mpr hmn
  by_cases hn : n = 0
  · simp only [hn, Nat.coprime_zero_right] at hmn
    rwa [hmn, pow_one] at ha
  by_cases ha' : a = 0
  · exact ⟨0, by simpa only [ha', zero_pow_eq_zero, pos_iff_ne_zero]⟩
  obtain ⟨x, hx⟩ := ha
  use x ^ k * a ^ l
  conv_rhs => rw [← zpow_one a, ← e]
  simp only [← zpow_ofNat, mul_zpow, zpow_add₀ ha', ← zpow_mul, mul_comm k]
  rw [zpow_mul, zpow_ofNat, zpow_mul a m, zpow_ofNat, ← hx]

open nonZeroDivisors
section

variable (R A K : Type*) [CommRing R] [CommRing A] [Field K] [Algebra A K] [IsFractionRing A K]
variable [IsDomain A]
variable (L : Type*) [Field L] (C : Type*) [CommRing C]
variable [Algebra K L] [Algebra A L] [IsScalarTower A K L]
variable [Algebra C L] [IsIntegralClosure C A L] [Algebra A C] [IsScalarTower A C L]

-- Mathlib/RingTheory/DedekindDomain/IntegralClosure.lean
-- generalized from `IsIntegralClosure.isLocalization`
open Algebra nonZeroDivisors Polynomial
theorem IsIntegralClosure.isLocalization' (ha : Algebra.IsAlgebraic K L) [NoZeroSMulDivisors A L] :
    IsLocalization (Algebra.algebraMapSubmonoid C A⁰) L := by
  haveI : IsDomain C :=
    (IsIntegralClosure.equiv A C L (integralClosure A L)).toMulEquiv.isDomain (integralClosure A L)
  haveI : NoZeroSMulDivisors A C := IsIntegralClosure.noZeroSMulDivisors A L
  refine' ⟨_, fun z => _, fun {x y} => fun h => ⟨1, _⟩⟩
  · rintro ⟨_, x, hx, rfl⟩
    rw [isUnit_iff_ne_zero, map_ne_zero_iff _ (IsIntegralClosure.algebraMap_injective C A L),
      Subtype.coe_mk, map_ne_zero_iff _ (NoZeroSMulDivisors.algebraMap_injective A C)]
    exact mem_nonZeroDivisors_iff_ne_zero.mp hx
  · obtain ⟨m, hm⟩ :=
      IsIntegral.exists_multiple_integral_of_isLocalization A⁰ z
        (isAlgebraic_iff_isIntegral.mp <| ha z)
    obtain ⟨x, hx⟩ : ∃ x, algebraMap C L x = m • z := IsIntegralClosure.isIntegral_iff.mp hm
    refine' ⟨⟨x, algebraMap A C m, m, SetLike.coe_mem m, rfl⟩, _⟩
    rw [Subtype.coe_mk, ← IsScalarTower.algebraMap_apply, hx, mul_comm, Submonoid.smul_def,
      smul_def]
  · simp only [IsIntegralClosure.algebraMap_injective C A L h]
end

-- Mathlib/RingTheory/Algebraic.lean
-- or Mathlib/RingTheory/LocalProperties.lean
open Polynomial in
lemma isAlgebraic_of_isLocalization {R} [CommRing R] (M : Submonoid R) (S) [CommRing S]
    [Nontrivial R] [Algebra R S] [IsLocalization M S] : Algebra.IsAlgebraic R S := by
  intro x
  obtain ⟨x, s, rfl⟩ := IsLocalization.mk'_surjective M x
  by_cases hs : (s : R) = 0
  · have := IsLocalization.mk'_spec S x s
    rw [hs, map_zero, mul_zero] at this
    exact ⟨X, X_ne_zero, by simp [IsLocalization.mk'_eq_mul_mk'_one x, ← this]⟩
  refine ⟨s • X - C x, ?_, ?_⟩
  · intro e; apply hs
    simpa only [coeff_sub, coeff_smul, coeff_X_one, coeff_C_succ, sub_zero, coeff_zero,
      ← Algebra.algebraMap_eq_smul_one, Submonoid.smul_def,
      Algebra.id.map_eq_id, RingHom.id_apply] using congr_arg (Polynomial.coeff · 1) e
  · simp only [map_sub, Algebra.smul_def, Submonoid.smul_def,
      map_mul, AlgHom.commutes, aeval_X, IsLocalization.mk'_spec', aeval_C, sub_self]

-- Mathlib/RingTheory/Localization/Basic.lean
instance {R} [CommRing R] (M : Submonoid R) (S) [CommRing S] [Algebra R S] [IsLocalization M S]
    (s : M) : Invertible (IsLocalization.mk' S (1 : R) s) where
  invOf := algebraMap R S s
  invOf_mul_self := by simp
  mul_invOf_self := by simp

-- Mathlib/RingTheory/Algebraic.lean
-- or Mathlib/RingTheory/LocalProperties.lean
open Polynomial nonZeroDivisors in
lemma isAlgebraic_of_isFractionRing {R S} (K L) [CommRing R] [CommRing S] [Field K] [Field L]
  [Algebra R S] [Algebra R K] [Algebra R L] [Algebra S L] [Algebra K L] [IsScalarTower R S L]
  [IsScalarTower R K L] [IsFractionRing R K] [IsFractionRing S L]
    (h : Algebra.IsIntegral R S) : Algebra.IsAlgebraic K L := by
  intro x
  obtain ⟨x, s, rfl⟩ := IsLocalization.mk'_surjective S⁰ x
  rw [isAlgebraic_iff_isIntegral, IsLocalization.mk'_eq_mul_mk'_one]
  apply RingHom.IsIntegralElem.mul
  · apply IsIntegral.tower_top (R := R)
    apply IsIntegral.map (IsScalarTower.toAlgHom R S L)
    exact h x
  · show IsIntegral _ _
    rw [← isAlgebraic_iff_isIntegral, ← IsAlgebraic.invOf_iff, isAlgebraic_iff_isIntegral]
    apply IsIntegral.tower_top (R := R)
    apply IsIntegral.map (IsScalarTower.toAlgHom R S L)
    exact h s

-- Mathlib/RingTheory/IntegralClosure.lean
lemma isIntegralClosure_of_isIntegrallyClosed (R S K) [CommRing R] [CommRing S] [CommRing K]
    [Algebra R S] [Algebra S K] [Algebra R K] [IsScalarTower R S K] [IsFractionRing S K]
    [Nontrivial K] [IsIntegrallyClosed S] (hRS : Algebra.IsIntegral R S) :
    IsIntegralClosure S R K := by
  refine ⟨IsLocalization.injective _ le_rfl, fun {x} ↦
    ⟨fun hx ↦ IsIntegralClosure.isIntegral_iff.mp (IsIntegral.tower_top (A := S) hx), ?_⟩⟩
  rintro ⟨y, rfl⟩
  exact IsIntegral.map (IsScalarTower.toAlgHom R S K) (hRS y)

-- Mathlib/RingTheory/IntegralClosure.lean
-- or Mathlib/RingTheory/LocalProperties.lean
lemma isIntegrallyClosed_of_isLocalization {R} [CommRing R] [IsIntegrallyClosed R] [IsDomain R]
    (M : Submonoid R) (hM : M ≤ R⁰) (S) [CommRing S] [Algebra R S] [IsLocalization M S] :
    IsIntegrallyClosed S := by
  let K := FractionRing R
  let g : S →+* K := IsLocalization.map _ (T := R⁰) (RingHom.id R) hM
  letI := g.toAlgebra
  have : IsScalarTower R S K := IsScalarTower.of_algebraMap_eq'
    (by rw [RingHom.algebraMap_toAlgebra, IsLocalization.map_comp, RingHomCompTriple.comp_eq])
  have := IsFractionRing.isFractionRing_of_isDomain_of_isLocalization M S K
  refine (isIntegrallyClosed_iff_isIntegralClosure (K := K)).mpr
    ⟨IsFractionRing.injective _ _, fun {x} ↦ ⟨?_, fun e ↦ e.choose_spec ▸ isIntegral_algebraMap⟩⟩
  intro hx
  obtain ⟨⟨y, y_mem⟩, hy⟩ := hx.exists_multiple_integral_of_isLocalization M _
  obtain ⟨z, hz⟩ := (isIntegrallyClosed_iff _).mp ‹_› hy
  refine' ⟨IsLocalization.mk' S z ⟨y, y_mem⟩, (IsLocalization.lift_mk'_spec _ _ _ _).mpr _⟩
  rw [RingHom.comp_id, hz, ← Algebra.smul_def]
  rfl

-- Mathlib/RingTheory/LocalProperties.lean
open Polynomial nonZeroDivisors in
lemma IsIntegral_of_isLocalization (R S Rₚ Sₚ) [CommRing R] [CommRing S] [CommRing Rₚ]
    [CommRing Sₚ] [Algebra R S] [Algebra R Rₚ] [Algebra R Sₚ] [Algebra S Sₚ] [Algebra Rₚ Sₚ]
    [IsScalarTower R S Sₚ] [IsScalarTower R Rₚ Sₚ] (M : Submonoid R) [IsLocalization M Rₚ]
    [IsLocalization (Algebra.algebraMapSubmonoid S M) Sₚ] (hRS : Algebra.IsIntegral R S) :
    Algebra.IsIntegral Rₚ Sₚ := by
  classical
  have : algebraMap Rₚ Sₚ = IsLocalization.map (T := Algebra.algebraMapSubmonoid S M) Sₚ
    (algebraMap R S) (Submonoid.le_comap_map M)
  · apply IsLocalization.ringHom_ext M
    simp only [IsLocalization.map_comp, ← IsScalarTower.algebraMap_eq]
  intros x
  obtain ⟨x, ⟨_, t, ht, rfl⟩, rfl⟩ := IsLocalization.mk'_surjective
    (Algebra.algebraMapSubmonoid S M) x
  rw [IsLocalization.mk'_eq_mul_mk'_one]
  apply RingHom.IsIntegralElem.mul
  · exact IsIntegral.tower_top (IsIntegral.map (IsScalarTower.toAlgHom R S Sₚ) (hRS x))
  · show IsIntegral _ _
    convert isIntegral_algebraMap (x := IsLocalization.mk' Rₚ 1 ⟨t, ht⟩)
    rw [this, IsLocalization.map_mk', _root_.map_one]



-- Mathlib/RingTheory/Polynomial/ScaleRoots.lean (this section is not needed anymore)
section scaleRoots

open Polynomial in
lemma Polynomial.derivative_scaleRoots {R} [CommRing R] (p : R[X]) (r) :
    derivative (p.scaleRoots r) = r ^ (natDegree p - (natDegree (derivative p) + 1)) •
      ((derivative p).scaleRoots r) := by
  by_cases hp : natDegree p = 0
  · rw [hp, Nat.zero_sub, pow_zero, one_smul]
    rw [natDegree_eq_zero_iff_degree_le_zero, degree_le_zero_iff] at hp
    rw [hp]; simp only [scaleRoots_C, derivative_C, zero_scaleRoots]
  ext i
  simp only [coeff_smul, coeff_scaleRoots, ge_iff_le, smul_eq_mul, coeff_derivative,
    mul_comm (r ^ (natDegree p - _)), mul_assoc, ← pow_add]
  simp_rw [← mul_assoc, ← coeff_derivative]
  cases lt_or_le (natDegree (derivative p)) i with
  | inl h => simp only [coeff_eq_zero_of_natDegree_lt h, zero_mul]
  | inr h =>
    congr
    have h' := natDegree_derivative_lt hp
    zify
    rw [Int.ofNat_sub h', Int.ofNat_sub h, Int.ofNat_sub (h.trans_lt h')]
    simp only [Nat.cast_succ]
    abel

open Polynomial in
lemma Polynomial.Separable.scaleRoots {R} [CommRing R] {p : R[X]}
    (hp : Polynomial.Separable p) (r) (hr : IsUnit r) :
    Polynomial.Separable (p.scaleRoots r) := by
  delta Polynomial.Separable at hp ⊢
  rw [Polynomial.derivative_scaleRoots, Algebra.smul_def]
  refine (isCoprime_mul_unit_left_right ((hr.pow _).map _) _ _).mpr ?_
  exact Polynomial.isCoprime_scaleRoots _ _ _ hr hp

open Polynomial nonZeroDivisors in
lemma IsSeparable_of_isLocalization (R S Rₚ Sₚ) [CommRing R] [CommRing S] [Field Rₚ]
    [CommRing Sₚ] [Algebra R S] [Algebra R Rₚ] [Algebra R Sₚ] [Algebra S Sₚ] [Algebra Rₚ Sₚ]
    [IsScalarTower R S Sₚ] [IsScalarTower R Rₚ Sₚ] (M : Submonoid R) [IsLocalization M Rₚ]
    [IsLocalization (Algebra.algebraMapSubmonoid S M) Sₚ] [hRS : IsSeparable R S] :
    IsSeparable Rₚ Sₚ := by
  have : algebraMap Rₚ Sₚ = IsLocalization.map (T := Algebra.algebraMapSubmonoid S M) Sₚ
    (algebraMap R S) (Submonoid.le_comap_map M)
  · apply IsLocalization.ringHom_ext M
    simp only [IsLocalization.map_comp, ← IsScalarTower.algebraMap_eq]
  refine ⟨fun x ↦ ?_⟩
  obtain ⟨x, s, rfl⟩ := IsLocalization.mk'_surjective (Algebra.algebraMapSubmonoid S M) x
  obtain ⟨t, ht, e⟩ := s.prop
  let P := ((minpoly R x).map (algebraMap R Rₚ)).scaleRoots (IsLocalization.mk' _ 1 ⟨t, ht⟩)
  refine Separable.of_dvd ?_ (minpoly.dvd _ (p := P) ?_)
  · apply (IsSeparable.separable R x).map.scaleRoots
    exact isUnit_of_invertible _
  · rw [aeval_def]
    convert scaleRoots_eval₂_eq_zero _ (r := algebraMap S Sₚ x) _
    · rw [this, IsLocalization.map_mk', _root_.map_one, IsLocalization.mk'_eq_mul_mk'_one,
        mul_comm]
      congr; ext; exact e.symm
    · rw [← aeval_def, ← map_aeval_eq_aeval_map, minpoly.aeval, map_zero]
      rw [← IsScalarTower.algebraMap_eq, ← IsScalarTower.algebraMap_eq]

end scaleRoots

-- Mathlib/RingTheory/LocalProperties.lean
-- Generalized universe from `localization_finite`
open Polynomial nonZeroDivisors in
lemma Module.Finite_of_isLocalization (R S Rₚ Sₚ) [CommRing R] [CommRing S] [CommRing Rₚ]
    [CommRing Sₚ] [Algebra R S] [Algebra R Rₚ] [Algebra R Sₚ] [Algebra S Sₚ] [Algebra Rₚ Sₚ]
    [IsScalarTower R S Sₚ] [IsScalarTower R Rₚ Sₚ] (M : Submonoid R) [IsLocalization M Rₚ]
    [IsLocalization (Algebra.algebraMapSubmonoid S M) Sₚ] [hRS : Module.Finite R S] :
    Module.Finite Rₚ Sₚ := by
  classical
  have : algebraMap Rₚ Sₚ = IsLocalization.map (T := Algebra.algebraMapSubmonoid S M) Sₚ
    (algebraMap R S) (Submonoid.le_comap_map M)
  · apply IsLocalization.ringHom_ext M
    simp only [IsLocalization.map_comp, ← IsScalarTower.algebraMap_eq]
  -- We claim that if `S` is generated by `T` as an `R`-module,
  -- then `S'` is generated by `T` as an `R'`-module.
  obtain ⟨T, hT⟩ := hRS
  use T.image (algebraMap S Sₚ)
  rw [eq_top_iff]
  rintro x -
  -- By the hypotheses, for each `x : S'`, we have `x = y / (f r)` for some `y : S` and `r : M`.
  -- Since `S` is generated by `T`, the image of `y` should fall in the span of the image of `T`.
  obtain ⟨y, ⟨_, ⟨r, hr, rfl⟩⟩, rfl⟩ :=
    IsLocalization.mk'_surjective (Algebra.algebraMapSubmonoid S M) x
  rw [IsLocalization.mk'_eq_mul_mk'_one, mul_comm, Finset.coe_image]
  have hy : y ∈ Submodule.span R ↑T := by rw [hT]; trivial
  replace hy : algebraMap S Sₚ y ∈ Submodule.map (IsScalarTower.toAlgHom R S Sₚ).toLinearMap
    (Submodule.span R (T : Set S)) := Submodule.mem_map_of_mem hy
  rw [Submodule.map_span (IsScalarTower.toAlgHom R S Sₚ).toLinearMap T] at hy
  have H : Submodule.span R (algebraMap S Sₚ '' T) ≤
      (Submodule.span Rₚ (algebraMap S Sₚ '' T)).restrictScalars R := by
    rw [Submodule.span_le]; exact Submodule.subset_span
  -- Now, since `y ∈ span T`, and `(f r)⁻¹ ∈ R'`, `x / (f r)` is in `span T` as well.
  convert (Submodule.span Rₚ (algebraMap S Sₚ '' T)).smul_mem
    (IsLocalization.mk' Rₚ (1 : R) ⟨r, hr⟩) (H hy) using 1
  rw [Algebra.smul_def, this, IsLocalization.map_mk', map_one]

-- Mathlib/RingTheory/Trace.lean
universe u v in
lemma Algebra.isNilpotent_trace_of_isNilpotent {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [Algebra R S] (x : S) (hx : IsNilpotent x) : IsNilpotent (Algebra.trace R S x) := by
  classical
  by_cases hS : ∃ s : Finset S, Nonempty (Basis s R S)
  · obtain ⟨s, ⟨b⟩⟩ := hS
    have := Module.Finite.of_basis b
    have := (Module.free_def.{u, v, v} R S).mpr ⟨s, ⟨b⟩⟩
    apply LinearMap.isNilpotent_trace_of_isNilpotent (hx.map (lmul R S))
  · rw [trace_eq_zero_of_not_exists_basis _ hS, LinearMap.zero_apply]
    exact IsNilpotent.zero

-- Mathlib/LinearAlgebra/Dimension.lean
lemma FiniteDimensional.finrank_le_of_span_eq_top
    {R M} [Ring R] [StrongRankCondition R] [AddCommGroup M] [Module R M]
    [Module.Free R M] {ι} [Fintype ι] (v : ι → M) (hv : Submodule.span R (Set.range v) = ⊤) :
    finrank R M ≤ Fintype.card ι := by
  classical
  apply finrank_le_of_rank_le
  rw [Module.Free.rank_eq_card_chooseBasisIndex]
  exact (linearIndependent_le_span _ (Module.Free.chooseBasis R M).linearIndependent _ hv).trans
    (Cardinal.natCast_le.mpr <| Fintype.card_range_le _)

-- Mathlib/Data/Polynomial/Taylor.lean
@[simps] noncomputable
def Polynomial.taylorAlgEquiv {R} [CommRing R] (r : R) : R[X] ≃ₐ[R] R[X] where
  __ := taylorAlgHom r
  invFun := fun p ↦ taylor (-r) p
  left_inv := fun p ↦ by simp [taylor_taylor]
  right_inv := fun p ↦ by simp [taylor_taylor]

-- Mathlib/Data/Polynomial/Taylor.lean
lemma Polynomial.irreducible_taylor_iff {R} [CommRing R] {r} {p : R[X]} :
    Irreducible (taylor r p) ↔ Irreducible p := by
  refine ⟨fun H ↦ of_irreducible_map (taylorAlgEquiv r).toRingEquiv H, fun H ↦ ?_⟩
  apply of_irreducible_map ((taylorAlgEquiv r).symm.toRingEquiv : R[X] →+* R[X])
  simpa only [AlgEquiv.toRingEquiv_eq_coe, RingHom.coe_coe, AlgEquiv.coe_ringEquiv,
    taylorAlgEquiv_symm_apply, taylor_taylor, add_left_neg, taylor_zero', LinearMap.id_coe, id_eq]

-- Mathlib/FieldTheory/Separable.lean
-- Generalizes (and should follow) `Separable.map`
open Polynomial in
attribute [local instance] Ideal.Quotient.field in
lemma Polynomial.separable_map' {R S} [Field R] [CommRing S] [Nontrivial S] (f : R →+* S) (p : R[X]) :
    (p.map f).Separable ↔ p.Separable :=  by
  refine ⟨fun H ↦ ?_, fun H ↦ H.map⟩
  obtain ⟨m, hm⟩ := Ideal.exists_maximal S
  have := Separable.map H (f := Ideal.Quotient.mk m)
  rwa [map_map, separable_map] at this

-- Somewhere in polynomial.
lemma Polynomial.dvd_C_mul_X_sub_one_pow_add_one
    {R} [CommRing R] {p : ℕ} (hpri : p.Prime) (hp : p ≠ 2) (a r : R)
    (h₁ : r ∣ a ^ p) (h₂ : r ∣ p * a) : C r ∣ (C a * X - 1) ^ p + 1 := by
  rw [sub_eq_add_neg, add_pow_prime_eq hpri, (hpri.odd_of_ne_two hp).neg_pow, one_pow,
    mul_pow, ← C.map_pow, add_comm, add_comm (_ * _), ← add_assoc, ← add_assoc,
    add_right_neg, zero_add]
  refine dvd_add (dvd_mul_of_dvd_left (_root_.map_dvd C h₁) _) ((_root_.map_dvd C h₂).trans ?_)
  rw [map_mul, map_natCast]
  exact mul_dvd_mul_left _ (Finset.dvd_sum (fun x hx ↦ dvd_mul_of_dvd_left
    (dvd_mul_of_dvd_left (dvd_pow (dvd_mul_right _ _) (Finset.mem_Ioo.mp hx).1.ne.symm) _) _))
