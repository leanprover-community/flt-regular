import Mathlib.NumberTheory.RamificationInertia
import Mathlib.FieldTheory.Galois
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.Norm
import Mathlib.Data.Set.Card
import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.RingTheory.DedekindDomain.Ideal
import Mathlib.RingTheory.Discriminant
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.NumberTheory.RamificationInertia
import Mathlib.NumberTheory.KummerDedekind
import Mathlib.Data.Polynomial.Taylor
import Mathlib.RingTheory.Localization.NormTrace
import Mathlib.NumberTheory.NumberField.Norm

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

-- Mathlib/Algebra/Algebra/Hom.lean
lemma AlgEquiv.toAlgHom_toRingHom {R A₁ A₂} [CommSemiring R] [Semiring A₁] [Semiring A₂]
    [Algebra R A₁] [Algebra R A₂] (e : A₁ ≃ₐ[R] A₂) : ((e : A₁ →ₐ[R] A₂) : A₁ →+* A₂) = e :=
  rfl

-- Mathlib/RingTheory/IntegralClosure.lean
lemma isIntegralClosure_self {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (hRS : Algebra.IsIntegral R S) : IsIntegralClosure S R S where
  algebraMap_injective' := Function.injective_id
  isIntegral_iff := fun {x} ↦ ⟨fun _ ↦ ⟨x, rfl⟩, fun _ ↦ hRS _⟩

-- Mathlib/Algebra/Group/Units.lean
lemma isUnit_iff_eq_one {M : Type*} [Monoid M] [Unique Mˣ] {x : M} : IsUnit x ↔ x = 1 :=
  ⟨fun h ↦ congr_arg Units.val (Subsingleton.elim (h.unit) 1), fun h ↦ h ▸ isUnit_one⟩

-- Mathlib/RingTheory/Ideal/Over.lean
lemma Ideal.exists_ideal_over_prime {R S : Type*} [CommSemiring R] [CommRing S] [Algebra R S]
  [NoZeroSMulDivisors R S]
  (I : Ideal S) (p : Ideal R) [p.IsPrime] (hI : I.comap (algebraMap R S) ≤ p) :
    ∃ P ≥ I, P.IsPrime ∧ P.comap (algebraMap R S) ≤ p := by
  let Sₚ := Localization (Algebra.algebraMapSubmonoid S p.primeCompl)
  let Iₚ := I.map (algebraMap S Sₚ)
  have H : Function.Injective (algebraMap S Sₚ)
  · apply IsLocalization.injective (M := Algebra.algebraMapSubmonoid S p.primeCompl)
    rintro _ ⟨x, hx : x ∉ p, rfl⟩ s hs
    rw [mul_comm, ← Algebra.smul_def] at hs
    refine (NoZeroSMulDivisors.eq_zero_or_eq_zero_of_smul_eq_zero hs).resolve_left ?_
    rintro rfl
    exact hx p.zero_mem
  have hI' : Disjoint (Algebra.algebraMapSubmonoid S p.primeCompl : Set S) I
  · rw [Set.disjoint_iff]
    rintro _ ⟨⟨x, hx : x ∉ p, rfl⟩, hx'⟩
    exact (hx (hI hx')).elim
  have : Iₚ ≠ ⊤
  · rw [Ne.def, Ideal.eq_top_iff_one, IsLocalization.mem_map_algebraMap_iff
      (Algebra.algebraMapSubmonoid S p.primeCompl) Sₚ, not_exists]
    simp only [one_mul, H.eq_iff]
    exact fun H ↦ hI'.ne_of_mem H.2.2 H.1.2
  obtain ⟨M, hM, hM'⟩ := Ideal.exists_le_maximal _ this
  refine ⟨_, Ideal.map_le_iff_le_comap.mp hM', hM.isPrime.comap _, ?_⟩
  intro x hx
  by_contra hx'
  exact Set.disjoint_left.mp ((IsLocalization.isPrime_iff_isPrime_disjoint
    (Algebra.algebraMapSubmonoid S p.primeCompl) Sₚ M).mp hM.isPrime).2 ⟨_, hx', rfl⟩ hx

-- Mathlib/Algebra/Algebra/Hom.lean
def algHomUnitsEquiv (R S : Type*) [CommSemiring R] [Semiring S] [Algebra R S] :
    (S →ₐ[R] S)ˣ ≃* (S ≃ₐ[R] S) where
  toFun := fun f ↦
    { (f : S →ₐ[R] S) with
      invFun := ↑(f⁻¹)
      left_inv := (fun x ↦ show (↑(f⁻¹ * f) : S →ₐ[R] S) x = x by rw [inv_mul_self]; rfl)
      right_inv := (fun x ↦ show (↑(f * f⁻¹) : S →ₐ[R] S) x = x by rw [mul_inv_self]; rfl) }
  invFun := fun f ↦ ⟨f, f.symm, f.comp_symm, f.symm_comp⟩
  left_inv := fun _ ↦ rfl
  right_inv := fun _ ↦ rfl
  map_mul' := fun _ _ ↦ rfl


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

-- Mathlib/Algebra/Hom/Units.lean
lemma Units.map_injective {M N} [Monoid M] [Monoid N] {f : M →* N} (hf : Function.Injective f) :
    Function.Injective (Units.map f) := fun _ _ e => ext (hf (congr_arg val e))

-- Mathlib/RingTheory/RootsOfUnity/Basic.lean
lemma IsPrimitiveRoot.isUnit_unit' {K} [Field K] {ζ : K} {n} (hn) (hζ : IsPrimitiveRoot ζ n) :
    IsPrimitiveRoot (hζ.isUnit hn).unit' n := coe_units_iff.mp hζ

-- Mathlib/RingTheory/RootsOfUnity/Basic.lean
noncomputable
def rootsOfUnity_equiv_of_primitiveRoots {K L} [Field K] [Field L]
    (f : K →+* L) (n : ℕ+) (hζ : (primitiveRoots n K).Nonempty) :
    (rootsOfUnity n K) ≃* rootsOfUnity n L := by
  haveI H : Function.Injective (Units.map f : Kˣ →* Lˣ) := Units.map_injective f.injective
  refine (Subgroup.equivMapOfInjective _ _ H).trans (MulEquiv.subgroupCongr ?_)
  letI : CommMonoid Lˣ := inferInstance
  have ⟨_, hζ⟩ := hζ
  rw [mem_primitiveRoots (k := n) n.2] at hζ
  replace hζ := hζ.isUnit_unit' n.2
  rw [← hζ.zpowers_eq, ← (hζ.map_of_injective H).zpowers_eq, MonoidHom.map_zpowers]

-- Mathlib/RingTheory/RootsOfUnity/Basic.lean
lemma rootsOfUnity_equiv_of_primitiveRoots_apply {K L} [Field K] [Field L]
    (f : K →+* L) (n : ℕ+) (hζ : (primitiveRoots n K).Nonempty) (η) :
    (rootsOfUnity_equiv_of_primitiveRoots f n hζ η : Lˣ) = f (η : Kˣ) := rfl

-- Mathlib/RingTheory/RootsOfUnity/Basic.lean
lemma rootsOfUnity_equiv_of_primitiveRoots_symm_apply {K L} [Field K] [Field L]
    (f : K →+* L) (n : ℕ+) (hζ : (primitiveRoots n K).Nonempty) (η) :
    f ((rootsOfUnity_equiv_of_primitiveRoots f n hζ).symm η : Kˣ) = (η : Lˣ) := by
  obtain ⟨ε, rfl⟩ := (rootsOfUnity_equiv_of_primitiveRoots f n hζ).surjective η
  rw [MulEquiv.symm_apply_apply, rootsOfUnity_equiv_of_primitiveRoots_apply]

-- Mathlib/Algebra/Algebra/Hom.lean
@[simps]
def AlgEquiv.toLinearMapHom (K L) [CommSemiring K] [Semiring L] [Algebra K L] :
    (L ≃ₐ[K] L) →* L →ₗ[K] L where
  toFun := AlgEquiv.toLinearMap
  map_one' := rfl
  map_mul' := fun _ _ ↦ rfl

-- Mathlib/Algebra/Algebra/Hom.lean
lemma AlgEquiv.toMulEquiv_injective {R A B} [CommSemiring R] [Semiring A] [Semiring B]
    [Algebra R A] [Algebra R B] :
    Function.Injective (AlgEquiv.toMulEquiv (R := R) (A := A) (B := B)) :=
  fun _ _ e ↦ ext fun a ↦ FunLike.congr_fun e a

lemma linearIndependent_algEquiv_toLinearMap'
    (K L) [CommSemiring K] [CommRing L] [IsDomain L] [Algebra K L] :
    LinearIndependent L (AlgEquiv.toLinearMap : (L ≃ₐ[K] L) → L →ₗ[K] L) := by
  apply LinearIndependent.of_comp (LinearMap.ltoFun K L L)
  exact (linearIndependent_monoidHom L L).comp
    (MulEquiv.toMonoidHom ∘ AlgEquiv.toMulEquiv : (L ≃ₐ[K] L) → _)
    (MulEquiv.toMonoidHom_injective.comp AlgEquiv.toMulEquiv_injective)

lemma linearIndependent_algEquiv_toLinearMap
    (K L) [Field K] [CommRing L] [IsDomain L] [Algebra K L] :
    LinearIndependent K (AlgEquiv.toLinearMap : (L ≃ₐ[K] L) → L →ₗ[K] L) := by
  apply (linearIndependent_algEquiv_toLinearMap' K L).restrict_scalars
  simp_rw [Algebra.smul_def, mul_one]
  exact (algebraMap K L).injective

-- Mathlib/Algebra/Algebra/Hom.lean (near `AlgEquiv.aut`)
lemma AlgEquiv.pow_toLinearMap {K L} [CommSemiring K] [Semiring L] [Algebra K L]
    (σ : L ≃ₐ[K] L) (n : ℕ) : (σ ^ n).toLinearMap = σ.toLinearMap ^ n :=
  (AlgEquiv.toLinearMapHom K L).map_pow σ n

-- Mathlib/Algebra/Algebra/Hom.lean
lemma AlgEquiv.one_toLinearMap {K L} [CommSemiring K] [Semiring L] [Algebra K L] :
    (1 : L ≃ₐ[K] L).toLinearMap = 1 := rfl

-- Mathlib/LinearAlgebra/Eigenspace/Basic.lean
lemma Module.End.HasEigenvector.pow_apply {R} [CommRing R] {M} [AddCommGroup M] [Module R M]
    {f : Module.End R M} {μ : R} {v : M}
    (hv : f.HasEigenvector μ v) (n : ℕ) : (f ^ n) v = μ ^ n • v := by
  induction n <;> simp [*, pow_succ f, hv.apply_eq_smul, smul_smul, pow_succ' μ]

-- Mathlib/Logic/Equiv/Defs.lean
lemma EquivLike.coe_coe {E α β : Sort*} [EquivLike E α β] (e : E) :
  ((e : α ≃ β) : α → β) = e := rfl

-- Mathlib/RingTheory/Finiteness.lean
theorem Module.Finite.of_fintype_basis {R M} [CommSemiring R] [AddCommMonoid M] [Module R M] {ι : Type w}
  [_root_.Finite ι] (h : Basis ι R M) : Finite R M := by
  classical
  cases nonempty_fintype ι
  exact ⟨⟨Finset.univ.image h, by
    convert h.span_eq
    simp⟩⟩

-- Mathlib/RingTheory/Trace.lean
lemma Algebra.trace_eq_of_algEquiv {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] (e : B ≃ₐ[A] C) (x) :
    Algebra.trace A C (e x) = Algebra.trace A B x := by
  by_cases hB : ∃ s : Finset B, Nonempty (Basis s A B)
  · obtain ⟨s, ⟨b⟩⟩ := hB
    haveI := Module.Finite.of_fintype_basis b
    haveI := (Module.free_def A B).mpr ⟨_, ⟨b⟩⟩
    haveI := Module.Finite.of_fintype_basis (b.map e.toLinearEquiv)
    haveI := (Module.free_def A C).mpr ⟨_, ⟨(b.map e.toLinearEquiv).reindex (e.image _)⟩⟩
    dsimp [Algebra.trace_apply]
    rw [← LinearMap.trace_conj' _ e.toLinearEquiv]
    congr
    ext; simp [LinearEquiv.conj_apply]
  rw [trace_eq_zero_of_not_exists_basis _ hB, trace_eq_zero_of_not_exists_basis]
  rfl
  intro ⟨s, ⟨b⟩⟩
  classical
  exact hB ⟨s.image e.symm, ⟨(b.map e.symm.toLinearEquiv).reindex
    ((e.symm.image s).trans (Equiv.Set.ofEq Finset.coe_image.symm))⟩⟩

-- Mathlib/RingTheory/Trace.lean
lemma Algebra.trace_eq_of_ringEquiv {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A C] [Algebra B C] (e : A ≃+* B) (he : (algebraMap B C).comp e = algebraMap A C) (x) :
    e (Algebra.trace A C x) = Algebra.trace B C x := by
  classical
  by_cases h : ∃ s : Finset C, Nonempty (Basis s B C)
  · obtain ⟨s, ⟨b⟩⟩ := h
    letI : Algebra A B := RingHom.toAlgebra e
    letI : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq' he.symm
    rw [Algebra.trace_eq_matrix_trace b,
      Algebra.trace_eq_matrix_trace (b.mapCoeffs e.symm (by simp [Algebra.smul_def, ← he]))]
    show e.toAddMonoidHom _ = _
    rw [AddMonoidHom.map_trace]
    congr
    ext i j
    simp [leftMulMatrix_apply, LinearMap.toMatrix_apply]
  rw [trace_eq_zero_of_not_exists_basis _ h, trace_eq_zero_of_not_exists_basis,
    LinearMap.zero_apply, LinearMap.zero_apply, map_zero]
  intro ⟨s, ⟨b⟩⟩
  exact h ⟨s, ⟨b.mapCoeffs e (by simp [Algebra.smul_def, ← he])⟩⟩

-- Mathlib/RingTheory/Trace.lean
lemma Algebra.trace_eq_of_equiv_equiv {A₁ B₁ A₂ B₂ : Type*} [CommRing A₁] [CommRing B₁]
    [CommRing A₂] [CommRing B₂] [Algebra A₁ B₁] [Algebra A₂ B₂] (e₁ : A₁ ≃+* A₂) (e₂ : B₁ ≃+* B₂)
    (he : RingHom.comp (algebraMap A₂ B₂) ↑e₁ = RingHom.comp ↑e₂ (algebraMap A₁ B₁)) (x) :
    Algebra.trace A₁ B₁ x = e₁.symm (Algebra.trace A₂ B₂ (e₂ x)) := by
  letI := (RingHom.comp (e₂ : B₁ →+* B₂) (algebraMap A₁ B₁)).toAlgebra
  let e' : B₁ ≃ₐ[A₁] B₂ := { e₂ with commutes' := fun _ ↦ rfl }
  rw [← Algebra.trace_eq_of_ringEquiv e₁ he, ← Algebra.trace_eq_of_algEquiv e',
    RingEquiv.symm_apply_apply]
  rfl

-- Mathlib/RingTheory/Norm.lean
lemma Algebra.norm_eq_of_algEquiv {A : Type u} {B : Type v} {C : Type w}
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] (e : B ≃ₐ[A] C) (x) :
    Algebra.norm A (e x) = Algebra.norm A x := by
  by_cases hB : ∃ s : Finset B, Nonempty (Basis s A B)
  · obtain ⟨s, ⟨b⟩⟩ := hB
    haveI := Module.Finite.of_fintype_basis b
    haveI := (Module.free_def.{u, v, v} A B).mpr ⟨_, ⟨b⟩⟩
    haveI := Module.Finite.of_fintype_basis (b.map e.toLinearEquiv)
    haveI := (Module.free_def.{u, w, w} A C).mpr ⟨_, ⟨(b.map e.toLinearEquiv).reindex (e.image _)⟩⟩
    dsimp [Algebra.norm_apply]
    rw [← LinearMap.det_conj _ e.toLinearEquiv]
    congr
    ext; simp [LinearEquiv.conj_apply]
  rw [norm_eq_one_of_not_exists_basis _ hB, norm_eq_one_of_not_exists_basis]
  intro ⟨s, ⟨b⟩⟩
  classical
  exact hB ⟨s.image e.symm, ⟨(b.map e.symm.toLinearEquiv).reindex
    ((e.symm.image s).trans (Equiv.Set.ofEq Finset.coe_image.symm))⟩⟩

-- Mathlib/RingTheory/Norm.lean
lemma Algebra.norm_eq_of_ringEquiv {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A C] [Algebra B C] (e : A ≃+* B) (he : (algebraMap B C).comp e = algebraMap A C)
    (x : C) :
    e (Algebra.norm A x) = Algebra.norm B x := by
  classical
  by_cases h : ∃ s : Finset C, Nonempty (Basis s B C)
  · obtain ⟨s, ⟨b⟩⟩ := h
    letI : Algebra A B := RingHom.toAlgebra e
    letI : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq' he.symm
    rw [Algebra.norm_eq_matrix_det b,
      Algebra.norm_eq_matrix_det (b.mapCoeffs e.symm (by simp [Algebra.smul_def, ← he]))]
    show e.toRingHom _ = _
    rw [RingHom.map_det]
    congr
    ext i j
    simp [leftMulMatrix_apply, LinearMap.toMatrix_apply]
  rw [norm_eq_one_of_not_exists_basis _ h, norm_eq_one_of_not_exists_basis, map_one]
  intro ⟨s, ⟨b⟩⟩
  exact h ⟨s, ⟨b.mapCoeffs e (by simp [Algebra.smul_def, ← he])⟩⟩

-- Mathlib/RingTheory/Norm.lean
lemma Algebra.norm_eq_of_equiv_equiv {A₁ B₁ A₂ B₂ : Type*} [CommRing A₁] [CommRing B₁]
    [CommRing A₂] [CommRing B₂] [Algebra A₁ B₁] [Algebra A₂ B₂] (e₁ : A₁ ≃+* A₂) (e₂ : B₁ ≃+* B₂)
    (he : RingHom.comp (algebraMap A₂ B₂) ↑e₁ = RingHom.comp ↑e₂ (algebraMap A₁ B₁)) (x) :
    Algebra.norm A₁ x = e₁.symm (Algebra.norm A₂ (e₂ x)) := by
  letI := (RingHom.comp (e₂ : B₁ →+* B₂) (algebraMap A₁ B₁)).toAlgebra
  let e' : B₁ ≃ₐ[A₁] B₂ := { e₂ with commutes' := fun _ ↦ rfl }
  rw [← Algebra.norm_eq_of_ringEquiv e₁ he, ← Algebra.norm_eq_of_algEquiv e',
    RingEquiv.symm_apply_apply]
  rfl

-- Mathlib/LinearAlgebra/Matrix/NonsingularInverse.lean
lemma Matrix.mulVec_bijective {n R} [CommRing R] [Fintype n] [DecidableEq n]
    (M : Matrix n n R) (hM : IsUnit M.det) : Function.Bijective (mulVec M) := by
  rw [Function.bijective_iff_has_inverse]
  use mulVec M⁻¹
  simp [Function.LeftInverse, Function.RightInverse, nonsing_inv_mul _ hM, mul_nonsing_inv _ hM]

lemma Matrix.mulVec_injective {n R} [CommRing R] [Fintype n] [DecidableEq n]
    (M : Matrix n n R) (hM : IsUnit M.det) : Function.Injective (mulVec M) :=
  (M.mulVec_bijective hM).injective

-- Mathlib/RingTheory/FractionalIdeal.lean
namespace FractionalIdeal

open nonZeroDivisors

variable {R K} [CommRing R] [Field K] [Algebra R K] [IsFractionRing R K] [IsDedekindDomain R]
variable {I J : FractionalIdeal R⁰ K}

lemma le_inv_comm (hI : I ≠ 0) (hJ : J ≠ 0) : I ≤ J⁻¹ ↔ J ≤ I⁻¹ := by
  rw [inv_eq_one_div, inv_eq_one_div, le_div_iff_mul_le hI, le_div_iff_mul_le hJ, mul_comm]

lemma inv_le_comm (hI : I ≠ 0) (hJ : J ≠ 0) : I⁻¹ ≤ J ↔ J⁻¹ ≤ I := by
  simpa using le_inv_comm (inv_ne_zero hI) (inv_ne_zero hJ)

end FractionalIdeal

-- -- Mathlib/RingTheory/Localization/FractionRing.lean
-- noncomputable
-- instance {A B} [CommRing A] [CommRing B] [Algebra A B] [IsDomain A] [IsDomain B]
--     [NoZeroSMulDivisors A B] : Algebra (FractionRing A) (FractionRing B) :=
--   FractionRing.liftAlgebra A _

-- -- Mathlib/RingTheory/Localization/FractionRing.lean
-- instance {A B} [CommRing A] [CommRing B] [Algebra A B] [IsDomain A] [IsDomain B]
--     [NoZeroSMulDivisors A B] : IsScalarTower A (FractionRing A) (FractionRing B) :=
--   FractionRing.isScalarTower_liftAlgebra _ _

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
  refine ⟨IsIntegral_of_isLocalization R S Rₚ Sₚ M (IsSeparable.isIntegral _), fun x ↦ ?_⟩
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
    have := Module.Finite.of_fintype_basis b
    have := (Module.free_def.{u, v, v} R S).mpr ⟨s, ⟨b⟩⟩
    apply LinearMap.isNilpotent_trace_of_isNilpotent (hx.map (lmul R S))
  · rw [trace_eq_zero_of_not_exists_basis _ hS, LinearMap.zero_apply]
    exact IsNilpotent.zero

-- Mathlib/RingTheory/IntegralClosure.lean
-- From `FG_adjoin_singleton_of_integral`
open Polynomial Submodule Algebra in
theorem span_range_natDegree_eq_adjoin {R A} [CommRing R] [CommRing A] [Algebra R A]
    (x : A) (hx : IsIntegral R x) [DecidableEq A] :
    span R (Finset.image (x ^ ·) (Finset.range (natDegree (minpoly R x)))) =
    Subalgebra.toSubmodule (adjoin R {x}) := by
  nontriviality R
  nontriviality A
  classical
  let f := minpoly R x
  let hfm := minpoly.monic hx
  apply le_antisymm
  · rw [span_le]
    intro s hs
    rw [Finset.mem_coe] at hs
    rcases Finset.mem_image.1 hs with ⟨k, hk, rfl⟩
    clear hk
    exact (Algebra.adjoin R {x}).pow_mem (Algebra.subset_adjoin (Set.mem_singleton _)) k
  intro r hr; change r ∈ Algebra.adjoin R ({x} : Set A) at hr
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hr
  rcases (aeval x).mem_range.mp hr with ⟨p, rfl⟩
  rw [← modByMonic_add_div p hfm]
  rw [AlgHom.map_add, AlgHom.map_mul, minpoly.aeval R x, zero_mul, add_zero]
  have : natDegree (p %ₘ f) < natDegree f := natDegree_modByMonic_lt p hfm (minpoly.ne_one _ _)
  generalize p %ₘ f = q at this ⊢
  rw [← sum_C_mul_X_pow_eq q, aeval_def, eval₂_sum, sum_def]
  refine' sum_mem fun k hkq => _
  rw [eval₂_mul, eval₂_C, eval₂_pow, eval₂_X, ← Algebra.smul_def]
  refine' smul_mem _ _ (subset_span _)
  rw [Finset.mem_coe]; refine' Finset.mem_image.2 ⟨_, _, rfl⟩
  rw [Finset.mem_range]
  exact (le_natDegree_of_mem_supp _ hkq).trans_lt this

-- Mathlib/Data/Polynomial/RingDivision.lean
open Polynomial BigOperators in
lemma Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero {R} [CommRing R] [IsDomain R]
    (p : R[X]) {ι} [Fintype ι] {f : ι → R} (hf : Function.Injective f)
    (heval : ∀ i, p.eval (f i) = 0) (hcard : natDegree p < Fintype.card ι) : p = 0 := by
  classical
  by_contra hp
  apply not_lt_of_le (le_refl (Finset.card p.roots.toFinset))
  calc
    Finset.card p.roots.toFinset ≤ Multiset.card p.roots := Multiset.toFinset_card_le _
    _ ≤ natDegree p := Polynomial.card_roots' p
    _ < Fintype.card ι := hcard
    _ = Fintype.card (Set.range f) := (Set.card_range_of_injective hf).symm
    _ = Finset.card (Finset.univ.image f) := by rw [← Set.toFinset_card, Set.toFinset_range]
    _ ≤ Finset.card p.roots.toFinset := Finset.card_mono ?_
  intro _
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Multiset.mem_toFinset, mem_roots', ne_eq,
    IsRoot.def, forall_exists_index, hp, not_false_eq_true]
  rintro x rfl
  exact heval _

-- Dunno. Somewhere near Mathlib/FieldTheory/Minpoly/Basic.lean.
lemma aeval_derivative_minpoly_ne_zero {K L} [CommRing K] [CommRing L] [Algebra K L] (x : L)
    (hx : (minpoly K x).Separable) [Nontrivial L] :
    Polynomial.aeval x (Polynomial.derivative (minpoly K x)) ≠ 0 := by
  intro h
  obtain ⟨a, b, e⟩ := hx
  apply_fun (Polynomial.aeval x ·) at e
  simp only [map_add, _root_.map_mul, minpoly.aeval, mul_zero, h, add_zero, _root_.map_one] at e
  exact zero_ne_one e

-- Mathlib/FieldTheory/Separable.lean
lemma IsSeparable_of_equiv_equiv {A₁ B₁ A₂ B₂ : Type*} [Field A₁] [Field B₁]
    [Field A₂] [Field B₂] [Algebra A₁ B₁] [Algebra A₂ B₂] (e₁ : A₁ ≃+* A₂) (e₂ : B₁ ≃+* B₂)
    (he : RingHom.comp (algebraMap A₂ B₂) ↑e₁ = RingHom.comp ↑e₂ (algebraMap A₁ B₁))
    [IsSeparable A₁ B₁] : IsSeparable A₂ B₂ := by
  letI := e₁.toRingHom.toAlgebra
  letI := ((algebraMap A₁ B₁).comp e₁.symm.toRingHom).toAlgebra
  haveI : IsScalarTower A₁ A₂ B₁ := IsScalarTower.of_algebraMap_eq
    (fun x ↦ by simp [RingHom.algebraMap_toAlgebra])
  let e : B₁ ≃ₐ[A₂] B₂ := { e₂ with commutes' := fun r ↦ by simpa [RingHom.algebraMap_toAlgebra]
                                                  using FunLike.congr_fun he.symm (e₁.symm r) }
  haveI := isSeparable_tower_top_of_isSeparable A₁ A₂ B₁
  exact IsSeparable.of_algHom _ _ e.symm.toAlgHom

-- Mathlib/RingTheory/Finiteness.lean
lemma Module.Finite_of_equiv_equiv {A₁ B₁ A₂ B₂ : Type*} [CommRing A₁] [CommRing B₁]
    [CommRing A₂] [CommRing B₂] [Algebra A₁ B₁] [Algebra A₂ B₂] (e₁ : A₁ ≃+* A₂) (e₂ : B₁ ≃+* B₂)
    (he : RingHom.comp (algebraMap A₂ B₂) ↑e₁ = RingHom.comp ↑e₂ (algebraMap A₁ B₁))
    [Module.Finite A₁ B₁] : Module.Finite A₂ B₂ := by
  letI := e₁.toRingHom.toAlgebra
  letI := ((algebraMap A₁ B₁).comp e₁.symm.toRingHom).toAlgebra
  haveI : IsScalarTower A₁ A₂ B₁ := IsScalarTower.of_algebraMap_eq
    (fun x ↦ by simp [RingHom.algebraMap_toAlgebra])
  let e : B₁ ≃ₐ[A₂] B₂ := { e₂ with commutes' := fun r ↦ by simpa [RingHom.algebraMap_toAlgebra]
                                                  using FunLike.congr_fun he.symm (e₁.symm r) }
  haveI := Module.Finite.of_restrictScalars_finite A₁ A₂ B₁
  exact Module.Finite.equiv e.toLinearEquiv

-- Mathlib/Algebra/Module/Submodule/Pointwise.lean
open Pointwise in
lemma Submodule.span_singleton_mul {R S} [CommRing R] [CommRing S] [Algebra R S]
    {x : S} {p : Submodule R S} : Submodule.span R {x} * p = x • p := by
  ext; exact Submodule.mem_span_singleton_mul

-- Mathlib/Algebra/Module/Submodule/Pointwise.lean
open Pointwise in
lemma Submodule.mem_smul_iff_inv {R S} [CommRing R] [Field S] [Algebra R S]
    {x : S} {p : Submodule R S} {y : S} (hx : x ≠ 0) : y ∈ x • p ↔ x⁻¹ * y ∈ p := by
  constructor
  · rintro ⟨a, ha : a ∈ p, rfl⟩; simpa [inv_mul_cancel_left₀ hx]
  · exact fun h ↦ ⟨_, h, by simp [mul_inv_cancel_left₀ hx]⟩

-- Mathlib/Algebra/Module/Submodule/Pointwise.lean
open Pointwise in
lemma Submodule.mul_mem_smul_iff {R S} [CommRing R] [Field S] [Algebra R S]
    {x : S} {p : Submodule R S} {y : S} (hx : x ≠ 0) : x * y ∈ x • p ↔ y ∈ p := by
  rw [Submodule.mem_smul_iff_inv hx, inv_mul_cancel_left₀ hx]

-- Mathlib/RingTheory/Adjoin/Basic.lean
lemma Algebra.map_adjoin_singleton {R A B} [CommRing R] [CommRing A] [CommRing B] [Algebra R A]
    [Algebra R B] (x : A) (e : A →ₐ[R] B) :
    (Algebra.adjoin R {x}).map e = Algebra.adjoin R {e x} := by
  rw [AlgHom.map_adjoin, Set.image_singleton]

-- Mathlib/NumberTheory/KummerDedekind.lean
open IsLocalization in
lemma mem_coeIdeal_conductor {A B L} [CommRing A] [CommRing B] [CommRing L] [Algebra A B]
    [Algebra B L] [Algebra A L] [IsScalarTower A B L] [NoZeroSMulDivisors B L]
    (x : B) (y : L) :
    y ∈ coeSubmodule L (conductor A x) ↔ ∀ z : B,
      y * (algebraMap B L) z ∈ Algebra.adjoin A {algebraMap B L x} := by
  cases subsingleton_or_nontrivial L
  · rw [Subsingleton.elim (coeSubmodule L _) ⊤, Subsingleton.elim (Algebra.adjoin A _) ⊤]; simp
  trans ∀ z, y * (algebraMap B L) z ∈ (Algebra.adjoin A {x}).map (IsScalarTower.toAlgHom A B L)
  · simp only [coeSubmodule, Submodule.mem_map, Algebra.linearMap_apply, Subalgebra.mem_map,
      IsScalarTower.coe_toAlgHom']
    constructor
    · rintro ⟨y, hy, rfl⟩ z
      exact ⟨_, hy z, map_mul _ _ _⟩
    · intro H
      obtain ⟨y, _, e⟩ := H 1
      rw [_root_.map_one, mul_one] at e
      subst e
      simp only [← _root_.map_mul, (NoZeroSMulDivisors.algebraMap_injective B L).eq_iff,
        exists_eq_right] at H
      exact ⟨_, H, rfl⟩
  · rw [AlgHom.map_adjoin, Set.image_singleton]; rfl

-- -- Mathlib/Data/Polynomial/AlgebraMap
-- open Polynomial in
-- theorem aeval_algebraMap {R A B} [CommSemiring R] [CommSemiring A] [Semiring B]
--   [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
--   (x : A) (p : R[X]) : aeval (algebraMap A B x) p = algebraMap A B (aeval x p) := by
--   rw [aeval_def, aeval_def, hom_eval₂, IsScalarTower.algebraMap_eq R A B]

-- Mathlib/RingTheory/Nakayama.lean
open Ideal in
theorem Submodule.le_of_le_smul_of_le_jacobson_bot {R M} [CommRing R] [AddCommGroup M] [Module R M]
    {I : Ideal R} {N N' : Submodule R M} (hN' : N'.FG)
    (hIJ : I ≤ jacobson ⊥) (hNN : N ⊔ N' ≤ N ⊔ I • N') : N' ≤ N := by
  have := Submodule.smul_sup_le_of_le_smul_of_le_jacobson_bot hN' hIJ hNN
  rw [sup_eq_left.mpr this] at hNN
  exact le_sup_right.trans hNN

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

-- Mathlib/RingTheory/PolynomialAlgebra.lean
open Polynomial in
lemma Matrix.eval_det_add_X_smul {n} [Fintype n] [DecidableEq n] {R} [CommRing R]
    (A) (M : Matrix n n R) :
    (det (A + (X : R[X]) • M.map C)).eval 0 = (det A).eval 0 := by
  simp only [eval_det, map_zero, map_add, eval_add, Algebra.smul_def, _root_.map_mul]
  simp only [Algebra.algebraMap_eq_smul_one, matPolyEquiv_smul_one, map_X, X_mul, eval_mul_X,
    mul_zero, add_zero]

-- Mathlib/LinearAlgebra/Matrix/Trace.lean
lemma Matrix.trace_submatrix_succ {n : ℕ} {R} [CommRing R] (M : Matrix (Fin n.succ) (Fin n.succ) R) :
    M 0 0 + trace (submatrix M Fin.succ Fin.succ) = trace M := by
  delta trace
  rw [← (finSuccEquiv n).symm.sum_comp]
  simp

-- Not sure about the following fivem but they should probably go togethere

open Polynomial in
lemma Matrix.derivative_det_one_add_X_smul_aux {n} {R} [CommRing R] (M : Matrix (Fin n) (Fin n) R) :
    (derivative <| det (1 + (X : R[X]) • M.map C)).eval 0 = trace M := by
  induction n with
  | zero => simp
  | succ n IH =>
    rw [det_succ_row_zero, map_sum, eval_finset_sum]
    simp only [add_apply, smul_apply, map_apply, smul_eq_mul, X_mul_C, submatrix_add,
      submatrix_smul, Pi.add_apply, Pi.smul_apply, submatrix_map, derivative_mul, map_add,
      derivative_C, zero_mul, derivative_X, mul_one, zero_add, eval_add, eval_mul, eval_C, eval_X,
      mul_zero, add_zero, eval_det_add_X_smul, eval_pow, eval_neg, eval_one]
    rw [Finset.sum_eq_single 0]
    · simp only [Fin.val_zero, pow_zero, derivative_one, eval_zero, one_apply_eq, eval_one,
        mul_one, zero_add, one_mul, Fin.succAbove_zero, submatrix_one _ (Fin.succ_injective _),
        det_one, IH, trace_submatrix_succ]
    · intro i _ hi
      cases n with
      | zero => exact (hi (Subsingleton.elim i 0)).elim
      | succ n =>
        simp only [one_apply_ne' hi, eval_zero, mul_zero, zero_add, zero_mul, add_zero]
        rw [det_eq_zero_of_column_eq_zero 0, eval_zero, mul_zero]
        intro j
        rw [submatrix_apply, Fin.succAbove_below, one_apply_ne]
        · exact (bne_iff_ne (Fin.succ j) (Fin.castSucc 0)).mp rfl
        · rw [Fin.castSucc_zero]; exact lt_of_le_of_ne (Fin.zero_le _) hi.symm
    · exact fun H ↦ (H <| Finset.mem_univ _).elim

open Polynomial in
lemma Matrix.derivative_det_one_add_X_smul {n} [Fintype n] [DecidableEq n] {R} [CommRing R]
    (M : Matrix n n R) : (derivative <| det (1 + (X : R[X]) • M.map C)).eval 0 = trace M := by
  let e := Matrix.reindexLinearEquiv R R (Fintype.equivFin n) (Fintype.equivFin n)
  rw [← Matrix.det_reindexLinearEquiv_self R[X] (Fintype.equivFin n)]
  convert derivative_det_one_add_X_smul_aux (e M)
  · ext; simp
  · delta trace
    rw [← (Fintype.equivFin n).symm.sum_comp]
    rfl

open Polynomial in
lemma Matrix.det_one_add_X_smul {n} [Fintype n] [DecidableEq n] {R} [CommRing R]
    (M : Matrix n n R) : det (1 + (X : R[X]) • M.map C) =
      (1 : R[X]) + trace M • X + (det (1 + (X : R[X]) • M.map C)).divX.divX * X ^ 2 := by
  rw [Algebra.smul_def (trace M), ← C_eq_algebraMap, pow_two, ← mul_assoc, add_assoc,
    ← add_mul, ← derivative_det_one_add_X_smul, ← coeff_zero_eq_eval_zero, coeff_derivative,
    Nat.cast_zero, @zero_add R, mul_one, ← coeff_divX, add_comm (C _), divX_mul_X_add,
    add_comm (1 : R[X]), ← C.map_one]
  convert (divX_mul_X_add _).symm
  rw [coeff_zero_eq_eval_zero, eval_det_add_X_smul, det_one, eval_one]

open Polynomial in
lemma Matrix.det_one_add_smul {n} [Fintype n] [DecidableEq n] {R} [CommRing R] (r : R)
    (M : Matrix n n R) : det (1 + r • M) =
      1 + trace M * r + (det (1 + (X : R[X]) • M.map C)).divX.divX.eval r * r ^ 2 := by
  have := congr_arg (eval r) (Matrix.det_one_add_X_smul M)
  simp only [eval_det, scalar_apply, map_add, _root_.map_one, eval_add, eval_one, eval_smul, eval_X,
    smul_eq_mul, eval_mul, eval_pow] at this
  convert this
  rw [Algebra.smul_def X, _root_.map_mul]
  have : matPolyEquiv (M.map C) = C M
  · ext; simp only [matPolyEquiv_coeff_apply, map_apply, coeff_C]; rw [ite_apply, ite_apply]; rfl
  simp only [Algebra.algebraMap_eq_smul_one, matPolyEquiv_smul_one, map_X, X_mul, eval_mul_X, this,
    Algebra.mul_smul_comm, mul_one, eval_C]
  exact Matrix.smul_eq_mul_diagonal _ _

lemma Algebra.norm_one_add_smul {A B} [CommRing A] [CommRing B] [Algebra A B]
  [Module.Free A B] [Module.Finite A B] (a : A) (x : B) :
    ∃ r : A, Algebra.norm A (1 + a • x) = 1 + Algebra.trace A B x * a + r * a ^ 2 := by
  classical
  let ι := Module.Free.ChooseBasisIndex A B
  let b : Basis ι A B := Module.Free.chooseBasis _ _
  haveI : Fintype ι := inferInstance
  clear_value ι b
  simp_rw [Algebra.norm_eq_matrix_det b, Algebra.trace_eq_matrix_trace b]
  simp only [map_add, map_one, map_smul, Matrix.det_one_add_smul a]
  exact ⟨_, rfl⟩

-- Mathlib/Algebra/Algebra/Hom.lean
lemma RingHom.toIntAlgHom_injective {R₁ R₂} [Ring R₁] [Ring R₂] [Algebra ℤ R₁] [Algebra ℤ R₂] :
    Function.Injective (RingHom.toIntAlgHom : (R₁ →+* R₂) → _) :=
  fun _ _ e ↦ FunLike.ext _ _ (fun x ↦ FunLike.congr_fun e x)

-- Mathlib/Data/Polynomial/RingDivision.lean
lemma one_mem_nthRootsFinset {R : Type*} {n : ℕ} [CommRing R] [IsDomain R] (hn : 0 < n) :
    1 ∈ nthRootsFinset n R := by rw [mem_nthRootsFinset hn, one_pow]

-- Mathlib/LinearAlgebra/FiniteDimensional.lean
lemma FiniteDimensional.finrank_eq_one_of_linearEquiv {R V} [Field R]
    [AddCommGroup V] [Module R V] (e : R ≃ₗ[R] V) : finrank R V = 1 :=
  finrank_eq_one_iff'.mpr ⟨e 1, by simp, fun w ↦ ⟨e.symm w, by simp [← e.map_smul]⟩⟩

-- Mathlib/LinearAlgebra/FiniteDimensional.lean
lemma FiniteDimensional.finrank_of_equiv_equiv {A₁ B₁ A₂ B₂ : Type*} [Field A₁] [Field B₁]
    [Field A₂] [Field B₂] [Algebra A₁ B₁] [Algebra A₂ B₂] (e₁ : A₁ ≃+* A₂) (e₂ : B₁ ≃+* B₂)
    (he : RingHom.comp (algebraMap A₂ B₂) ↑e₁ = RingHom.comp ↑e₂ (algebraMap A₁ B₁)) :
    finrank A₁ B₁ = finrank A₂ B₂ := by
  letI := e₁.toRingHom.toAlgebra
  letI := ((algebraMap A₁ B₁).comp e₁.symm.toRingHom).toAlgebra
  haveI : IsScalarTower A₁ A₂ B₁ := IsScalarTower.of_algebraMap_eq
    (fun x ↦ by simp [RingHom.algebraMap_toAlgebra])
  let e : B₁ ≃ₐ[A₂] B₂ := { e₂ with commutes' := fun r ↦ by simpa [RingHom.algebraMap_toAlgebra]
                                                  using FunLike.congr_fun he.symm (e₁.symm r) }
  have H : finrank A₁ A₂ = 1 := finrank_eq_one_of_linearEquiv
    { e₁ with map_smul' := (IsScalarTower.toAlgHom A₁ A₁ A₂).toLinearMap.map_smul }
  have := finiteDimensional_of_finrank_eq_succ H
  rw [← e.toLinearEquiv.finrank_eq, ← finrank_mul_finrank A₁ A₂ B₁, H, one_mul]
