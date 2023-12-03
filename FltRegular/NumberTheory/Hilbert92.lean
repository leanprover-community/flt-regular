
import FltRegular.NumberTheory.Cyclotomic.UnitLemmas
import FltRegular.NumberTheory.GaloisPrime
import FltRegular.NumberTheory.SystemOfUnits
import Mathlib

set_option autoImplicit false
open scoped NumberField nonZeroDivisors
open FiniteDimensional
open NumberField

variable (p : ℕ+) {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable {k : Type*} [Field k] [NumberField k] (hp : Nat.Prime p)

open FiniteDimensional BigOperators Finset
open CyclotomicIntegers (zeta)
-- Z[H] module M (rank L) submodule N (rank l) H-stable
-- H cyclic order p
-- M / N is free up to torsion rank r (as an ab group free rank r p)
-- r = r1 + r2 - 1 = NumberField.Units.rank


section thm91
variable
  (G : Type*) {H : Type*} [AddCommGroup G] [CommGroup H] [Fintype H] (hCard : Fintype.card H = p)
  (σ : H) (hσ : Subgroup.zpowers σ = ⊤) (r : ℕ)
  [DistribMulAction H G] [Module.Free ℤ G] [Module.Finite ℤ G] (hf : finrank ℤ G = r * (p - 1))

-- TODO maybe abbrev
local notation3 "A" => CyclotomicIntegers p
  -- MonoidAlgebra ℤ H ⧸ Ideal.span {∑ i in Finset.range p, (MonoidAlgebra.of ℤ H σ) ^ i}


abbrev systemOfUnits.IsMaximal {r} {p : ℕ+} {G} [AddCommGroup G] [Module (CyclotomicIntegers p) G]
    (sys : systemOfUnits (G := G) p r) :=
  Fintype (G ⧸ Submodule.span (CyclotomicIntegers p) (Set.range sys.units))

noncomputable
def systemOfUnits.isMaximal {r} (hf : finrank ℤ G = r * (p - 1)) [Module A G]
  (sys : systemOfUnits (G := G) p r) : sys.IsMaximal := by
  apply Nonempty.some
  apply (@nonempty_fintype _ ?_)
  apply Module.finite_of_fg_torsion
  rw [← FiniteDimensional.finrank_eq_zero_iff,  finrank_quotient',
    finrank_spanA p hp _ _ sys.linearIndependent, hf, mul_comm, Nat.sub_self]

noncomputable
def systemOfUnits.index [Module A G] (sys : systemOfUnits p G r) [sys.IsMaximal] :=
  Fintype.card (G ⧸ Submodule.span A (Set.range sys.units))


def systemOfUnits.IsFundamental [Module A G] (h : systemOfUnits p G r) :=
  ∃ _ : h.IsMaximal, ∀ (s : systemOfUnits p G r) (_ : s.IsMaximal), h.index ≤ s.index

lemma systemOfUnits.IsFundamental.maximal' [Module A G] (S : systemOfUnits p G r)
    (hs : S.IsFundamental) (a : systemOfUnits p G r) [a.IsMaximal] :
    (Submodule.span A (Set.range S.units)).toAddSubgroup.index ≤
      (Submodule.span A (Set.range a.units)).toAddSubgroup.index := by
  letI := hs.choose
  convert hs.choose_spec a ‹_› <;> symm <;> exact Nat.card_eq_fintype_card.symm

@[to_additive]
theorem Finsupp.prod_congr' {α M N} [Zero M] [CommMonoid N] {f₁ f₂ : α →₀ M} {g1 g2 : α → M → N}
    (h : ∀ x, g1 x (f₁ x) = g2 x (f₂ x)) (hg1 : ∀ i, g1 i 0 = 1) (hg2 : ∀ i, g2 i 0 = 1) :
    f₁.prod g1 = f₂.prod g2 := by
  classical
  rw [f₁.prod_of_support_subset (Finset.subset_union_left _ f₂.support) _ (fun i _ ↦ hg1 i),
    f₂.prod_of_support_subset (Finset.subset_union_right f₁.support _) _ (fun i _ ↦ hg2 i)]
  exact Finset.prod_congr rfl (fun x _ ↦ h x)

lemma LinearIndependent.update {ι} [DecidableEq ι] {R} [CommRing R] [Module R G]
    (f : ι → G) (i : ι) (g : G) (σ : R)
    (hσ : σ ∈ nonZeroDivisors R) (hg : σ • g = f i) (hf : LinearIndependent R f):
    LinearIndependent R (Function.update f i g) := by
  classical
  rw [linearIndependent_iff] at hf ⊢
  intros l hl
  have : (Finsupp.total ι G R f) (Finsupp.update (σ • l) i (l i)) = 0
  · rw [← smul_zero σ, ← hl, Finsupp.total_apply, Finsupp.total_apply, Finsupp.smul_sum]
    apply Finsupp.sum_congr'
    · intro x
      simp only [Finsupp.coe_update, Finsupp.coe_smul, Function.update_apply, ite_smul, smul_ite]
      rw [smul_smul, mul_comm σ, ← smul_smul, hg, Pi.smul_apply, smul_eq_mul, ← smul_smul]
      split <;> simp [*]
    · simp
    · simp
  ext j
  have := FunLike.congr_fun (hf (Finsupp.update (σ • l) i (l i)) this) j
  simp only [Finsupp.coe_update, Finsupp.coe_smul, ne_eq, Function.update_apply, Finsupp.coe_zero,
    Pi.zero_apply] at this
  split_ifs at this with hij
  · exact hij ▸ this
  · exact hσ (l j) ((mul_comm _ _).trans this)

@[to_additive]
lemma Subgroup.index_mono {G : Type*} [Group G] {H₁ H₂ : Subgroup G} (h : H₁ < H₂)
  [h₁ : Fintype (G ⧸ H₁)] :
  H₂.index < H₁.index := by
  rcases eq_or_ne H₂.index 0 with hn | hn
  · rw [hn, index_eq_card]
    exact Fintype.card_pos
  apply lt_of_le_of_ne
  · refine Nat.le_of_dvd (by rw [index_eq_card]; apply Fintype.card_pos) <| Subgroup.index_dvd_of_le h.le
  · have := fintypeOfIndexNeZero hn
    rw [←mul_one H₂.index, ←relindex_mul_index h.le, mul_comm, Ne, eq_comm]
    simp [-one_mul, -Nat.one_mul, hn, h.not_le]

namespace fundamentalSystemOfUnits
lemma existence [Module A G] : ∃ S : systemOfUnits p G r, S.IsFundamental := by
  obtain ⟨S⟩ := systemOfUnits.existence p hp G r hf
  letI := S.isMaximal hp hf
  have : { a | ∃ (S : systemOfUnits p G r) (_ : S.IsMaximal), a = S.index p G r }.Nonempty :=
    ⟨S.index, S, S.isMaximal hp hf, rfl⟩
  obtain ⟨S', hS', ha⟩ := Nat.sInf_mem this
  use S', hS'
  intro a' ha'
  rw [← ha]
  apply csInf_le (OrderBot.bddBelow _)
  use a', ha'

lemma lemma2 [Module A G] (S : systemOfUnits p G r) (hs : S.IsFundamental) (i : Fin r) :
    ∀ g : G, (1 - zeta p) • g ≠ S.units i := by
  intro g hg
  letI := Fact.mk hp
  let S' : systemOfUnits p G r := ⟨Function.update S.units i g,
    LinearIndependent.update (hσ := CyclotomicIntegers.one_sub_zeta_mem_nonZeroDivisors p)
      (hg := hg) S.linearIndependent⟩
  letI := S'.isMaximal hp hf
  suffices : Submodule.span A (Set.range S.units) < Submodule.span A (Set.range S'.units)
  · exact (hs.maximal' S').not_lt (AddSubgroup.index_mono (h₁ := S.isMaximal hp hf) this)
  rw [SetLike.lt_iff_le_and_exists]
  constructor
  · rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    by_cases hij : i = j
    · rw [← hij, ← hg]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, Function.update_same _ _ _⟩)
    · exact Submodule.subset_span ⟨j, Function.update_noteq (Ne.symm hij) _ _⟩
  · refine ⟨g, Submodule.subset_span ⟨i, Function.update_same _ _ _⟩, ?_⟩
    rw [← Finsupp.range_total]
    rintro ⟨l, rfl⟩
    letI := (Algebra.id A).toModule
    letI : SMulZeroClass A A := SMulWithZero.toSMulZeroClass
    letI : Module A (Fin r →₀ A) := Finsupp.module (Fin r) A
    rw [← (Finsupp.total _ _ _ _).map_smul, ← one_smul A (S.units i),
      ← Finsupp.total_single A (v := S.units), ← sub_eq_zero,
      ← (Finsupp.total (Fin r) G A S.units).map_sub] at hg
    have := FunLike.congr_fun (linearIndependent_iff.mp S.linearIndependent _ hg) i
    simp only [Finsupp.coe_sub, Pi.sub_apply, Finsupp.single_eq_same] at this
    exact CyclotomicIntegers.not_isUnit_one_sub_zeta p
      (isUnit_of_mul_eq_one _ _ (sub_eq_zero.mp this))

lemma lemma2' [Module A G] (S : systemOfUnits p G r) (hs : S.IsFundamental) (i : Fin r) (a : ℤ)
    (ha : ¬ (p : ℤ) ∣ a) : ∀ g : G, (1 - zeta p) • g ≠ a • (S.units i) := by
  intro g hg
  letI := Fact.mk hp
  obtain ⟨x, y, e⟩ := CyclotomicIntegers.isCoprime_one_sub_zeta p a ha
  apply lemma2 p hp G r hf S hs i (x • (S.units i) + y • g)
  conv_rhs => rw [← one_smul A (S.units i), ← e, add_smul, ← smul_smul y, intCast_smul, ← hg]
  rw [smul_add, smul_smul, smul_smul, smul_smul, mul_comm x, mul_comm y]

lemma corollary [Module A G] (S : systemOfUnits p G r) (hs : S.IsFundamental) (a : Fin r → ℤ)
    (ha : ∃ i , ¬ (p : ℤ) ∣ a i) :
  ∀ g : G, (1 - zeta p) • g ≠ ∑ i, a i • S.units i := sorry

end fundamentalSystemOfUnits
section application

variable
    [Algebra k K] [IsGalois k K] [FiniteDimensional k K] -- [IsCyclic (K ≃ₐ[k] K)] -- technically redundant but useful
    (hKL : finrank k K = p) (σ : K ≃ₐ[k] K) (hσ : ∀ x, x ∈ Subgroup.zpowers σ)

def RelativeUnits (k K : Type*) [Field k] [Field K] [Algebra k K] :=
  ((𝓞 K)ˣ ⧸ (MonoidHom.range <| Units.map (algebraMap ↥(𝓞 k) ↥(𝓞 K) : ↥(𝓞 k) →* ↥(𝓞 K))))

instance : CommGroup (RelativeUnits k K) := by delta RelativeUnits; infer_instance

attribute [local instance] IsCyclic.commGroup

attribute [local instance 2000] inst_ringOfIntegersAlgebra Algebra.toSMul Algebra.toModule

instance : IsScalarTower ↥(𝓞 k) ↥(𝓞 K) K := IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
instance : IsIntegralClosure ↥(𝓞 K) ↥(𝓞 k) K := isIntegralClosure_of_isIntegrallyClosed _ _ _
  (fun x ↦ IsIntegral.tower_top (IsIntegralClosure.isIntegral ℤ K x))

lemma coe_galRestrictHom_apply (σ : K →ₐ[k] K) (x) :
    (galRestrictHom (𝓞 k) k (𝓞 K) K σ x : K) = σ x :=
  algebraMap_galRestrictHom_apply (𝓞 k) k (𝓞 K) K σ x

noncomputable
def relativeUnitsMap (σ : K →ₐ[k] K) : RelativeUnits k K →* RelativeUnits k K := by
  apply QuotientGroup.lift _
    ((QuotientGroup.mk' _).comp (Units.map (galRestrictHom (𝓞 k) k (𝓞 K) K σ)))
  rintro _ ⟨i, rfl⟩
  simp only [MonoidHom.mem_ker, MonoidHom.coe_comp, QuotientGroup.coe_mk', Function.comp_apply,
    QuotientGroup.eq_one_iff, MonoidHom.mem_range, Units.ext_iff, Units.coe_map, MonoidHom.coe_coe,
    AlgHom.commutes, exists_apply_eq_apply]

lemma relativeUnitsMap_mk (σ : K →ₐ[k] K) (x : (𝓞 K)ˣ) :
    relativeUnitsMap σ (QuotientGroup.mk x) =
      QuotientGroup.mk (Units.map (galRestrictHom (𝓞 k) k (𝓞 K) K σ) x) := rfl

@[simps]
noncomputable
def relativeUnitsMapHom : (K →ₐ[k] K) →* (Monoid.End (RelativeUnits k K)) where
  toFun := relativeUnitsMap
  map_one' := by
    refine FunLike.ext _ _ (fun x ↦ ?_)
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
    rw [relativeUnitsMap]
    erw [QuotientGroup.lift_mk'] -- why?
    simp only [map_one, MonoidHom.coe_comp, QuotientGroup.coe_mk', Function.comp_apply,
      Monoid.coe_one, id_eq]
    rfl
  map_mul' := by
    intros f g
    refine FunLike.ext _ _ (fun x ↦ ?_)
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
    simp only [relativeUnitsMap, map_mul, Monoid.coe_mul, Function.comp_apply]
    rfl

@[simps]
def Monoid.EndAdditive {M} [Monoid M] : Monoid.End M ≃* AddMonoid.End (Additive M) where
  __ := MonoidHom.toAdditive
  map_mul' := fun _ _ ↦ rfl

def Group.forall_mem_zpowers_iff {H} [Group H] {x : H} :
    (∀ y, y ∈ Subgroup.zpowers x) ↔ Subgroup.zpowers x = ⊤ := by
  rw [SetLike.ext_iff]
  simp only [Subgroup.mem_top, iff_true]

lemma pow_finEquivZpowers_symm_apply {M} [Group M] (x : M) (hx) (a) :
    x ^ ((finEquivZpowers x hx).symm a : ℕ) = a :=
  congr_arg Subtype.val ((finEquivZpowers x hx).apply_symm_apply a)

open Polynomial in
lemma isTors' : Module.IsTorsionBySet ℤ[X]
    (Module.AEval' (addMonoidEndRingEquivInt _
      (Monoid.EndAdditive <| relativeUnitsMap <| ((algHomUnitsEquiv _ _).symm σ).val)))
    (Ideal.span {cyclotomic p ℤ}) := by
  classical
  have := Fact.mk hp
  rw [← Module.isTorsionBySet_iff_is_torsion_by_span, Module.isTorsionBySet_singleton_iff]
  intro x
  obtain ⟨x, rfl⟩ := (Module.AEval.of _ _ _).surjective x
  obtain ⟨x, rfl⟩ := Additive.ofMul.surjective x
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
  rw [← Module.AEval.of_aeval_smul]
  simp only [AlgEquiv.toAlgHom_eq_coe, addMonoidHomLequivInt_apply, LinearMap.smul_def,
    AddEquivClass.map_eq_zero_iff, Polynomial.cyclotomic_prime ℤ p]
  simp only [map_sum, aeval_X, LinearMap.coeFn_sum, sum_apply, map_pow]
  simp only [← relativeUnitsMapHom_apply, ← map_pow, ← Units.val_pow_eq_pow_val]
  simp only [algHomUnitsEquiv, AlgHom.toRingHom_eq_coe, RingHom.toMonoidHom_eq_coe,
    OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe, MonoidHom.coe_coe, RingHom.coe_coe,
    MulEquiv.symm_mk, MulEquiv.coe_mk, Equiv.coe_fn_symm_mk, relativeUnitsMapHom_apply,
    Monoid.EndAdditive_apply, Equiv.toFun_as_coe, addMonoidEndRingEquivInt_apply,
    AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe, addMonoidHomLequivInt_apply,
    AddMonoidHom.coe_toIntLinearMap, MonoidHom.toAdditive_apply_apply, toMul_ofMul,
    relativeUnitsMap_mk]
  rw [← ofMul_prod, ← QuotientGroup.mk_prod, ofMul_eq_zero, QuotientGroup.eq_one_iff]
  use Units.map (RingOfIntegers.norm k) x
  ext
  simp only [Units.coe_map, MonoidHom.coe_coe, RingOfIntegers.coe_algebraMap_norm, map_pow,
    Units.coe_prod, Submonoid.coe_finset_prod, Subsemiring.coe_toSubmonoid,
    Subalgebra.coe_toSubsemiring, Algebra.norm_eq_prod_automorphisms]
  rw [← hKL, ← IsGalois.card_aut_eq_finrank, ← orderOf_eq_card_of_forall_mem_zpowers hσ,
    ← Fin.prod_univ_eq_prod_range, ← (finEquivZpowers σ <| isOfFinOrder_of_finite _).symm.prod_comp]
  simp only [pow_finEquivZpowers_symm_apply, coe_galRestrictHom_apply, AlgHom.coe_coe]
  rw [Finset.prod_set_coe (α := K ≃ₐ[k] K) (β := K) (f := fun i ↦ i ↑x) (Subgroup.zpowers σ)]
  congr
  ext x
  simpa using hσ x

@[nolint unusedArguments]
def relativeUnitsWithGenerator (_hp : Nat.Prime p)
  (_hKL : finrank k K = p) (σ : K ≃ₐ[k] K) (_hσ : ∀ x, x ∈ Subgroup.zpowers σ) : Type _ :=
  RelativeUnits k K

instance : CommGroup (relativeUnitsWithGenerator p hp hKL σ hσ) := by
  delta relativeUnitsWithGenerator; infer_instance

local notation "G" =>
  Additive (relativeUnitsWithGenerator p hp hKL σ hσ) ⧸
    AddCommGroup.torsion (Additive (relativeUnitsWithGenerator p hp hKL σ hσ))

def unit_to_U (u : (𝓞 K)ˣ) : G := QuotientAddGroup.mk (Additive.ofMul <| QuotientGroup.mk u)

local notation "mkG" => unit_to_U p hp hKL σ hσ

lemma unit_to_U_one : mkG 1 = 0 := by
  rw [unit_to_U, QuotientGroup.mk_one, ofMul_one, QuotientAddGroup.mk_zero]

lemma unit_to_U_mul (x y) : mkG (x * y) = mkG x + mkG y := by
  rw [unit_to_U, unit_to_U, unit_to_U, QuotientGroup.mk_mul, ofMul_mul, QuotientAddGroup.mk_add]

lemma unit_to_U_inv (x) : mkG (x⁻¹) = - mkG x := by
  rw [eq_neg_iff_add_eq_zero, ← unit_to_U_mul, mul_left_inv, unit_to_U_one]

lemma unit_to_U_div (x y) : mkG (x / y) = mkG x - mkG y := by
  rw [div_eq_mul_inv, unit_to_U_mul, unit_to_U_inv, sub_eq_add_neg]

noncomputable
instance relativeUnitsModule : Module A G := by
  letI : Module A (Additive (relativeUnitsWithGenerator p hp hKL σ hσ)) :=
    (isTors' p hp hKL σ hσ).module
  infer_instance

noncomputable
abbrev CyclotomicIntegers.mk : Polynomial ℤ →+* CyclotomicIntegers p := AdjoinRoot.mk _

lemma relativeUnitsModule_zeta_smul (x) :
    (zeta p) • mkG x = mkG (Units.map (galRestrictHom (𝓞 k) k (𝓞 K) K σ) x) := by
  let φ := (addMonoidEndRingEquivInt _
      (Monoid.EndAdditive <| relativeUnitsMap <| ((algHomUnitsEquiv _ _).symm σ).val))
  show QuotientAddGroup.mk ((Module.AEval'.of φ).symm <|
    Polynomial.X • Module.AEval'.of φ (Additive.ofMul (QuotientGroup.mk x))) = _
  simp only [val_algHomUnitsEquiv_symm_apply, Monoid.EndAdditive_apply, Equiv.toFun_as_coe,
    addMonoidEndRingEquivInt_apply, AddHom.toFun_eq_coe, LinearMap.coe_toAddHom,
    LinearEquiv.coe_coe, addMonoidHomLequivInt_apply, Module.AEval.of_symm_smul, Polynomial.aeval_X,
    LinearEquiv.symm_apply_apply, LinearMap.smul_def, AddMonoidHom.coe_toIntLinearMap,
    MonoidHom.toAdditive_apply_apply, toMul_ofMul, relativeUnitsMap_mk, unit_to_U]
  rfl

@[to_additive]
lemma isOfFinOrder_iff_zpow_eq_one {M} [Group M] {x : M} :
    IsOfFinOrder x ↔ ∃ (n : ℤ), n ≠ 0 ∧ x ^ n = 1 := by
  rw [isOfFinOrder_iff_pow_eq_one]
  refine ⟨fun ⟨n, hn, hn'⟩ ↦ ⟨n, Int.coe_nat_ne_zero_iff_pos.mpr hn, zpow_coe_nat x n ▸ hn'⟩,
    fun ⟨n, hn, hn'⟩ ↦ ⟨n.natAbs, Int.natAbs_pos.mpr hn, ?_⟩⟩
  cases' (Int.natAbs_eq_iff (a := n)).mp rfl with h h;
  · rwa [h, zpow_coe_nat] at hn'
  · rwa [h, zpow_neg, inv_eq_one, zpow_coe_nat] at hn'

lemma Submodule.torsion_int {M} [AddCommGroup M] :
    (Submodule.torsion ℤ M).toAddSubgroup = AddCommGroup.torsion M := by
  ext x
  refine ((isOfFinAddOrder_iff_zsmul_eq_zero (x := x)).trans ?_).symm
  simp [mem_nonZeroDivisors_iff_ne_zero]

local instance {M} [AddCommGroup M] : NoZeroSMulDivisors ℤ (M ⧸ AddCommGroup.torsion M) := by
  rw [← Submodule.torsion_int]
  show NoZeroSMulDivisors ℤ (M ⧸ Submodule.torsion ℤ M)
  infer_instance

lemma NumberField.Units.finrank_eq : finrank ℤ (Additive (𝓞 k)ˣ) = NumberField.Units.rank k := by
  rw [← rank_modTorsion]
  show _ = finrank ℤ (Additive (𝓞 k)ˣ ⧸ (AddCommGroup.torsion <| Additive (𝓞 k)ˣ))
  rw [← Submodule.torsion_int]
  exact (FiniteDimensional.finrank_quotient_of_le_torsion _ le_rfl).symm

instance : Module.Finite ℤ (Additive <| (𝓞 K)ˣ) := by
  constructor
  apply Submodule.fg_of_fg_map_of_fg_inf_ker ((Submodule.torsion ℤ (Additive <| (𝓞 K)ˣ)).mkQ)
  · simp only [Submodule.map_top, Submodule.range_mkQ]
    have : Module.Finite ℤ (Additive <| (𝓞 K)ˣ ⧸ (NumberField.Units.torsion K)) := inferInstance
    have : Module.Finite ℤ (Additive (𝓞 K)ˣ ⧸ (AddCommGroup.torsion <| Additive (𝓞 K)ˣ)) := this
    rw [← Submodule.torsion_int] at this
    exact this.1
  · simp only [Submodule.ker_mkQ, ge_iff_le, top_le_iff, le_top, inf_of_le_right]
    suffices : Module.Finite ℤ (AddCommGroup.torsion <| Additive <| (𝓞 K)ˣ)
    · rw [← Submodule.torsion_int] at this
      exact (Submodule.fg_top _).mp this.1
    show Module.Finite ℤ (Additive <| NumberField.Units.torsion K)
    rw [Module.Finite.iff_addGroup_fg, ← GroupFG.iff_add_fg]
    infer_instance

local instance : Module.Finite ℤ (Additive <| RelativeUnits k K) := by
  delta RelativeUnits
  show Module.Finite ℤ (Additive (𝓞 K)ˣ ⧸ AddSubgroup.toIntSubmodule (Subgroup.toAddSubgroup
    (MonoidHom.range <| Units.map (algebraMap ↥(𝓞 k) ↥(𝓞 K) : ↥(𝓞 k) →* ↥(𝓞 K)))))
  infer_instance

local instance : Module.Finite ℤ (Additive <| relativeUnitsWithGenerator p hp hKL σ hσ) := by
  delta relativeUnitsWithGenerator
  infer_instance

local instance : Module.Finite ℤ G := Module.Finite.of_surjective
  (M := Additive (relativeUnitsWithGenerator p hp hKL σ hσ))
  (QuotientAddGroup.mk' _).toIntLinearMap (QuotientAddGroup.mk'_surjective _)

local instance : Module.Free ℤ G := Module.free_of_finite_type_torsion_free'

lemma card_infinitePlace_eq_finrank_mul_of_odd {k K} [Field k] [Field K] [NumberField k]
    [NumberField K] [Algebra k K] (h : Odd (finrank k K)) :
    Fintype.card (InfinitePlace K) = finrank k K * Fintype.card (InfinitePlace k) := sorry

lemma NumberField.Units.rank_of_odd (h : Odd (finrank k K)) :
    NumberField.Units.rank K = (finrank k K) * NumberField.Units.rank k + (finrank k K) - 1 := by
  delta NumberField.Units.rank
  rw [card_infinitePlace_eq_finrank_mul_of_odd h,
    mul_tsub, mul_one, tsub_add_cancel_of_le]
  refine (mul_one _).symm.trans_le (Nat.mul_le_mul_left _ ?_)
  rw [Nat.one_le_iff_ne_zero, ← Nat.pos_iff_ne_zero, Fintype.card_pos_iff]
  infer_instance

variable (hp2 : p ≠ 2)

lemma finrank_G (hp2 : p ≠ 2) : finrank ℤ G = (Units.rank k + 1) * (↑p - 1) := by
  rw [← Submodule.torsion_int]
  refine (FiniteDimensional.finrank_quotient_of_le_torsion _ le_rfl).trans ?_
  show finrank ℤ (Additive (𝓞 K)ˣ ⧸ AddSubgroup.toIntSubmodule (Subgroup.toAddSubgroup
    (MonoidHom.range <| Units.map (algebraMap ↥(𝓞 k) ↥(𝓞 K) : ↥(𝓞 k) →* ↥(𝓞 K))))) = _
  rw [FiniteDimensional.finrank_quotient]
  show _ - finrank ℤ (LinearMap.range <| AddMonoidHom.toIntLinearMap <|
    MonoidHom.toAdditive <| Units.map (algebraMap ↥(𝓞 k) ↥(𝓞 K) : ↥(𝓞 k) →* ↥(𝓞 K))) = _
  have hodd : Odd (finrank k K)
  · rw [hKL]; exact hp.odd_of_ne_two (PNat.coe_injective.ne hp2)
  rw [LinearMap.finrank_range_of_inj, NumberField.Units.finrank_eq, NumberField.Units.finrank_eq,
    NumberField.Units.rank_of_odd hodd, add_mul, one_mul, mul_tsub, mul_one, mul_comm,
      add_tsub_assoc_of_le,
    tsub_add_eq_add_tsub, hKL]
  · exact (mul_one _).symm.trans_le (Nat.mul_le_mul_left _ hp.one_lt.le)
  · exact hKL ▸ hp.one_lt.le
  · intros i j e
    apply Additive.toMul.injective
    ext
    apply (algebraMap k K).injective
    exact congr_arg (fun i : Additive (𝓞 K)ˣ ↦ (↑(↑(Additive.toMul i) : 𝓞 K) : K)) e

lemma Hilbert91ish :
    ∃ S : systemOfUnits p G (NumberField.Units.rank k + 1), S.IsFundamental :=
  fundamentalSystemOfUnits.existence p hp G (NumberField.Units.rank k + 1)
    (finrank_G p hp hKL σ hσ hp2)

noncomputable

def unitlifts
   (S : systemOfUnits p G (NumberField.Units.rank k + 1))  :
  Fin (NumberField.Units.rank k + 1) → Additive (𝓞 K)ˣ := by
  let U := S.units
  intro i
  let u := (((U i)).out').out'
  exact u

lemma norm_map_inv (z : K) : Algebra.norm k z⁻¹ = (Algebra.norm k z)⁻¹ := by
    by_cases h : z = 0
    rw [h]
    simp
    apply eq_inv_of_mul_eq_one_left
    rw [← map_mul, inv_mul_cancel h, map_one]

lemma torsion_free_lin_system [Algebra k K] (h : Monoid.IsTorsionFree (𝓞 K)ˣ)
  (ι : Fin (NumberField.Units.rank k + 1) → Additive (𝓞 k)ˣ) :
  ∃ (a : (Fin (NumberField.Units.rank k + 1) → ℤ)) (i : Fin (NumberField.Units.rank k + 1)),
  ¬ ((p : ℤ) ∣ a i) ∧ ∑ i in ⊤, (a i) • (ι i) = 0 := by sorry



lemma u_lemma2 (u v : (𝓞 K)ˣ) (hu : u = v / (σ v : K)) : (mkG u) = (1 - zeta p : A) • (mkG v) := by
  rw [sub_smul, one_smul, relativeUnitsModule_zeta_smul, ← unit_to_U_div]
  congr
  rw [eq_div_iff_mul_eq']
  ext
  simp only [Units.val_mul, Units.coe_map, MonoidHom.coe_coe, Submonoid.coe_mul,
    Subsemiring.coe_toSubmonoid, Subalgebra.coe_toSubsemiring, coe_galRestrictHom_apply, hu]
  refine div_mul_cancel _ ?_
  simp only [ne_eq, map_eq_zero, ZeroMemClass.coe_eq_zero, Units.ne_zero, not_false_eq_true]


lemma lh_pow_free_aux {M} [CommGroup M] (h : ℕ) (ζ : M)
  (hζ : IsPrimitiveRoot ζ (p ^ h)) (hk : ∀ ε : M, ¬ IsPrimitiveRoot ε (p ^ (h + 1)))
  (r) (hr : finrank ℤ (Additive M) < r) (η : Fin r → Additive M) :
  ∃ (a : ℤ) (ι : Fin r → ℤ) (i : Fin r),
    ∑ i, ι i • η i = a • (Additive.ofMul ζ) ∧ ¬ ↑p ∣ ι i := by sorry

lemma lh_pow_free' {M} [CommGroup M] (h : ℕ) (ζ : M)
  (hζ : IsPrimitiveRoot ζ (p ^ h)) (hk : ∀ ε : M, ¬ IsPrimitiveRoot ε (p ^ (h + 1)))
  (r) (hr : finrank ℤ (Additive M) + 1 < r) (η : Fin r → Additive M) :
  ∃ (a : ℤ) (ι : Fin r → ℤ) (i : Fin r),
    ∑ i, ι i • (η i) = (a * p) • (Additive.ofMul ζ) ∧ ¬ ↑p ∣ ι i := by
  cases' r with r
  · exact (not_lt_zero' hr).elim
  simp only [Nat.succ_eq_add_one, add_lt_add_iff_right] at hr
  obtain ⟨a₁, ι₁, i₁, e₁, hi₁⟩ := lh_pow_free_aux p h ζ hζ hk r hr (η ∘ Fin.succ)
  obtain ⟨a₂, ι₂, i₂, e₂, hi₂⟩ := lh_pow_free_aux p h ζ hζ hk r hr (η ∘ Fin.succAbove i₁.succ)
  by_cases ha₁ : ↑p ∣ a₁
  · obtain ⟨b, hb⟩ := ha₁
    refine ⟨b, Function.extend Fin.succ ι₁ 0, Fin.succ i₁, ?_,
      by rwa [(Fin.succ_injective r).extend_apply]⟩
    rw [← hb.trans (mul_comm _ _), ← e₁]
    simp [Fin.sum_univ_succ, (Fin.succ_injective r).extend_apply]
  by_cases ha₂ : ↑p ∣ a₂
  · obtain ⟨b, hb⟩ := ha₂
    refine ⟨b, Function.extend (Fin.succAbove i₁.succ) ι₂ 0, Fin.succAbove i₁.succ i₂, ?_,
      by rwa [Fin.succAbove_right_injective.extend_apply]⟩
    rw [← hb.trans (mul_comm _ _), ← e₂]
    simp [Fin.sum_univ_succAbove _ i₁.succ, Fin.succAbove_right_injective.extend_apply]
  obtain ⟨α₁, β₁, h₁⟩ := (Nat.prime_iff_prime_int.mp hp).coprime_iff_not_dvd.mpr ha₁
  obtain ⟨α₂, β₂, h₂⟩ := (Nat.prime_iff_prime_int.mp hp).coprime_iff_not_dvd.mpr ha₂
  refine ⟨α₂ - α₁, β₁ • Function.extend Fin.succ ι₁ 0 -
      β₂ • Function.extend (Fin.succAbove i₁.succ) ι₂ 0, i₁.succ, ?_, ?_⟩
  · rw [sub_mul, eq_sub_iff_add_eq.mpr h₁, eq_sub_iff_add_eq.mpr h₂]
    simp only [zsmul_eq_mul, Pi.coe_int, Int.cast_id, Pi.sub_apply, Pi.mul_apply,
      Fin.exists_succ_eq_iff, ne_eq, not_not, not_exists, sub_sub_sub_cancel_left]
    simp only [sub_smul, mul_smul, ← e₁, ← e₂, sum_sub_distrib]
    rw [Fin.sum_univ_succ, Fin.sum_univ_succAbove _ i₁.succ]
    simp [(Fin.succ_injective r).extend_apply, Fin.succAbove_right_injective.extend_apply,
      (Fin.castSucc_lt_last _).ne, smul_sum]
  · simp only [zsmul_eq_mul, Pi.coe_int, Int.cast_id, Pi.sub_apply, Pi.mul_apply, Fin.succ_inj,
      exists_eq, not_true_eq_false, (Fin.succ_injective r).extend_apply, Fin.exists_succAbove_eq_iff,
      ne_eq, not_false_eq_true, Function.extend_apply', Pi.zero_apply, mul_zero, sub_zero,
      (Nat.prime_iff_prime_int.mp hp).dvd_mul, hi₁, not_or, and_true]
    intro H
    exact (Nat.prime_iff_prime_int.mp hp).not_dvd_one
      (h₁ ▸ dvd_add (dvd_mul_left (p : ℤ) α₁) (dvd_mul_of_dvd_left H a₁))

lemma IsPrimitiveRoot.coe_coe_iff {ζ : (𝓞 k)ˣ} {n} :
    IsPrimitiveRoot (ζ : k) n ↔ IsPrimitiveRoot ζ n :=
  IsPrimitiveRoot.map_iff_of_injective
    (f := (algebraMap (𝓞 k) k).toMonoidHom.comp (Units.coeHom (𝓞 k)))
    ((IsFractionRing.injective (𝓞 k) k).comp Units.ext)

lemma lh_pow_free [Algebra k K] [IsGalois k K] [FiniteDimensional k K] (h : ℕ) (ζ : (𝓞 k)ˣ)
  (hζ : IsPrimitiveRoot (ζ : k) (p ^ h)) (hk : ∀ ε : k, ¬ IsPrimitiveRoot ε (p ^ (h + 1)))
  (η : Fin (NumberField.Units.rank k + 2) → Additive (𝓞 k)ˣ) :
  ∃ (a : ℤ) (ι : Fin (NumberField.Units.rank k + 2) → ℤ) (i : Fin (NumberField.Units.rank k + 2)),
    ∑ i, ι i • (η i) = (a*p) • (Additive.ofMul ζ) ∧ ¬ ((p : ℤ) ∣ ι i) := by
  refine lh_pow_free' p hp h ζ (IsPrimitiveRoot.coe_coe_iff.mp hζ)
    (fun _ ↦ IsPrimitiveRoot.coe_coe_iff.not.mp (hk _)) _ ?_ η
  rw [NumberField.Units.finrank_eq]
  exact Nat.lt.base _

lemma IsPrimitiveRoot.totient_le_finrank {R} [CommRing R] [IsDomain R] [CharZero R]
    [Module.Finite ℤ R] {ζ : R} {r}
    (hζ : IsPrimitiveRoot ζ r) : r.totient ≤ finrank ℤ R := by
  by_cases hr : r = 0
  · rw [hr]; exact Nat.zero_le _
  replace hr := Nat.pos_iff_ne_zero.mpr hr
  calc
    _ ≤ (minpoly ℤ ζ).natDegree :=
      hζ.totient_le_degree_minpoly
    _ = (Algebra.adjoin.powerBasis' (hζ.isIntegral hr)).dim :=
      (Algebra.adjoin.powerBasis'_dim (hζ.isIntegral hr)).symm
    _ = finrank ℤ ↥(Algebra.adjoin ℤ {ζ}) :=
      (Algebra.adjoin.powerBasis' (hζ.isIntegral hr)).finrank'.symm
    _ ≤ finrank ℤ R :=
      Submodule.finrank_le (Subalgebra.toSubmodule (Algebra.adjoin ℤ {ζ}))



lemma h_exists : ∃ (h : ℕ) (ζ : (𝓞 k)ˣ),
    IsPrimitiveRoot (ζ : k) (p ^ h) ∧ ∀ ε : k, ¬ IsPrimitiveRoot ε (p ^ (h + 1)) := by
  classical
  have H : ∃ n, ∀ ε : k, ¬ IsPrimitiveRoot ε (p ^ n : ℕ+)
  · use finrank ℤ (𝓞 k) + 1
    intro ζ hζ
    have := hζ.unit'_coe.totient_le_finrank
    generalize finrank ℤ (𝓞 k) = n at this
    rw [PNat.pow_coe, Nat.totient_prime_pow_succ hp] at this
    have := (Nat.mul_le_mul_left _ (show (1 : ℕ) ≤ ↑p - 1 from
      le_tsub_of_add_le_right hp.two_le)).trans_lt (this.trans_lt n.lt_two_pow)
    simp only [mul_one] at this
    exact (lt_of_pow_lt_pow _ (Nat.zero_le _) this).not_le hp.two_le
  cases h : Nat.find H with
  | zero => simp at h
  | succ n =>
    have := Nat.find_min H ((Nat.lt_succ.mpr le_rfl).trans_le h.ge)
    simp only [not_forall, not_not] at this
    obtain ⟨ζ, hζ⟩ := this
    refine ⟨n, hζ.unit', hζ, by simpa only [h] using Nat.find_spec H⟩

lemma Hilbert92ish
    [Algebra k K] [IsGalois k K] [FiniteDimensional k K] [IsCyclic (K ≃ₐ[k] K)]
    (hKL : finrank k K = p) (σ : K ≃ₐ[k] K) (hσ : ∀ x, x ∈ Subgroup.zpowers σ) (hp : Nat.Prime p) :
    ∃ η : (𝓞 K)ˣ, Algebra.norm k (η : K) = 1 ∧ ∀ ε : (𝓞 K)ˣ, (η : K) ≠ ε / (σ ε : K) := by
    obtain ⟨h, ζ, hζ⟩ := h_exists p (k := k) hp
    by_cases H : ∀ ε : (𝓞 K)ˣ, (algebraMap k K ζ) ≠ ε / (σ ε : K)
    sorry
    simp only [ne_eq, not_forall, not_not] at H
    obtain ⟨ E, hE⟩:= H
    let NE := Units.map (RingOfIntegers.norm k ) E
    obtain ⟨S, hS⟩ := Hilbert91ish p (K := K) (k := k) hp hKL σ hσ hp2
    have NE_p_pow : ((Units.map (algebraMap (𝓞 k) (𝓞 K) ).toMonoidHom  ) NE) = E^(p : ℕ) := by sorry
    let H := unitlifts p hp hKL σ hσ S
    let N : Fin (NumberField.Units.rank k + 1) →  Additive (𝓞 k)ˣ :=
      fun e => Additive.ofMul (Units.map (RingOfIntegers.norm k )) (Additive.toMul (H e))
    let η : Fin (NumberField.Units.rank k + 1).succ →  Additive (𝓞 k)ˣ := Fin.snoc N (Additive.ofMul NE)
    obtain ⟨a, ι,i, ha⟩ := lh_pow_free p hp h ζ (k := k) (K:= K) hζ.1 hζ.2 η
    let Ζ :=  ((Units.map (algebraMap (𝓞 k) (𝓞 K) ).toMonoidHom  ) ζ)^(-a)
    let H2 : Fin (NumberField.Units.rank k + 1).succ →  Additive (𝓞 K)ˣ := Fin.snoc H (Additive.ofMul (E))
    let J := (Additive.toMul (∑ i : Fin (NumberField.Units.rank k + 1).succ, ι i • H2 i)) *
                 ((Units.map (algebraMap (𝓞 k) (𝓞 K) ).toMonoidHom  ) ζ)^(-a)
    refine ⟨J, ?_⟩
    constructor

    have JM : J = E^(ι (Fin.last (NumberField.Units.rank k + 1)))* Ζ *
          ∏ i : (Fin (NumberField.Units.rank k + 1)), (Additive.toMul (H2 i))^(ι i) := by
      simp only  [toMul_sum]
      rw [Fin.prod_univ_castSucc]
      simp only [Fin.snoc_castSucc, toMul_zsmul, Fin.snoc_last, toMul_ofMul,
        RingHom.toMonoidHom_eq_coe, zpow_neg, Fin.coe_eq_castSucc]
      sorry



    rw [JM]
    simp only [zpow_neg, RingHom.toMonoidHom_eq_coe, Fin.coe_eq_castSucc, Fin.snoc_castSucc,
      Units.val_mul, Units.coe_prod, Submonoid.coe_mul, Subsemiring.coe_toSubmonoid,
      Subalgebra.coe_toSubsemiring, coe_zpow', Submonoid.coe_finset_prod, map_mul, map_prod]




    sorry
    sorry
/-


    have S := @Hilbert91ish p K _ k _ _ _ _ σ
    obtain ⟨S, hS⟩ := S
    let H := @unitlifts p K _ k _ _ _ _ σ  S
    let N : Fin (NumberField.Units.rank k + 1) →  Additive (𝓞 k)ˣ :=
      fun e => Additive.ofMul (Units.map (RingOfIntegers.norm k )) (Additive.toMul (H e))
    let η : Fin (NumberField.Units.rank k + 2) →  Additive (𝓞 k)ˣ := Fin.cons (Additive.ofMul NE) N
    obtain ⟨a, ι,i, ha⟩ := lh_pow_free p h ζ (k := k) (K:= K) hζ.1 hζ.2 η


    have S := @Hilbert91ish p K _ k _ _ _ _ σ
    obtain ⟨S, hS⟩ := S
    let H := @unitlifts p K _ k _ _ _ S
    let N : Fin (NumberField.Units.rank k + 1) →  Additive (𝓞 k)ˣ :=
      fun e => Additive.ofMul (Units.map (RingOfIntegers.norm k )) (Additive.toMul (H e))


    by_cases T : Monoid.IsTorsionFree (𝓞 K)ˣ
    obtain ⟨a, i, ha⟩ := torsion_free_lin_system p T N
    have C := fundamentalSystemOfUnits.corollary p (Additive G ⧸ tors (k := k) (K := K) p)
      (NumberField.Units.rank k + 1) S hS a ⟨i, ha.1⟩
    let J := Additive.toMul (∑ i in ⊤, a i • H i)
    use J
    constructor
    let r :=   (Additive.toMul (H 1)).1

    have H1 : ∀ i : Fin (NumberField.Units.rank k + 1),
       (Algebra.norm k (( (Additive.toMul (H i)).1) : K)) = ((N i).1 : k) := by
       intro i
       simp
    have H2 : ∏ i in ⊤, ((N i).1 : k)^ a i = 1 := sorry
    simp only [toMul_sum, toMul_zsmul, Units.coe_prod, Submonoid.coe_finset_prod,
      Subsemiring.coe_toSubmonoid, Subalgebra.coe_toSubsemiring, coe_zpow', map_prod]
    rw [←H2]
    congr
    ext1 v
    simp only [toMul_ofMul, Units.coe_map, RingOfIntegers.norm_apply_coe]
    rw [map_zpow']
    apply norm_map_inv
    by_contra h
    simp at h

-/



lemma Hilbert92
    [Algebra k K] [IsGalois k K] [FiniteDimensional k K]
    (hKL : finrank k K = p) (σ : K ≃ₐ[k] K) (hσ : ∀ x, x ∈ Subgroup.zpowers σ) :
    ∃ η : (𝓞 K)ˣ, Algebra.norm k (η : K) = 1 ∧ ∀ ε : (𝓞 K)ˣ, (η : K) ≠ ε / (σ ε : K) := by sorry


end application

end thm91
