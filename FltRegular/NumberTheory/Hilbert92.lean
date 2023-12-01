
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
  [DistribMulAction H G] [Module.Free ℤ G] (hf : finrank ℤ G = r * (p - 1))

-- TODO maybe abbrev
local notation3 "A" => CyclotomicIntegers p
  -- MonoidAlgebra ℤ H ⧸ Ideal.span {∑ i in Finset.range p, (MonoidAlgebra.of ℤ H σ) ^ i}

instance systemOfUnits.instFintype {r}
  [Module A G] -- [IsScalarTower ℤ A G]
  (sys : systemOfUnits (G := G) p r) : Fintype (G ⧸ Submodule.span A (Set.range sys.units)) := sorry

def systemOfUnits.index [Module A G] (sys : systemOfUnits p G r) :=
  Fintype.card (G ⧸ Submodule.span A (Set.range sys.units))

def systemOfUnits.IsFundamental [Module A G] (h : systemOfUnits p G r) :=
  ∀ s : systemOfUnits p G r, h.index ≤ s.index

lemma systemOfUnits.IsFundamental.maximal' [Module A G] (S : systemOfUnits p G r)
    (hs : S.IsFundamental) (a : systemOfUnits p G r) :
    (Submodule.span A (Set.range S.units)).toAddSubgroup.index ≤
      (Submodule.span A (Set.range a.units)).toAddSubgroup.index := by
  convert hs a <;> symm <;> exact Nat.card_eq_fintype_card.symm

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
  have : { a | ∃ S : systemOfUnits p G r, a = S.index}.Nonempty := ⟨S.index, S, rfl⟩
  obtain ⟨S', ha⟩ := Nat.sInf_mem this
  use S'
  intro a'
  rw [← ha]
  apply csInf_le (OrderBot.bddBelow _)
  use a'

lemma lemma2 [Module A G] (S : systemOfUnits p G r) (hs : S.IsFundamental) (i : Fin r) :
    ∀ g : G, (1 - zeta p) • g ≠ S.units i := by
  intro g hg
  letI := Fact.mk hp
  let S' : systemOfUnits p G r := ⟨Function.update S.units i g,
    LinearIndependent.update (hσ := CyclotomicIntegers.one_sub_zeta_mem_nonZeroDivisors p)
      (hg := hg) S.linearIndependent⟩
  suffices : Submodule.span A (Set.range S.units) < Submodule.span A (Set.range S'.units)
  · exact (hs.maximal' S').not_lt (AddSubgroup.index_mono (h₁ := S.instFintype) this)
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
  apply lemma2 p hp G r S hs i (x • (S.units i) + y • g)
  conv_rhs => rw [← one_smul A (S.units i), ← e, add_smul, ← smul_smul y, intCast_smul, ← hg]
  rw [smul_add, smul_smul, smul_smul, smul_smul, mul_comm x, mul_comm y]

lemma corollary [Module A G] (S : systemOfUnits p G r) (hs : S.IsFundamental) (a : Fin r → ℤ)
    (ha : ∃ i , ¬ (p : ℤ) ∣ a i) :
  ∀ g : G, (1 - zeta p) • g ≠ ∑ i, a i • S.units i := sorry

end fundamentalSystemOfUnits
section application

variable
    [Algebra k K] [IsGalois k K] [FiniteDimensional k K] [IsCyclic (K ≃ₐ[k] K)] -- technically redundant but useful
    (hKL : finrank k K = p) (σ : K ≃ₐ[k] K) (hσ : ∀ x, x ∈ Subgroup.zpowers σ)

-- local instance : CommGroup (K ≃ₐ[k] K) where
--   mul_comm := by
--     have : Fintype.card (K ≃ₐ[k] K) = p := by
--       rwa [IsGalois.card_aut_eq_finrank]
--     have : IsCyclic (K ≃ₐ[k] K) := isCyclic_of_prime_card (hp := ⟨hp⟩) this
--     use IsCyclic.commGroup.mul_comm

def RelativeUnits (k K : Type*) [Field k] [Field K] [Algebra k K] :=
  ((𝓞 K)ˣ ⧸ (MonoidHom.range <| Units.map (algebraMap ↥(𝓞 k) ↥(𝓞 K) : ↥(𝓞 k) →* ↥(𝓞 K))))


-- local notation "G" => RelativeUnits k K

instance : CommGroup (RelativeUnits k K) := by delta RelativeUnits; infer_instance

attribute [local instance] IsCyclic.commGroup

-- open CommGroup
-- instance : MulDistribMulAction (K ≃ₐ[k] K) (K) := inferInstance
-- -- instance : MulDistribMulAction (K ≃ₐ[k] K) (𝓞 K) := sorry

-- noncomputable
-- instance : MulAction (K ≃ₐ[k] K) (𝓞 K)ˣ where
--   smul a := Units.map (galRestrict _ _ _ _ a : 𝓞 K ≃ₐ[ℤ] 𝓞 K)
--   one_smul b := by
--     change Units.map (galRestrict _ _ _ _ 1 : 𝓞 K ≃ₐ[ℤ] 𝓞 K) b = b
--     rw [MonoidHom.map_one]
--     rfl

--   mul_smul a b c := by
--     change (Units.map _) c = (Units.map _) (Units.map _ c)
--     rw [MonoidHom.map_mul]
--     rw [← MonoidHom.comp_apply]
--     rw [← Units.map_comp]
--     rfl

-- noncomputable
-- instance : MulDistribMulAction (K ≃ₐ[k] K) (𝓞 K)ˣ where
--   smul_mul a b c := by
--     change (Units.map _) (_ * _) = (Units.map _) _ * (Units.map _) _
--     rw [MonoidHom.map_mul]
--   smul_one a := by
--     change (Units.map _) 1 = 1
--     rw [MonoidHom.map_one]

-- instance : MulDistribMulAction (K ≃ₐ[k] K) G := sorry
-- -- instance : DistribMulAction (K ≃ₐ[k] K) (Additive G) := inferInstance
-- def ρ : Representation ℤ (K ≃ₐ[k] K) (Additive G) := Representation.ofMulDistribMulAction _ _
-- noncomputable
-- instance foof : Module
--   (MonoidAlgebra ℤ (K ≃ₐ[k] K))
--   (Additive G) := Representation.asModuleModule (ρ (k := k) (K := K))

-- lemma tors1 (a : Additive G) :
--     (∑ i in Finset.range p, (MonoidAlgebra.of ℤ (K ≃ₐ[k] K) σ) ^ i) • a = 0 := by
--   rw [sum_smul]
--   simp only [MonoidAlgebra.of_apply]
--   sorry

-- lemma tors2 (a : Additive G) (t)
--     (ht : t ∈ Ideal.span {∑ i in Finset.range p, (MonoidAlgebra.of ℤ (K ≃ₐ[k] K) σ) ^ i}) :
--     t • a = 0 := by
--   simp only [one_pow, Ideal.mem_span_singleton] at ht
--   obtain ⟨r, rfl⟩ := ht
--   let a': Module
--     (MonoidAlgebra ℤ (K ≃ₐ[k] K))
--     (Additive G) := foof
--   let a'': MulAction
--     (MonoidAlgebra ℤ (K ≃ₐ[k] K))
--     (Additive G) := inferInstance
--   rw [mul_comm, mul_smul]
--   let a''': MulActionWithZero
--     (MonoidAlgebra ℤ (K ≃ₐ[k] K))
--     (Additive G) := inferInstance
--   rw [tors1 p σ a, smul_zero] -- TODO this is the worst proof ever maybe because of sorries

attribute [local instance 2000] inst_ringOfIntegersAlgebra Algebra.toSMul

instance : IsScalarTower ↥(𝓞 k) ↥(𝓞 K) K := sorry
instance : IsIntegralClosure ↥(𝓞 K) ↥(𝓞 k) K := sorry

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


-- lemma isTors : Module.IsTorsionBySet
--     (MonoidAlgebra ℤ (K ≃ₐ[k] K))
--     (Additive G)
--     (Ideal.span {∑ i in Finset.range p, (MonoidAlgebra.of ℤ (K ≃ₐ[k] K) σ) ^ i} : Set _) := by
--   intro a s
--   rcases s with ⟨s, hs⟩
--   simp only [MonoidAlgebra.of_apply, one_pow, SetLike.mem_coe] at hs -- TODO ew why is MonoidAlgebra.single_pow simp matching here
--   have := tors2 p σ a s hs
--   simpa
-- noncomputable
-- local instance : Module
--   (MonoidAlgebra ℤ (K ≃ₐ[k] K) ⧸
--     Ideal.span {∑ i in Finset.range p, (MonoidAlgebra.of ℤ (K ≃ₐ[k] K) σ) ^ i}) (Additive G) :=
-- (isTors (k := k) (K := K) p σ).module

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

instance torsion.module {R M} [CommRing R] [AddCommGroup M] [Module R M] :
    Module R (M ⧸ AddCommGroup.torsion M) := by
  letI : Submodule R M := { AddCommGroup.torsion M with smul_mem' := fun r m ⟨n, hn, hn'⟩ ↦
    ⟨n, hn, by { simp only [Function.IsPeriodicPt, Function.IsFixedPt, add_left_iterate, add_zero,
      Nat.isUnit_iff, smul_comm n] at hn' ⊢; simp only [hn', smul_zero] }⟩ }
  exact inferInstanceAs (Module R (M ⧸ this))


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

local instance : Module.Free ℤ G := sorry

lemma finrank_G : finrank ℤ G = (Units.rank k + 1) * (↑p - 1) := sorry

-- #exit
lemma Hilbert91ish :
    ∃ S : systemOfUnits p G (NumberField.Units.rank k + 1), S.IsFundamental :=
  fundamentalSystemOfUnits.existence p hp G (NumberField.Units.rank k + 1) (finrank_G p hp hKL σ hσ)



-- #exit


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

lemma lh_pow_free  [Algebra k K] [IsGalois k K] [FiniteDimensional k K] (h : ℕ) (ζ : (𝓞 k)ˣ)
  (hζ : IsPrimitiveRoot ζ (p^h)) (hk : ∀ ε : k, ¬ IsPrimitiveRoot ε (p^(h+1)))
  ( η : Fin (NumberField.Units.rank k + 2) → Additive (𝓞 k)ˣ ) :
  ∃ (a : ℤ) (ι : Fin (NumberField.Units.rank k + 2) → ℤ) (i : Fin (NumberField.Units.rank k + 2)),
    ∑ i in ⊤, ι i • (η i) = (a*p) • (Additive.ofMul ζ) ∧ ¬ ((p : ℤ) ∣ ι i) := by sorry



lemma h_exists : ∃ (h : ℕ) (ζ : (𝓞 k)ˣ),
  IsPrimitiveRoot ζ (p^h) ∧   ∀ ε : k, ¬ IsPrimitiveRoot ε (p^(h+1)) := by sorry



--set_option maxHeartbeats 400000

lemma Hilbert92ish
    [Algebra k K] [IsGalois k K] [FiniteDimensional k K] [IsCyclic (K ≃ₐ[k] K)]
    (hKL : finrank k K = p) (σ : K ≃ₐ[k] K) (hσ : ∀ x, x ∈ Subgroup.zpowers σ) (hp : Nat.Prime p) :
    ∃ η : (𝓞 K)ˣ, Algebra.norm k (η : K) = 1 ∧ ∀ ε : (𝓞 K)ˣ, (η : K) ≠ ε / (σ ε : K) := by
    obtain ⟨h, ζ, hζ⟩:= h_exists p (k := k)
    by_cases H : ∀ ε : (𝓞 K)ˣ, (algebraMap k K ζ) ≠ ε / (σ ε : K)
    sorry
    simp only [ne_eq, not_forall, not_not] at H
    obtain ⟨ E, hE⟩:= H
    let NE := Units.map (RingOfIntegers.norm k ) E
    obtain ⟨S, hS⟩ := Hilbert91ish p (K := K) (k := k) hp
    have NE_p_pow : ((Units.map (algebraMap (𝓞 k) (𝓞 K) ).toMonoidHom  ) NE) = E^(p : ℕ) := by sorry
    let H := unitlifts p (K:= K) (k:=k)  S
    let N : Fin (NumberField.Units.rank k + 1) →  Additive (𝓞 k)ˣ :=
      fun e => Additive.ofMul (Units.map (RingOfIntegers.norm k )) (Additive.toMul (H e))
    let η : Fin (NumberField.Units.rank k + 1).succ →  Additive (𝓞 k)ˣ := Fin.snoc N (Additive.ofMul NE)
    obtain ⟨a, ι,i, ha⟩ := lh_pow_free p h ζ (k := k) (K:= K) hζ.1 hζ.2 η
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
