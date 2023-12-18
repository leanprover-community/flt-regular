import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Norm
import FltRegular.NumberTheory.AuxLemmas
import FltRegular.NumberTheory.Cyclotomic.UnitLemmas
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
/-!
# Kummer Theory

## Main result
- `isCyclic_tfae`:
Suppose `L/K` is a finite extension of dimension `n`, and `K` contains all `n`-th roots of unity.
Then `L/K` is cyclic iff
`L` is a splitting field of some irreducible polynomial of the form `Xⁿ - a : K[X]` iff
`L = K[α]` for some `αⁿ ∈ K`.

- `autEquivRootsOfUnity`:
Given an instance `IsSplittingField K L (X ^ n - C a)`
(perhaps via `isSplittingField_X_pow_sub_C_of_root_adjoin_eq_top`),
then the galois group is isomorphic to `rootsOfUnity n K`, by sending
`σ ↦ σ α / α` for `α ^ n = a`, and the inverse is given by `μ ↦ (α ↦ μ • α)`.

- `autEquivZmod`:
Furthermore, given an explicit choice `ζ` of a primitive `n`-th root of unity, the galois group is
then isomorphic to `Multiplicative (ZMod n)` whose inverse is given by
`i ↦ (α ↦ ζⁱ • α)`.

## Other results
Criteria for `X ^ n - C a` to be irreducible is given:
`X_pow_sub_C_irreducible_iff_of_prime`: `X ^ n - C a` is irreducible iff `a` is not a `p`-power.

TODO: criteria for general `n`.

-/
variable {K : Type*} [Field K]

open Polynomial IntermediateField AdjoinRoot

section Splits

theorem nthRoots_zero' {R} [CommRing R] [IsDomain R] {n : ℕ} :
    nthRoots n (0 : R) = Multiset.replicate n 0 := by
  rw [nthRoots, map_zero, sub_zero, roots_pow, roots_X, Multiset.nsmul_singleton]

lemma root_X_pow_sub_C_pow (n : ℕ) (a : K) :
    (AdjoinRoot.root (X ^ n - C a)) ^ n = AdjoinRoot.of _ a := by
  rw [← sub_eq_zero, ← AdjoinRoot.eval₂_root, eval₂_sub, eval₂_C, eval₂_pow, eval₂_X]

lemma root_X_pow_sub_C_ne_zero {n : ℕ} (hn : 1 < n) (a : K) :
    (AdjoinRoot.root (X ^ n - C a)) ≠ 0 :=
  mk_ne_zero_of_natDegree_lt (monic_X_pow_sub_C _ (Nat.not_eq_zero_of_lt hn))
    X_ne_zero <| by rwa [natDegree_X_pow_sub_C, natDegree_X]

lemma injOn_pow_mul_of_isPrimitiveRoot {n : ℕ} (hn : 0 < n) {ζ : K} (hζ : IsPrimitiveRoot ζ n)
    {α : K} (hα : α ≠ 0) :
    Set.InjOn (fun x => ζ ^ x * α) (Finset.range n) := by
  intros i hi j hj e
  rw [Finset.coe_range, Set.mem_Iio] at hi hj
  simp only [mul_eq_mul_right_iff, or_iff_left hα] at e
  have : (hζ.isUnit hn).unit' ^ i = (hζ.isUnit hn).unit' ^ j := Units.ext (by simpa using e)
  rw [pow_inj_mod, ← orderOf_injective ⟨⟨Units.val, Units.val_one⟩, Units.val_mul⟩
    Units.ext (hζ.isUnit hn).unit'] at this
  simpa [← hζ.eq_orderOf, Nat.mod_eq_of_lt, hi, hj] using this

theorem nthRoots_eq_of_isPrimitiveRoot {n : ℕ} (hn : 0 < n) {ζ : K} (hζ : IsPrimitiveRoot ζ n)
    {α a : K} (e : α ^ n = a) :
    nthRoots n a = (Finset.range n).val.map (ζ ^ · * α) := by
  by_cases hα : α = 0
  · rw [hα, zero_pow hn] at e
    simp only [hα, e.symm, nthRoots_zero', mul_zero,
      Finset.range_val, Multiset.map_const', Multiset.card_range]
  classical
  symm; apply Multiset.eq_of_le_of_card_le
  · rw [← Finset.image_val_of_injOn, Finset.val_le_iff_val_subset]
    · intro x hx
      simp only [Finset.image_val, Finset.range_val, Multiset.mem_dedup, Multiset.mem_map,
        Multiset.mem_range] at hx
      obtain ⟨m, _, rfl⟩ := hx
      rw [mem_nthRoots hn, mul_pow, e, ← pow_mul, mul_comm m,
        pow_mul, hζ.pow_eq_one, one_pow, one_mul]
    · exact injOn_pow_mul_of_isPrimitiveRoot hn hζ hα
  · simpa only [Finset.range_val, Multiset.card_map, Multiset.card_range] using card_nthRoots n a

theorem X_pow_sub_C_splits_of_isPrimitiveRoot
    {n : ℕ} {ζ : K} (hζ : IsPrimitiveRoot ζ n) {α a : K} (e : α ^ n = a) :
    (X ^ n - C a).Splits (RingHom.id _) := by
  cases n.eq_zero_or_pos with
  | inl hn =>
    rw [hn, pow_zero, ← C.map_one, ← map_sub]
    exact splits_C _ _
  | inr hn =>
    rw [splits_iff_card_roots, ← nthRoots, nthRoots_eq_of_isPrimitiveRoot hn hζ e,
      natDegree_X_pow_sub_C, Finset.range_val, Multiset.card_map, Multiset.card_range]

open BigOperators

theorem X_pow_sub_C_eq_prod
    {n : ℕ} {ζ : K} (hζ : IsPrimitiveRoot ζ n) {α a : K} (hn : 0 < n) (e : α ^ n = a) :
    (X ^ n - C a) = ∏ i in Finset.range n, (X - C (ζ ^ i * α)) := by
  rw [eq_prod_roots_of_monic_of_splits_id (monic_X_pow_sub_C _ (Nat.pos_iff_ne_zero.mp hn))
    (X_pow_sub_C_splits_of_isPrimitiveRoot hζ e), ← nthRoots,
    nthRoots_eq_of_isPrimitiveRoot hn hζ e, Multiset.map_map]
  rfl

end Splits

section Irreducible

lemma ne_zero_of_irreducible_X_pow_sub_C {n : ℕ} {a : K} (H : Irreducible (X ^ n - C a)) :
    n ≠ 0 := by
  rintro rfl
  rw [pow_zero, ← C.map_one, ← map_sub] at H
  exact not_irreducible_C _ H

lemma ne_zero_of_irreducible_X_pow_sub_C' {n : ℕ} (hn : n ≠ 1) {a : K}
    (H : Irreducible (X ^ n - C a)) : a ≠ 0 := by
  rintro rfl
  rw [map_zero, sub_zero] at H
  exact not_irreducible_pow hn H

-- TODO: use this to prove the case where the degree is arbitrary
theorem X_pow_sub_C_irreducible_of_prime {p : ℕ} (hp : p.Prime) {a : K} (ha : ∀ b : K, b ^ p ≠ a) :
    Irreducible (X ^ p - C a) := by
  -- First of all, We may find an irreducible factor `g` of `X ^ p - C a`.
  have : ¬ IsUnit (X ^ p - C a)
  · rw [Polynomial.isUnit_iff_degree_eq_zero, degree_X_pow_sub_C hp.pos, Nat.cast_eq_zero]
    exact hp.ne_zero
  have ⟨g, hg, hg'⟩ := WfDvdMonoid.exists_irreducible_factor this (X_pow_sub_C_ne_zero hp.pos a)
  -- It suffices to show that `deg g = p`.
  suffices natDegree g = p from (associated_of_dvd_of_natDegree_eq hg'
    (this.trans natDegree_X_pow_sub_C.symm) (X_pow_sub_C_ne_zero hp.pos a)).irreducible hg
  by_contra h
  have : Fact (Irreducible g) := ⟨hg⟩
  let Kx := AdjoinRoot g
  -- Let `r` be a root of `g`, then `N_K(r) ^ p = N_K(r ^ p) = N_K(a) = a ^ (deg g)`.
  have key : (Algebra.norm K (AdjoinRoot.root g)) ^ p = a ^ g.natDegree
  · have htop : Subalgebra.toSubmodule (⊤ : IntermediateField K Kx).toSubalgebra = ⊤ := rfl
    have := eval₂_eq_zero_of_dvd_of_eval₂_eq_zero _ _ hg' (AdjoinRoot.eval₂_root g)
    rw [eval₂_sub, eval₂_pow, eval₂_C, eval₂_X, sub_eq_zero] at this
    rw [← map_pow, this, ← AdjoinRoot.algebraMap_eq, Algebra.norm_algebraMap,
      ← finrank_top, ← htop, ← IntermediateField.adjoin_adjoinRoot_root_eq_top g,
      Subalgebra.finrank_toSubmodule, finrank_eq_finrank_subalgebra,
      IntermediateField.adjoin.finrank,
      AdjoinRoot.minpoly_root hg.ne_zero, natDegree_mul_C]
    · simpa using hg.ne_zero
    · exact AdjoinRoot.isIntegral_root hg.ne_zero
  -- Since `a ^ (deg g)` is a `p`-power, and `p` is coprime to `deg g`, we conclude that `a` is
  -- also a `p`-power, contradicting the hypothesis
  have : p.Coprime (natDegree g) := hp.coprime_iff_not_dvd.mpr (fun e ↦ h (((natDegree_le_of_dvd hg'
    (X_pow_sub_C_ne_zero hp.pos a)).trans_eq natDegree_X_pow_sub_C).antisymm (Nat.le_of_dvd
      (natDegree_pos_iff_degree_pos.mpr <| Polynomial.degree_pos_of_irreducible hg) e)))
  exact ha _ (mem_range_pow_of_coprime_of_pow_mem_range_pow this.symm a ⟨_, key⟩).choose_spec

theorem X_pow_sub_C_irreducible_iff_of_prime {p : ℕ} (hp : p.Prime) (a : K) :
    Irreducible (X ^ p - C a) ↔ ∀ b : K, b ^ p ≠ a := by
  refine ⟨?_, X_pow_sub_C_irreducible_of_prime hp⟩
  contrapose!
  rintro ⟨α, rfl⟩ H
  have := degree_eq_one_of_irreducible_of_root H (x := α) (by simp)
  rw [degree_X_pow_sub_C hp.pos, Nat.cast_eq_one] at this
  exact hp.ne_one this

end Irreducible

variable (n : ℕ) (hζ : (primitiveRoots n K).Nonempty) (a : K) (H : Irreducible (X ^ n - C a))

set_option quotPrecheck false in
notation3 "K[" n "√" a "]" => AdjoinRoot (Polynomial.X ^ n - Polynomial.C a)

section AdjoinRoot

-- Also see Polynomial.separable_X_pow_sub_C_unit
theorem separable_X_pow_sub_C_of_irreducible : (X ^ n - C a).Separable := by
  letI := Fact.mk H
  letI : Algebra K K[n√a] := inferInstance
  have hn := Nat.pos_iff_ne_zero.mpr (ne_zero_of_irreducible_X_pow_sub_C H)
  by_cases hn' : n = 1
  · rw [hn', pow_one]; exact separable_X_sub_C
  have ⟨ζ, hζ⟩ := hζ
  rw [mem_primitiveRoots (Nat.pos_of_ne_zero <| ne_zero_of_irreducible_X_pow_sub_C H)] at hζ
  rw [← separable_map (algebraMap K K[n√a]), Polynomial.map_sub, Polynomial.map_pow, map_C, map_X,
    algebraMap_eq, X_pow_sub_C_eq_prod (hζ.map_of_injective (algebraMap K _).injective) hn
    (root_X_pow_sub_C_pow n a), separable_prod_X_sub_C_iff']
  refine injOn_pow_mul_of_isPrimitiveRoot hn (hζ.map_of_injective (algebraMap K _).injective)
    (root_X_pow_sub_C_ne_zero ?_ _)
  exact lt_of_le_of_ne (show 1 ≤ n from hn) (Ne.symm hn')

noncomputable
def autAdjoinRootXPowSubCHom (hn : 0 < n) :
    rootsOfUnity ⟨n, hn⟩ K →* (K[n√a] →ₐ[K] K[n√a]) where
  toFun := fun η ↦ liftHom (X ^ n - C a) (((η : Kˣ) : K) • (root _) : K[n√a]) <| by
    have := (mem_rootsOfUnity' _ _).mp η.prop
    dsimp at this
    rw [map_sub, map_pow, aeval_C, aeval_X, Algebra.smul_def, mul_pow, root_X_pow_sub_C_pow,
      AdjoinRoot.algebraMap_eq, ← map_pow, this, map_one, one_mul, sub_self]
  map_one' := algHom_ext <| by simp
  map_mul' := fun ε η ↦ algHom_ext <| by simp [mul_smul, smul_comm ((ε : Kˣ) : K)]

noncomputable
def autAdjoinRootXPowSubC (hn : 0 < n) :
    rootsOfUnity ⟨n, hn⟩ K →* (K[n√a] ≃ₐ[K] K[n√a]) :=
  (algHomUnitsEquiv _ _).toMonoidHom.comp (autAdjoinRootXPowSubCHom n a hn).toHomUnits

lemma autAdjoinRootXPowSubC_root (hn : 0 < n) (η) :
    autAdjoinRootXPowSubC n a hn η (root _) = ((η : Kˣ) : K) • root _ := by
  dsimp [autAdjoinRootXPowSubC, autAdjoinRootXPowSubCHom, algHomUnitsEquiv]
  apply liftHom_root

variable {n} {a}

noncomputable
def autAdjoinRootXPowSubCEquiv (hn : 0 < n) :
    rootsOfUnity ⟨n, hn⟩ K ≃* (K[n√a] ≃ₐ[K] K[n√a]) where
  __ := autAdjoinRootXPowSubC n a hn
  invFun :=
    letI := Fact.mk H
    letI : Algebra K K[n√a] := inferInstance
    letI := Classical.decEq K
    fun σ ↦ (rootsOfUnity_equiv_of_primitiveRoots (algebraMap K K[n√a]) ⟨n, hn⟩ hζ).symm <|
      rootsOfUnity.mkOfPowEq (if n = 1 then 1 else σ (root _) / root _ : K[n√a]) <| by
        split
        · exact one_pow _
        rw [div_pow, ← map_pow]
        simp only [PNat.mk_coe, root_X_pow_sub_C_pow, ← algebraMap_eq, AlgEquiv.commutes]
        rw [div_self]
        rw [Ne.def, map_eq_zero_iff _ (algebraMap K _).injective]
        exact (ne_zero_of_irreducible_X_pow_sub_C' ‹_› H)
  left_inv := by
    intro η
    letI := Fact.mk H
    letI : Algebra K K[n√a] := inferInstance
    apply (rootsOfUnity_equiv_of_primitiveRoots (algebraMap K K[n√a]) ⟨n, hn⟩ hζ).injective
    ext
    simp only [algebraMap_eq, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
      autAdjoinRootXPowSubC_root, Algebra.smul_def, ne_eq, MulEquiv.apply_symm_apply,
      rootsOfUnity.val_mkOfPowEq_coe, rootsOfUnity_equiv_of_primitiveRoots_apply]
    split_ifs with h
    · subst h
      have : (η : Kˣ) = 1 := (pow_one _).symm.trans η.prop
      simp only [PNat.mk_one, this, Units.val_one, map_one]
    · refine mul_div_cancel _ (root_X_pow_sub_C_ne_zero ?_ _)
      exact lt_of_le_of_ne (show 1 ≤ n from hn) (Ne.symm h)
  right_inv := by
    intro e
    letI := Fact.mk H
    letI : Algebra K K[n√a] := inferInstance
    apply AlgEquiv.coe_algHom_injective
    apply AdjoinRoot.algHom_ext
    simp only [algebraMap_eq, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe, AlgHom.coe_coe,
      autAdjoinRootXPowSubC_root, Algebra.smul_def, PNat.mk_coe]
    rw [rootsOfUnity_equiv_of_primitiveRoots_symm_apply, rootsOfUnity.val_mkOfPowEq_coe]
    split_ifs with h
    · subst h
      rw [(pow_one _).symm.trans (root_X_pow_sub_C_pow 1 a), one_mul,
        ← algebraMap_eq, AlgEquiv.commutes]
    · refine div_mul_cancel _ (root_X_pow_sub_C_ne_zero ?_ _)
      exact lt_of_le_of_ne (show 1 ≤ n from hn) (Ne.symm h)

lemma autAdjoinRootXPowSubCEquiv_apply (hn : 0 < n) (η) :
    autAdjoinRootXPowSubCEquiv hζ H hn η = autAdjoinRootXPowSubC n a hn η := rfl

end AdjoinRoot

section IsSplittingField

variable {n} {a}
variable {L : Type*} [Field L] [Algebra K L] [IsSplittingField K L (X ^ n - C a)]

lemma isSplittingField_AdjoinRoot_X_pow_sub_C :
    letI := Fact.mk H
    letI : Algebra K K[n√a] := inferInstance
    IsSplittingField K K[n√a] (X ^ n - C a) := by
  letI := Fact.mk H
  letI : Algebra K K[n√a] := inferInstance
  constructor
  · rw [← splits_id_iff_splits, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_C,
      Polynomial.map_X]
    have ⟨_, hζ⟩ := hζ
    rw [mem_primitiveRoots (Nat.pos_of_ne_zero <| ne_zero_of_irreducible_X_pow_sub_C H)] at hζ
    exact X_pow_sub_C_splits_of_isPrimitiveRoot (hζ.map_of_injective (algebraMap K _).injective)
      (root_X_pow_sub_C_pow n a)
  · rw [eq_top_iff, ← AdjoinRoot.adjoinRoot_eq_top]
    apply Algebra.adjoin_mono
    have := ne_zero_of_irreducible_X_pow_sub_C H
    rw [Set.singleton_subset_iff, mem_rootSet_of_ne (X_pow_sub_C_ne_zero
      (Nat.pos_of_ne_zero this) a), aeval_def, AdjoinRoot.algebraMap_eq, AdjoinRoot.eval₂_root]


noncomputable
def adjoinRootXPowSubCEquiv (α : L) (hα : α ^ n = algebraMap K L a) :
    K[n√a] ≃ₐ[K] L :=
  AlgEquiv.ofBijective (AdjoinRoot.liftHom (X ^ n - C a) α (by simp [hα])) <| by
    haveI := Fact.mk H
    haveI := isSplittingField_AdjoinRoot_X_pow_sub_C hζ H
    refine ⟨(AlgHom.toRingHom _).injective, ?_⟩
    rw [← Algebra.range_top_iff_surjective, ← IsSplittingField.adjoin_rootSet _ (X ^ n - C a),
      eq_comm, adjoin_rootSet_eq_range, IsSplittingField.adjoin_rootSet]
    exact IsSplittingField.splits _ _

lemma adjoinRootXPowSubCEquiv_root (α : L) (hα : α ^ n = algebraMap K L a) :
    adjoinRootXPowSubCEquiv hζ H α hα (root _) = α := by
  rw [adjoinRootXPowSubCEquiv, AlgEquiv.coe_ofBijective, liftHom_root]

lemma adjoinRootXPowSubCEquiv_symm_eq_root (α : L) (hα : α ^ n = algebraMap K L a) :
    (adjoinRootXPowSubCEquiv hζ H α hα).symm α = root _ := by
  apply (adjoinRootXPowSubCEquiv hζ H α hα).injective
  rw [(adjoinRootXPowSubCEquiv hζ H α hα).apply_symm_apply, adjoinRootXPowSubCEquiv_root]

lemma adjoin_root_eq_top_of_isSplittingField (α : L) (hα : α ^ n = algebraMap K L a) :
    Algebra.adjoin K {α} = ⊤ := by
  apply Subalgebra.map_injective (f := (adjoinRootXPowSubCEquiv hζ H α hα).symm)
    (adjoinRootXPowSubCEquiv hζ H α hα).symm.injective
  rw [Algebra.map_top, (Algebra.range_top_iff_surjective _).mpr
    (adjoinRootXPowSubCEquiv hζ H α hα).symm.surjective, AlgHom.map_adjoin,
    Set.image_singleton, AlgHom.coe_coe, adjoinRootXPowSubCEquiv_symm_eq_root, adjoinRoot_eq_top]

lemma adjoin_root_eq_top_of_isSplittingField' (α : L) (hα : α ^ n = algebraMap K L a) :
    K⟮α⟯ = ⊤ := by
  refine (IntermediateField.eq_adjoin_of_eq_algebra_adjoin _ _ _ ?_).symm
  exact (adjoin_root_eq_top_of_isSplittingField hζ H α hα).symm

variable (n) (a) (L)

noncomputable
abbrev rootOfSplitsXPowSubC (hn : 0 < n) : L :=
  (rootOfSplits _ (IsSplittingField.splits L (X ^ n - C a))
      (by simpa [degree_X_pow_sub_C hn] using Nat.pos_iff_ne_zero.mp hn))

lemma rootOfSplitsXPowSubC_pow (hn : 0 < n) :
    (rootOfSplitsXPowSubC n a L hn) ^ n = algebraMap K L a := by
  have := map_rootOfSplits _ (IsSplittingField.splits L (X ^ n - C a))
  simp only [eval₂_sub, eval₂_X_pow, eval₂_C, sub_eq_zero] at this
  exact this _

variable {n} {a}

noncomputable
def autEquivRootsOfUnity (hn : 0 < n) :
    (L ≃ₐ[K] L) ≃* (rootsOfUnity ⟨n, hn⟩ K) :=
  (AlgEquiv.autCongr (adjoinRootXPowSubCEquiv hζ H (rootOfSplitsXPowSubC n a L hn)
    (rootOfSplitsXPowSubC_pow n a L hn)).symm).trans (autAdjoinRootXPowSubCEquiv hζ H hn).symm

lemma autEquivRootsOfUnity_apply_rootOfSplit (hn : 0 < n) (e : L ≃ₐ[K] L) :
    e (rootOfSplitsXPowSubC n a L hn) =
      autEquivRootsOfUnity hζ H L hn e • (rootOfSplitsXPowSubC n a L hn) := by
  obtain ⟨η, rfl⟩ := (autEquivRootsOfUnity hζ H L hn).symm.surjective e
  rw [MulEquiv.apply_symm_apply, autEquivRootsOfUnity]
  simp only [MulEquiv.symm_trans_apply, AlgEquiv.autCongr_symm, AlgEquiv.symm_symm,
    MulEquiv.symm_symm, autAdjoinRootXPowSubCEquiv_apply, AlgEquiv.autCongr_apply,
    AlgEquiv.trans_apply, adjoinRootXPowSubCEquiv_symm_eq_root, adjoinRootXPowSubCEquiv_root,
    autAdjoinRootXPowSubC_root, AlgEquiv.map_smul]
  rfl

lemma autEquivRootsOfUnity_smul (hn : 0 < n) (e : L ≃ₐ[K] L)
    (α : L) (hα : α ^ n = algebraMap K L a) :
    autEquivRootsOfUnity hζ H L hn e • α = e α := by
  have ⟨ζ, hζ'⟩ := hζ
  rw [mem_primitiveRoots hn] at hζ'
  have := nthRoots_eq_of_isPrimitiveRoot hn (hζ'.map_of_injective (algebraMap K L).injective)
    (rootOfSplitsXPowSubC_pow n a L hn)
  rw [← mem_nthRoots hn] at hα
  simp only [this, Finset.range_val, Multiset.mem_map, Multiset.mem_range] at hα
  obtain ⟨i, _, rfl⟩ := hα
  simp only [map_mul, ← map_pow, ← Algebra.smul_def, AlgEquiv.map_smul,
    autEquivRootsOfUnity_apply_rootOfSplit hζ H L]
  exact smul_comm _ _ _

lemma ext_of_isSplittingField_X_pow_sub_C (e₁ e₂ : L ≃ₐ[K] L)
    (α : L) (hα : α ^ n = algebraMap K L a) (h : e₁ α = e₂ α) : e₁ = e₂ := by
  have hn := Nat.pos_of_ne_zero (ne_zero_of_irreducible_X_pow_sub_C H)
  apply (autEquivRootsOfUnity hζ H L hn).injective
  by_cases hn' : n = 1
  · subst hn'
    apply (config := {allowSynthFailures := true }) Subsingleton.elim
    exact ⟨fun a b ↦ by simpa using a.prop.trans b.prop.symm⟩
  simp_rw [← autEquivRootsOfUnity_smul hζ H L hn _ α hα, Subgroup.smul_def] at h
  have : α ≠ 0
  · rintro rfl
    apply ne_zero_of_irreducible_X_pow_sub_C' hn' H
    rwa [zero_pow hn, eq_comm, map_eq_zero_iff _ (algebraMap K L).injective] at hα
  ext
  exact smul_left_injective _ this h

noncomputable
def autEquivZmod {ζ : K} (hζ : IsPrimitiveRoot ζ n) :
    (L ≃ₐ[K] L) ≃* Multiplicative (ZMod n) :=
  haveI hn := Nat.pos_iff_ne_zero.mpr (ne_zero_of_irreducible_X_pow_sub_C H)
  (autEquivRootsOfUnity ⟨ζ, (mem_primitiveRoots hn).mpr hζ⟩ H L hn).trans
    ((MulEquiv.subgroupCongr (IsPrimitiveRoot.zpowers_eq (k := ⟨n, hn⟩)
      (hζ.isUnit_unit' hn)).symm).trans (AddEquiv.toMultiplicative'
        (hζ.isUnit_unit' hn).zmodEquivZPowers.symm))

lemma MulEquiv.subgroupCongr_apply {G} [Group G] {H₁ H₂ : Subgroup G} (e : H₁ = H₂) (x) :
  (MulEquiv.subgroupCongr e x : G) = x := rfl

lemma MulEquiv.subgroupCongr_symm_apply {G} [Group G] {H₁ H₂ : Subgroup G} (e : H₁ = H₂) (x) :
  ((MulEquiv.subgroupCongr e).symm x : G) = x := rfl

lemma autEquivZmod_symm_apply {ζ : K} (hζ : IsPrimitiveRoot ζ n)
    (α : L) (hα : α ^ n = algebraMap K L a) (m : ℤ) :
    (autEquivZmod H L hζ).symm (Multiplicative.ofAdd (m : ZMod n)) α = ζ ^ m • α := by
  haveI hn := Nat.pos_iff_ne_zero.mpr (ne_zero_of_irreducible_X_pow_sub_C H)
  rw [← autEquivRootsOfUnity_smul ⟨ζ, (mem_primitiveRoots hn).mpr hζ⟩ H L hn _ α hα]
  simp [MulEquiv.subgroupCongr_symm_apply, Subgroup.smul_def, Units.smul_def, autEquivZmod]

lemma isCyclic_of_isSplittingField_X_pow_sub_C : IsCyclic (L ≃ₐ[K] L) :=
  haveI hn := Nat.pos_iff_ne_zero.mpr (ne_zero_of_irreducible_X_pow_sub_C H)
  isCyclic_of_surjective _
    (autEquivZmod H _ <| (mem_primitiveRoots hn).mp hζ.choose_spec).symm.surjective

lemma isGalois_of_isSplittingField_X_pow_sub_C : IsGalois K L :=
  IsGalois.of_separable_splitting_field (separable_X_pow_sub_C_of_irreducible n hζ a H)

lemma finrank_of_isSplittingField_X_pow_sub_C : FiniteDimensional.finrank K L = n := by
  have := Polynomial.IsSplittingField.finiteDimensional L (X ^ n - C a)
  have := isGalois_of_isSplittingField_X_pow_sub_C hζ H L
  have hn := Nat.pos_iff_ne_zero.mpr (ne_zero_of_irreducible_X_pow_sub_C H)
  have : NeZero n := ⟨ne_zero_of_irreducible_X_pow_sub_C H⟩
  rw [← IsGalois.card_aut_eq_finrank, Fintype.card_congr ((autEquivZmod H L <|
    (mem_primitiveRoots hn).mp hζ.choose_spec).toEquiv.trans Multiplicative.toAdd), ZMod.card]

end IsSplittingField

section IsCyclic

variable {L} [Field L] [Algebra K L] [IsGalois K L] [FiniteDimensional K L] [IsCyclic (L ≃ₐ[K] L)]
variable (hK : (primitiveRoots (FiniteDimensional.finrank K L) K).Nonempty)

open BigOperators

/-- The minimal polynomial (over `K`) of `σ : Gal(L/K)` is `X ^ (orderOf σ) - 1`. -/
lemma minpoly_algEquiv_toLinearMap (σ : L ≃ₐ[K] L) :
    minpoly K σ.toLinearMap = X ^ (orderOf σ) - C 1 := by
  apply eq_of_monic_of_associated (minpoly.monic (LinearMap.isIntegral _))
    (monic_X_pow_sub_C _ (orderOf_pos σ).ne.symm)
  -- First of all, the minimal polynomial divides `X ^ (orderOf σ) - 1`.
  have H : minpoly K σ.toLinearMap ∣ X ^ (orderOf σ) - C 1
  · refine minpoly.dvd _ _ ?_
    simp only [map_one, aeval_def, eval₂_sub, eval₂_X_pow, eval₂_one]
    rw [← AlgEquiv.pow_toLinearMap, pow_orderOf_eq_one, AlgEquiv.one_toLinearMap, sub_self]
  refine Polynomial.associated_of_dvd_of_natDegree_eq H ?_ (X_pow_sub_C_ne_zero (orderOf_pos σ) _)
  apply (natDegree_le_of_dvd H (X_pow_sub_C_ne_zero (orderOf_pos σ) _)).antisymm
  -- It suffices to show that the degree of the minimal polynomial is at most `orderOf σ`.
  rw [natDegree_X_pow_sub_C, ← not_lt]
  intro H
  -- Suppose not, we will obtain a nontrivial linear relation between `{ σⁱ }` (that are distinct).
  have : ∑ i : Fin (orderOf σ), coeff (minpoly K σ.toLinearMap) i • (σ ^ (i : ℕ)).toLinearMap = 0
  · simp_rw [AlgEquiv.pow_toLinearMap]
    rw [Fin.sum_univ_eq_sum_range (fun i ↦ coeff (minpoly K σ.toLinearMap) i • σ.toLinearMap ^ i),
      ← aeval_eq_sum_range' H, minpoly.aeval]
  refine minpoly.ne_zero σ.toLinearMap.isIntegral ?_
  -- However `{ σⁱ }` are linear independent (via Dedekind's linear independence of characters).
  have := Fintype.linearIndependent_iff.mp
    ((linearIndependent_algEquiv_toLinearMap K L).comp _
      (Subtype.val_injective.comp ((finEquivPowers σ (isOfFinOrder_of_finite σ)).injective)))
    ((minpoly K σ.toLinearMap).coeff ∘ (↑)) this ⟨_, H⟩
  simpa using this

open FiniteDimensional
variable (K L)

lemma exists_root_adjoin_eq_top_of_isCyclic :
    ∃ (α : L), α ^ (finrank K L) ∈ Set.range (algebraMap K L) ∧ K⟮α⟯ = ⊤ := by
  -- Let `ζ` be an `n`-th root of unity, and `σ` be a generator of `L ≃ₐ[K] L`.
  have ⟨ζ, hζ⟩ := hK
  rw [mem_primitiveRoots finrank_pos] at hζ
  obtain ⟨σ, hσ⟩ := ‹IsCyclic (L ≃ₐ[K] L)›
  have hσ' := orderOf_eq_card_of_forall_mem_zpowers hσ
  -- Since the minimal polynomial of `σ` over `K` is `Xⁿ - 1`,
  -- `σ` has an eigenvector `v` with eigenvalue `ζ`.
  have : IsRoot (minpoly K σ.toLinearMap) ζ := by simpa [minpoly_algEquiv_toLinearMap, hσ',
    sub_eq_zero, IsGalois.card_aut_eq_finrank] using hζ.pow_eq_one
  obtain ⟨v, hv⟩ := (Module.End.hasEigenvalue_of_isRoot this).exists_hasEigenvector
  have hv' := hv.pow_apply
  simp_rw [← AlgEquiv.pow_toLinearMap, AlgEquiv.toLinearMap_apply] at hv'
  -- We claim that `v` is the desired root.
  refine ⟨v, ?_, ?_⟩
  · -- Since `v ^ n` is fixed by `σ` (`σ (v ^ n) = ζ ^ n • v ^ n = v ^ n`), it is in `K`.
    rw [← IntermediateField.mem_bot,
      ← OrderIso.map_bot IsGalois.intermediateFieldEquivSubgroup.symm]
    intro ⟨σ', hσ'⟩
    obtain ⟨n, rfl : σ ^ n = σ'⟩ := mem_powers_iff_mem_zpowers.mpr (hσ σ')
    rw [smul_pow', Submonoid.smul_def, AlgEquiv.smul_def, hv', smul_pow, ← pow_mul,
      mul_comm, pow_mul, hζ.pow_eq_one, one_pow, one_smul]
  · -- Since `σ` does not fix `K⟮α⟯`, `K⟮α⟯` is `L`.
    apply IsGalois.intermediateFieldEquivSubgroup.injective
    rw [map_top, eq_top_iff]
    intros σ' hσ'
    obtain ⟨n, rfl : σ ^ n = σ'⟩ := mem_powers_iff_mem_zpowers.mpr (hσ σ')
    have := hσ' ⟨v, IntermediateField.mem_adjoin_simple_self K v⟩
    simp only [AlgEquiv.smul_def, hv'] at this
    conv_rhs at this => rw [← one_smul K v]
    obtain ⟨k, rfl⟩ := hζ.dvd_of_pow_eq_one n (smul_left_injective K hv.2 this)
    rw [pow_mul, ← IsGalois.card_aut_eq_finrank, pow_card_eq_one, one_pow]
    exact one_mem _

variable {K L}

lemma irreducible_X_pow_sub_C_of_root_adjoin_eq_top
    {a : K} {α : L} (ha : α ^ (finrank K L) = algebraMap K L a) (hα : K⟮α⟯ = ⊤) :
    Irreducible (X ^ (finrank K L) - C a) := by
  have : minpoly K α = X ^ (finrank K L) - C a
  · apply eq_of_monic_of_associated (minpoly.monic (IsIntegral.of_finite K α))
      (monic_X_pow_sub_C _ finrank_pos.ne.symm)
    refine Polynomial.associated_of_dvd_of_natDegree_eq ?_ ?_
      (X_pow_sub_C_ne_zero finrank_pos _)
    · refine minpoly.dvd _ _ ?_
      simp only [aeval_def, eval₂_sub, eval₂_X_pow, ha, eval₂_C, sub_self]
    · rw [← IntermediateField.adjoin.finrank (IsIntegral.of_finite K α), hα, natDegree_X_pow_sub_C]
      exact finrank_top K L
  exact this ▸ minpoly.irreducible (IsIntegral.of_finite K α)

lemma isSplittingField_X_pow_sub_C_of_root_adjoin_eq_top
    {a : K} {α : L} (ha : α ^ (finrank K L) = algebraMap K L a) (hα : K⟮α⟯ = ⊤) :
    IsSplittingField K L (X ^ (finrank K L) - C a) := by
  constructor
  · rw [← splits_id_iff_splits, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_C,
      Polynomial.map_X]
    have ⟨_, hζ⟩ := hK
    rw [mem_primitiveRoots finrank_pos] at hζ
    exact X_pow_sub_C_splits_of_isPrimitiveRoot (hζ.map_of_injective (algebraMap K _).injective) ha
  · rw [eq_top_iff, ← IntermediateField.top_toSubalgebra, ← hα,
      IntermediateField.adjoin_simple_toSubalgebra_of_integral (IsIntegral.of_finite K α)]
    apply Algebra.adjoin_mono
    rw [Set.singleton_subset_iff, mem_rootSet_of_ne (X_pow_sub_C_ne_zero finrank_pos a),
      aeval_def, eval₂_sub, eval₂_X_pow, eval₂_C, ha, sub_self]

end IsCyclic

open FiniteDimensional in
/--
Suppose `L/K` is a finite extension of dimension `n`, and `K` contains all `n`-th roots of unity.
Then `L/K` is cyclic iff
`L` is a splitting field of some irreducible polynomial of the form `Xⁿ - a : K[X]` iff
`L = K[α]` for some `αⁿ ∈ K`.
-/
lemma isCyclic_tfae (K L) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (hK : (primitiveRoots (FiniteDimensional.finrank K L) K).Nonempty) :
    List.TFAE [
      IsGalois K L ∧ IsCyclic (L ≃ₐ[K] L),
      ∃ a : K, Irreducible (X ^ (finrank K L) - C a) ∧
        IsSplittingField K L (X ^ (finrank K L) - C a),
      ∃ (α : L), α ^ (finrank K L) ∈ Set.range (algebraMap K L) ∧ K⟮α⟯ = ⊤] := by
  tfae_have 1 → 3
  · intro ⟨inst₁, inst₂⟩
    exact exists_root_adjoin_eq_top_of_isCyclic K L hK
  tfae_have 3 → 2
  · intro ⟨α, ⟨a, ha⟩, hα⟩
    exact ⟨a, irreducible_X_pow_sub_C_of_root_adjoin_eq_top ha.symm hα,
      isSplittingField_X_pow_sub_C_of_root_adjoin_eq_top hK ha.symm hα⟩
  tfae_have 2 → 1
  · intro ⟨a, H, inst⟩
    exact ⟨isGalois_of_isSplittingField_X_pow_sub_C hK H L,
      isCyclic_of_isSplittingField_X_pow_sub_C hK H L⟩
  tfae_finish
