import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.Data.Set.Card
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.RingTheory.DedekindDomain.Ideal

/-!
# Galois action on primes

## Main Definition
- `galRestrict`: The restriction of `Gal(L/K)` into `Aut(B/A)`.

## Main Result
- `exists_comap_galRestrict_eq`: The galois action on `primesOver` is transitive.
- `Ideal.ramificationIdxIn_mul_inertiaDegIn_mul_ncard_primesOver`: `e * f * g = [L : K]`.
- `prod_primesOverFinset_pow_ramificationIdxIn`: `(∏_P P) ^ e = p`
- `prod_smul_primesOver`: `∏_σ σ • P = p ^ f`

-/
open BigOperators UniqueFactorizationMonoid Ideal

section primesOver
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

lemma ne_bot_of_mem_primesOver [IsDedekindDomain S] [NoZeroSMulDivisors R S] {p : Ideal R}
    (hp : p ≠ ⊥) {P : Ideal S} (hP : P ∈ primesOver p S) :
    P ≠ ⊥ := by
  have :  P.LiesOver p := hP.2
  exact Ideal.ne_bot_of_liesOver_of_ne_bot hp _

lemma isMaximal_of_mem_primesOver [IsDedekindDomain S] [NoZeroSMulDivisors R S] {p : Ideal R}
    (hp : p ≠ ⊥) {P : Ideal S} (hP : P ∈ primesOver p S) :
    P.IsMaximal :=
  hP.1.isMaximal (ne_bot_of_mem_primesOver hp hP)

lemma prime_of_mem_primesOver [IsDedekindDomain S] [NoZeroSMulDivisors R S] {p : Ideal R}
    (hp : p ≠ ⊥) {P : Ideal S} (hP : P ∈ primesOver p S) :
    Prime P := prime_of_isPrime (ne_bot_of_mem_primesOver hp hP) hP.1

end primesOver

variable (R K L S : Type*) [CommRing R] [CommRing S] [Algebra R S] [Field K] [Field L]
    [Algebra R K] [IsFractionRing R K] [Algebra S L]
    [Algebra K L] [Algebra R L] [IsScalarTower R S L] [IsScalarTower R K L]
    [IsIntegralClosure S R L] [FiniteDimensional K L]

lemma prod_galRestrictHom_eq_norm [IsDedekindDomain R] [IsGalois K L] (x) :
    (∏ σ : L ≃ₐ[K] L, galRestrictHom R K L S σ x) =
    algebraMap R S (IsIntegralClosure.mk' (R := R) R (Algebra.norm K <| algebraMap S L x)
      (Algebra.isIntegral_norm K (IsIntegralClosure.isIntegral R L x).algebraMap)) :=
  prod_galRestrict_eq_norm ..

noncomputable
instance (p : Ideal R) : MulAction (L ≃ₐ[K] L) (primesOver p S) where
  smul := fun σ P ↦ ⟨comap (galRestrict R K L S σ⁻¹) P, P.2.1.comap _, ⟨by
    rw [← comap_coe (galRestrict R K L S _), under, comap_comap,
      ← AlgEquiv.toAlgHom_toRingHom, AlgHom.comp_algebraMap]
    exact P.2.2.1⟩⟩
  one_smul := by
    intro p
    ext1
    show comap _ _ = _
    rw [inv_one, map_one]
    rfl
  mul_smul := by
    intro σ₁ σ₂ p
    ext1
    show comap _ _ = comap _ (comap _ _)
    rw [← comap_coe (galRestrict R K L S _), ← comap_coe (galRestrict R K L S _),
      ← comap_coe (galRestrict R K L S _), comap_comap, mul_inv_rev, _root_.map_mul]
    rfl

-- lemma coe_smul_primesOver {p : Ideal R} (σ : L ≃ₐ[K] L) (P : primesOver p S) :
--   (↑(σ • P) : Ideal S) = comap (galRestrict R K L S σ⁻¹) P := rfl

open BigOperators

instance [IsDedekindDomain R] [IsGalois K L] (p : Ideal R) :
    MulAction.IsPretransitive (L ≃ₐ[K] L) (primesOver p S) := by
  -- Set up instances.
  have : IsDomain S :=
    (IsIntegralClosure.equiv R S L (integralClosure R L)).toMulEquiv.isDomain (integralClosure R L)
  have := IsIntegralClosure.isDedekindDomain R K L S
  have hRS : Function.Injective (algebraMap R S) := by
    refine Function.Injective.of_comp (f := algebraMap S L) ?_
    rw [← RingHom.coe_comp, ← IsScalarTower.algebraMap_eq, IsScalarTower.algebraMap_eq R K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective _ _)
  rw [← NoZeroSMulDivisors.iff_algebraMap_injective] at hRS
  -- Given `P` and `Q` over `p`, we ought to show that `σ • P = Q` for some `σ`.
  constructor
  intros P Q
  -- We first rule out the trivial case where `p = ⊥`.
  by_cases hp : p = ⊥
  · subst hp
    have : Subsingleton (primesOver (⊥ : Ideal R) S) := by
      have : Algebra.IsIntegral R S := (IsIntegralClosure.isIntegral_algebra R L)
      rw [primesOver_bot]; infer_instance
    exact ⟨1, Subsingleton.elim _ _⟩
  have hP := isMaximal_of_mem_primesOver hp P.prop
  -- Suppose the contrary that `σ • P ≠ Q` for all `σ`.
  by_contra H
  push_neg at H
  -- Then `I := ∏ σ • Q` is coprime to `P`.
  let I := ∏ σ : L ≃ₐ[K] L, (↑(σ • Q) : Ideal S)
  have : I ⊔ ↑P = ⊤ := by
    by_contra h
    have := hP.eq_of_le h le_sup_right
    rw [right_eq_sup, ← dvd_iff_le,
      (prime_of_mem_primesOver hp P.prop).dvd_finset_prod_iff] at this
    obtain ⟨σ, _, hσ⟩ := this
    apply H (σ⁻¹)
    rw [inv_smul_eq_iff]
    ext1
    exact ((isMaximal_of_mem_primesOver hp (σ • Q).prop).eq_of_le hP.ne_top (dvd_iff_le.mp hσ)).symm
  rw [eq_top_iff_one, Submodule.mem_sup] at this
  -- In particular we may find some `x ∈ I` and `y ∈ p` such that `x + y = 1`.
  have ⟨x, hx, y, hy, hxy⟩ := this
  have hQ := Q.prop.1
  -- Then `σ y ∉ Q` for all `σ`, or else `1 = x + y ∈ σ⁻¹ • Q`.
  -- This implies that `∏ σ y ∉ Q`.
  have : ∏ σ : L ≃ₐ[K] L, galRestrictHom R K L S σ y ∉ (Q : Ideal S) := by
    apply prod_mem (S := (Q : Ideal S).primeCompl)
    intro σ _ hσ
    apply (isMaximal_of_mem_primesOver hp (σ⁻¹ • Q).prop).ne_top
    rw [eq_top_iff_one, ← hxy]
    apply add_mem
    · suffices ↑(σ⁻¹ • Q) ∣ I from (dvd_iff_le.mp this) hx
      exact Finset.dvd_prod_of_mem _ (Finset.mem_univ _)
    · show galRestrictHom R K L S ↑(σ⁻¹⁻¹) y ∈ (Q : Ideal S)
      rwa [inv_inv]
  -- OTOH we show that `∏ σ y ∈ Q`.
  -- Since `∏ σ y` is the norm of `y ∈ P`, it falls in `R ∩ Q = p = R ∩ P` as desired.
  apply this
  have hQ := Q.prop.2.1
  have hP := P.prop.2.1
  rw [under_def] at hQ hP
  rw [prod_galRestrictHom_eq_norm, ← mem_comap, ← hQ, hP, mem_comap, ← prod_galRestrictHom_eq_norm]
  rw [← SetLike.mem_coe, ← Set.singleton_subset_iff, ← span_le] at hy
  apply hy
  rw [mem_span_singleton]
  refine dvd_trans ?_ (Finset.dvd_prod_of_mem _ (Finset.mem_univ 1))
  show y ∣ galRestrictHom R K L S 1 y
  rw [map_one]
  exact dvd_rfl
  -- Which gives a contradiction and hence there is some `σ` such that `σ • P = Q`.

lemma exists_comap_galRestrict_eq [IsDedekindDomain R] [IsGalois K L] {p : Ideal R}
    {P₁ P₂ : Ideal S} (hP₁ : P₁ ∈ primesOver p S) (hP₂ : P₂ ∈ primesOver p S) :
    ∃ σ, P₁.comap (galRestrict R K L S σ) = P₂ :=
⟨_, congr_arg Subtype.val (MulAction.exists_smul_eq (L ≃ₐ[K] L)
  (⟨P₁, hP₁⟩ : primesOver p S) ⟨P₂, hP₂⟩).choose_spec⟩

-- variable {R}

-- open scoped Classical in
-- noncomputable
-- def Ideal.ramificationIdxIn (p : Ideal R) : ℕ :=
--   if h : (primesOver p S).Nonempty then
--     ramificationIdx (algebraMap R S) p h.choose else 0

-- open scoped Classical in
-- noncomputable
-- def Ideal.inertiaDegIn (p : Ideal R) [p.IsMaximal] : ℕ :=
--   if h : (primesOver p S).Nonempty then inertiaDeg p h.choose else 0
--
-- variable (R)
--
-- lemma Ideal.ramificationIdxIn_bot : (⊥ : Ideal R).ramificationIdxIn S = 0 := by
--   delta ramificationIdxIn
--   by_cases h : (primesOver (⊥ : Ideal R) S).Nonempty
--   · rw [dif_pos h, ramificationIdx_bot]
--   · exact dif_neg h
--
-- lemma Ideal.inertiaDegIn_bot [Nontrivial R] [IsDomain S] [NoZeroSMulDivisors R S] [IsNoetherian R S]
--     [Algebra.IsIntegral R S] [H : (⊥ : Ideal R).IsMaximal] :
--     (⊥ : Ideal R).inertiaDegIn S = Module.finrank R S := by
--   dsimp [inertiaDegIn]
--   rw [primesOver_bot]
--   have : ({⊥} : Set (Ideal S)).Nonempty := by simp
--   rw [dif_pos this, this.choose_spec]
--   have hR := not_imp_not.mp (Ring.ne_bot_of_isMaximal_of_not_isField H) rfl
--   have hS := isField_of_isIntegral_of_isField' (S := S) hR
--   letI : Field R := hR.toField
--   letI : Field S := hS.toField
--   rw [← map_bot (f := algebraMap R S), ← finrank_quotient_map (R := R) (S := S) ⊥ R S]
--   convert inertiaDeg_algebraMap _ _
--   simp only [map_bot]
--   exact ⟨(comap_bot_of_injective _
--     (NoZeroSMulDivisors.iff_algebraMap_injective.1 inferInstance)).symm⟩
--
-- variable {S}
--
-- variable [IsDedekindDomain R]
--
-- lemma Ideal.ramificationIdxIn_eq_ramificationIdx [IsGalois K L] (p : Ideal R) (P : Ideal S)
--     (hP : P ∈ primesOver p S) :
--     p.ramificationIdxIn S = ramificationIdx (algebraMap R S) p P := by
--   delta ramificationIdxIn
--   have : (primesOver p S).Nonempty := ⟨P, hP⟩
--   rw [dif_pos this]
--   have ⟨σ, hσ⟩ := exists_comap_galRestrict_eq R K L S hP this.choose_spec
--   rw [← hσ]
--   exact ramificationIdx_comap_eq _ (galRestrict R K L S σ) P
--
-- lemma Ideal.inertiaDegIn_eq_inertiaDeg [IsGalois K L] (p : Ideal R) (P : Ideal S)
--     (hP : P ∈ primesOver p S) [p.IsMaximal] :
--     p.inertiaDegIn S = inertiaDeg p P := by
--   delta inertiaDegIn
--   have : (primesOver p S).Nonempty := ⟨P, hP⟩
--   rw [dif_pos this]
--   have ⟨σ, hσ⟩ := exists_comap_galRestrict_eq R K L S hP this.choose_spec
--   rw [← hσ]
--   exact inertiaDeg_comap_eq p (galRestrict R K L S σ) P
--
-- open Module
--
-- lemma Ideal.ramificationIdxIn_mul_inertiaDegIn_mul_ncard_primesOver
--     [IsGalois K L] (p : Ideal R) (hp : p ≠ ⊥) [p.IsMaximal] :
--     p.ramificationIdxIn S * p.inertiaDegIn S * (primesOver p S).ncard = finrank K L := by
--   classical
--   have : IsDomain S :=
--     (IsIntegralClosure.equiv R S L (integralClosure R L)).toMulEquiv.isDomain (integralClosure R L)
--   have := IsIntegralClosure.isDedekindDomain R K L S
--   have := IsIntegralClosure.isFractionRing_of_finite_extension R K L S
--   have := IsIntegralClosure.isNoetherian R K L S
--   have hRS : Function.Injective (algebraMap R S) := by
--     refine Function.Injective.of_comp (f := algebraMap S L) ?_
--     rw [← RingHom.coe_comp, ← IsScalarTower.algebraMap_eq, IsScalarTower.algebraMap_eq R K L]
--     exact (algebraMap K L).injective.comp (IsFractionRing.injective _ _)
--   rw [← NoZeroSMulDivisors.iff_algebraMap_injective] at hRS
--   rw [← sum_ramification_inertia (S := S) p K L hp, ← coe_primesOverFinset hp,
--     Set.ncard_coe_Finset, mul_comm, ← smul_eq_mul, ← Finset.sum_const]
--   apply Finset.sum_congr rfl
--   simp_rw [← Finset.mem_coe, coe_primesOverFinset hp]
--   intro P hP
--   rw [ramificationIdxIn_eq_ramificationIdx K L p P hP, inertiaDegIn_eq_inertiaDeg K L p P hP]
--
-- open scoped Classical in
-- lemma ramificationIdxIn_smul_primesOverFinset [IsDedekindDomain S]
--     [IsGalois K L] (p : Ideal R) [p.IsPrime] :
--     (p.ramificationIdxIn S) • (primesOverFinset p S).val = factors (p.map (algebraMap R S)) := by
--   have hRS : Function.Injective (algebraMap R S) := by
--     refine Function.Injective.of_comp (f := algebraMap S L) ?_
--     rw [← RingHom.coe_comp, ← IsScalarTower.algebraMap_eq, IsScalarTower.algebraMap_eq R K L]
--     exact (algebraMap K L).injective.comp (IsFractionRing.injective _ _)
--   rw [← NoZeroSMulDivisors.iff_algebraMap_injective] at hRS
--   by_cases hp : p = ⊥
--   · subst hp
--     rw [ramificationIdxIn_bot, zero_smul, Ideal.map_bot]
--     exact factors_zero.symm
--   ext P
--   by_cases hP : P ∈ primesOverFinset p S; swap
--   · rw [Multiset.count_nsmul, Multiset.count_eq_zero_of_not_mem hP, mul_zero,
--       Multiset.count_eq_zero_of_not_mem]
--     rwa [primesOverFinset, Multiset.mem_toFinset] at hP
--   have hP' := hP
--   rw [primesOverFinset, Multiset.mem_toFinset] at hP
--   have : p.IsMaximal := Ring.DimensionLEOne.maximalOfPrime hp ‹_›
--   rw [← Finset.mem_coe, coe_primesOverFinset hp] at hP'
--   rw [ramificationIdxIn_eq_ramificationIdx K L p P hP', Multiset.count_nsmul,
--     IsDedekindDomain.ramificationIdx_eq_factors_count _ hP'.1
--     (ne_bot_of_mem_primesOver hp hP'), primesOverFinset,
--     Multiset.toFinset_val, Multiset.count_dedup, if_pos hP, mul_one]
--   rwa [Ne, map_eq_bot_iff_of_injective (NoZeroSMulDivisors.algebraMap_injective _ _)]
--
-- lemma prod_primesOverFinset_pow_ramificationIdxIn [IsDedekindDomain S] [IsGalois K L] (p : Ideal R)
--     (hp : p ≠ ⊥) [p.IsMaximal] :
--     (∏ P in primesOverFinset p S, P) ^ p.ramificationIdxIn S = p.map (algebraMap R S) := by
--   classical
--   have hRS : Function.Injective (algebraMap R S) := by
--     refine Function.Injective.of_comp (f := algebraMap S L) ?_
--     rw [← RingHom.coe_comp, ← IsScalarTower.algebraMap_eq, IsScalarTower.algebraMap_eq R K L]
--     exact (algebraMap K L).injective.comp (IsFractionRing.injective _ _)
--   delta Finset.prod
--   rw [Multiset.map_id', ← Multiset.prod_nsmul, ← associated_iff_eq,
--     ramificationIdxIn_smul_primesOverFinset K L]
--   apply factors_prod
--   rwa [Ne, zero_eq_bot, map_eq_bot_iff_of_injective hRS]
--
-- lemma prod_smul_primesOver [IsGalois K L] (p : Ideal R) (P : primesOver p S) [p.IsMaximal] :
--     ∏ σ : L ≃ₐ[K] L, (↑(σ • P) : Ideal S) = (p.map (algebraMap R S)) ^ (p.inertiaDegIn S) := by
--   classical
--   have : IsDomain S :=
--     (IsIntegralClosure.equiv R S L (integralClosure R L)).toMulEquiv.isDomain (integralClosure R L)
--   have := IsIntegralClosure.isDedekindDomain R K L S
--   have hRS : Function.Injective (algebraMap R S) := by
--     refine Function.Injective.of_comp (f := algebraMap S L) ?_
--     rw [← RingHom.coe_comp, ← IsScalarTower.algebraMap_eq, IsScalarTower.algebraMap_eq R K L]
--     exact (algebraMap K L).injective.comp (IsFractionRing.injective _ _)
--   rw [← NoZeroSMulDivisors.iff_algebraMap_injective] at hRS
--   have := IsIntegralClosure.isNoetherian R K L S
--   by_cases hp : p = ⊥
--   · subst hp
--     have := P.prop
--     have hRS : Algebra.IsIntegral R S := IsIntegralClosure.isIntegral_algebra R L
--     simp_rw [primesOver_bot R S,
--       Set.mem_singleton_iff] at this
--     simp_rw [coe_smul_primesOver, this,
--       comap_bot_of_injective _ (galRestrict R K L S _).injective, Finset.prod_const,
--       Ideal.map_bot, inertiaDegIn_bot R S]
--     refine (zero_pow ?_).trans (zero_pow ?_).symm
--     · rw [Finset.card_univ, Ne, Fintype.card_eq_zero_iff]
--       simp only [not_isEmpty_of_nonempty, not_false_eq_true]
--     · have hR := not_imp_not.mp (Ring.ne_bot_of_isMaximal_of_not_isField ‹_›) rfl
--       letI : Field R := hR.toField
--       exact finrank_pos.ne'
--   rw [← prod_primesOverFinset_pow_ramificationIdxIn K L p hp]
--   delta Finset.prod
--   rw [← pow_mul, ← Multiset.prod_nsmul, Multiset.map_id']
--   congr
--   ext P'
--   rw [Multiset.count_nsmul, primesOverFinset, Multiset.toFinset_val, Multiset.count_dedup]
--   simp_rw [← Multiset.mem_toFinset, ← Finset.mem_coe]
--   rw [← primesOverFinset]
--   simp_rw [coe_primesOverFinset hp]
--   by_cases hP' : P' ∈ primesOver p S
--   · rw [if_pos hP', mul_one, Multiset.count_map]
--     have : Fintype (primesOver p S) := (primesOver_finite p S).fintype
--     apply mul_left_injective₀ (Set.ncard_ne_zero_of_mem P.prop)
--     dsimp only
--     rw [ramificationIdxIn_mul_inertiaDegIn_mul_ncard_primesOver K L p hp,
--       ← IsGalois.card_aut_eq_finrank, ← MulAction.card_orbit_mul_card_stabilizer_eq_card_group
--         (L ≃ₐ[K] L) P, MulAction.orbit_eq_univ, mul_comm]
--     simp only [Fintype.card_ofFinset, Set.mem_univ, Finset.mem_univ, forall_true_left,
--       Subtype.forall, implies_true, forall_const, Finset.filter_true_of_mem,
--       MulAction.mem_stabilizer_iff, Finset.card_univ, ← Set.Nat.card_coe_set_eq,
--       Nat.card_eq_fintype_card]
--     congr 1
--     rw [← Finset.filter_val, ← Finset.card, ← Fintype.card_subtype]
--     obtain ⟨σ, hσ⟩ := MulAction.exists_smul_eq (L ≃ₐ[K] L) P ⟨P', hP'⟩
--     have : P' = ↑(σ • P) := by rw [hσ]
--     simp_rw [this, ← Subtype.ext_iff, ← eq_inv_smul_iff (g := σ), ← mul_smul, eq_comm (a := P)]
--     exact Fintype.card_congr
--       { toFun := fun x ↦ ⟨σ⁻¹ * x, x.prop⟩,
--         invFun := fun x ↦ ⟨σ * x, (inv_mul_cancel_left σ x).symm ▸ x.prop⟩,
--         left_inv := fun x ↦ Subtype.ext (mul_inv_cancel_left σ x),
--         right_inv := fun x ↦ Subtype.ext (inv_mul_cancel_left σ x) }
--   · rw [if_neg hP', mul_zero, Multiset.count_eq_zero]
--     simp only [Multiset.mem_map, Finset.mem_val, Finset.mem_univ, true_and, not_exists]
--     rintro σ rfl
--     exact hP' (σ • P).2
