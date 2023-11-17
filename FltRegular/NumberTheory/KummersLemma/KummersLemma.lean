import FltRegular.NumberTheory.KummersLemma.Field
import FltRegular.NumberTheory.Hilbert92
import FltRegular.NumberTheory.Hilbert90
import FltRegular.NumberTheory.IdealNorm

open scoped NumberField

variable {K : Type*} {p : ℕ+} [hpri : Fact p.Prime] [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable (hp : p ≠ 2) [Fintype (ClassGroup (𝓞 K))] (hreg : (p : ℕ).Coprime <| Fintype.card <| ClassGroup (𝓞 K))

variable {ζ : K} (hζ : IsPrimitiveRoot ζ p) (u : (𝓞 K)ˣ)
  (hcong : (hζ.unit' - 1 : 𝓞 K) ^ (p : ℕ) ∣ (↑u : 𝓞 K) - 1) (hu : ∀ v : K, v ^ (p : ℕ) ≠ u)

attribute [-instance] instCoeOut

open Polynomial

variable {L} [Field L] [Algebra K L] [FiniteDimensional K L]
variable [IsSplittingField K L (X ^ (p : ℕ) - C (u : K))]
variable (σ : L ≃ₐ[K] L) (hσ : ∀ x, x ∈ Subgroup.zpowers σ)

variable {A B} [CommRing A] [CommRing B] [Algebra A B] [Algebra A L] [Algebra A K]
    [Algebra B L] [IsScalarTower A B L] [IsScalarTower A K L] [IsFractionRing A K]
    [IsIntegralClosure B A L]

lemma comap_span_galRestrict_eq_of_cyclic (β : B) (η : Bˣ) (hβ : η * (galRestrict A K B L σ) β = β)
    (σ' : L ≃ₐ[K] L) :
    (Ideal.span {β}).comap (galRestrict A K B L σ') = Ideal.span {β} := by
  suffices : (Ideal.span {β}).map
      (galRestrict A K B L σ'⁻¹).toRingEquiv.toRingHom = Ideal.span {β}
  · rwa [RingEquiv.toRingHom_eq_coe, Ideal.map_comap_of_equiv, map_inv] at this
  apply_fun (Ideal.span {·}) at hβ
  rw [← Ideal.span_singleton_mul_span_singleton, Ideal.span_singleton_eq_top.mpr η.isUnit,
    ← Ideal.one_eq_top, one_mul, ← Set.image_singleton, ← Ideal.map_span] at hβ
  change Ideal.map (galRestrict A K B L σ : B →+* B) _ = _ at hβ
  generalize σ'⁻¹ = σ'
  obtain ⟨n, rfl : σ ^ n = σ'⟩ := mem_powers_iff_mem_zpowers.mpr (hσ σ')
  rw [map_pow]
  induction n with
  | zero =>
    simp only [Nat.zero_eq, pow_zero, AlgEquiv.toRingEquiv_eq_coe, RingEquiv.toRingHom_eq_coe]
    exact Ideal.map_id _
  | succ n IH =>
    simp only [AlgEquiv.toRingEquiv_eq_coe, RingEquiv.toRingHom_eq_coe, pow_succ'] at IH ⊢
    conv_lhs at IH => rw [← hβ, Ideal.map_map]
    exact IH

open FiniteDimensional in
theorem exists_units_eq_div_root_of_isUnramified
    [IsDedekindDomain A] [IsUnramified A B] [Fintype (ClassGroup A)]
    (Hp : Nat.Coprime p <| Fintype.card <| ClassGroup A) (η : Bˣ)
    (hη : Algebra.norm K (algebraMap B L η) = 1) :
    ∃ α : Bˣ, algebraMap B L η = (algebraMap B L α) / σ (algebraMap B L α) := by
  haveI := isGalois_of_isSplittingField_X_pow_sub_C ⟨ζ, (mem_primitiveRoots p.pos).mpr hζ⟩
      (X_pow_sub_C_irreducible_of_prime hpri.out hu) L
  obtain ⟨β, hβ_zero, hβ⟩ := Hilbert90_integral (A := A) (B := B) σ hσ η hη
  haveI : IsDomain B :=
    (IsIntegralClosure.equiv A B L (integralClosure A L)).toMulEquiv.isDomain (integralClosure A L)
  haveI := IsIntegralClosure.isNoetherian A K L B
  haveI := IsIntegralClosure.isDedekindDomain A K L B
  haveI := IsIntegralClosure.isFractionRing_of_finite_extension A K L B
  have hAB : Function.Injective (algebraMap A B)
  · refine Function.Injective.of_comp (f := algebraMap B L) ?_
    rw [← RingHom.coe_comp, ← IsScalarTower.algebraMap_eq, IsScalarTower.algebraMap_eq A K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective _ _)
  rw [← NoZeroSMulDivisors.iff_algebraMap_injective] at hAB
  have H : RingHom.comp (algebraMap (FractionRing A) (FractionRing B))
    ↑(FractionRing.algEquiv A K).symm.toRingEquiv =
      RingHom.comp ↑(FractionRing.algEquiv B L).symm.toRingEquiv (algebraMap K L)
  · apply IsLocalization.ringHom_ext (nonZeroDivisors A)
    ext
    simp only [AlgEquiv.toRingEquiv_eq_coe, RingHom.coe_comp, RingHom.coe_coe,
      AlgEquiv.coe_ringEquiv, Function.comp_apply, AlgEquiv.commutes,
      ← IsScalarTower.algebraMap_apply]
    rw [IsScalarTower.algebraMap_apply A B L, AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply]
  have : IsSeparable (FractionRing A) (FractionRing B) := IsSeparable_of_equiv_equiv _ _ H
  have hLK : finrank (FractionRing A) (FractionRing B) = finrank K L :=
    (FiniteDimensional.finrank_of_equiv_equiv _ _ H).symm
  have hβ' := comap_map_eq_of_isUnramified K L _
    (comap_span_galRestrict_eq_of_cyclic σ hσ (A := A) (B := B) β η hβ)
  obtain ⟨⟨γ, hγ : _ = Ideal.span _⟩⟩ : ((Ideal.span {β}).comap (algebraMap A B)).IsPrincipal
  · apply_fun Ideal.spanIntNorm A at hβ'
    rw [Ideal.spanIntNorm_map, Ideal.spanIntNorm_singleton, hLK] at hβ'
    letI : Fact (Nat.Prime p) := hpri
    apply IsPrincipal_of_IsPrincipal_pow_of_Coprime _ p Hp
    rw [← finrank_of_isSplittingField_X_pow_sub_C ⟨ζ, (mem_primitiveRoots p.pos).mpr hζ⟩
      (X_pow_sub_C_irreducible_of_prime hpri.out hu) L, hβ']
    exact ⟨⟨_, rfl⟩⟩
  rw [hγ, Ideal.map_span, Set.image_singleton, Ideal.span_singleton_eq_span_singleton] at hβ'
  obtain ⟨a, rfl⟩ := hβ'
  rw [map_mul, AlgEquiv.commutes, mul_left_comm, (mul_right_injective₀ _).eq_iff] at hβ
  use a
  conv_rhs => enter [1]; rw [← hβ]
  rw [map_mul, ← AlgHom.coe_coe σ, ← algebraMap_galRestrictHom_apply A K B L σ a]
  refine (mul_div_cancel _ ?_).symm
  · rw [ne_eq, (injective_iff_map_eq_zero' _).mp (IsFractionRing.injective B L),
      (injective_iff_map_eq_zero' _).mp (galRestrict A K B L σ).injective]
    exact a.isUnit.ne_zero
  · exact (mul_ne_zero_iff.mp hβ_zero).1

theorem false_of_zeta_sub_one_pow_dvd_sub_one_of_pow_ne (u : (𝓞 K)ˣ)
    (hcong : (hζ.unit' - 1 : 𝓞 K) ^ (p : ℕ) ∣ (↑u : 𝓞 K) - 1)
    (hu : ∀ v : K, v ^ (p : ℕ) ≠ u) : False := by
  letI := Fact.mk (X_pow_sub_C_irreducible_of_prime hpri.out hu)
  let L := AdjoinRoot (Polynomial.X ^ (p : ℕ) - Polynomial.C (u : K))
  haveI := isSplittingField_AdjoinRoot_X_pow_sub_C ⟨ζ, (mem_primitiveRoots p.pos).mpr hζ⟩
    (X_pow_sub_C_irreducible_of_prime hpri.out hu)
  haveI := isGalois_of_isSplittingField_X_pow_sub_C ⟨ζ, (mem_primitiveRoots p.pos).mpr hζ⟩
    (X_pow_sub_C_irreducible_of_prime hpri.out hu) L
  have := Polynomial.IsSplittingField.finiteDimensional L
    (Polynomial.X ^ (p : ℕ) - Polynomial.C (u : K))
  obtain ⟨⟨σ, hσ⟩⟩ :=
    isCyclic_of_isSplittingField_X_pow_sub_C ⟨ζ, (mem_primitiveRoots p.pos).mpr hζ⟩
      (X_pow_sub_C_irreducible_of_prime hpri.out hu) L
  obtain ⟨η, hη, hη'⟩ := Hilbert92 p σ hσ
  haveI := KummersLemma.isUnramified hp hζ u hcong hu L
  obtain ⟨α, hα⟩ :=
    exists_units_eq_div_root_of_isUnramified hζ u hu σ hσ (A := 𝓞 K) (B := 𝓞 L) hreg η hη
  exact hη' α hα

-- Let 𝑝 be a regular prime (i.e. an odd prime which does not divide the class number off
-- the 𝑝-th cyclotomic field) and 𝜉 a primitive 𝑝-th root of unity;
-- if a unit 𝑢∈𝐐(𝜉) is congruent to an integer modulo 𝑝, then 𝑢 is a 𝑝-th power in 𝐐(𝜉).
theorem eq_pow_prime_of_unit_of_congruent (u : (𝓞 K)ˣ)
    (hcong : ∃ n : ℤ, (p : 𝓞 K) ∣ (↑u - n : 𝓞 K)) :
    ∃ v, u = v ^ (p : ℕ) := by
  haveI : Fact (Nat.Prime p) := hpri
  obtain ⟨ζ, hζ⟩ := IsCyclotomicExtension.exists_prim_root (S := {p}) ℚ (B := K) (n := p) rfl
  obtain ⟨x, hx⟩ : (p : 𝓞 K) ∣ (↑(u ^ (p - 1 : ℕ)) : 𝓞 K) - 1
  · obtain ⟨n, hn⟩ := hcong
    have hn' : (p : ℤ) ∣ n ^ (p - 1 : ℕ) - 1
    · refine Int.modEq_iff_dvd.mp (Int.ModEq.pow_card_sub_one_eq_one hpri.out (n := n) ?_).symm
      rw [isCoprime_comm, (Nat.prime_iff_prime_int.mp hpri.out).coprime_iff_not_dvd]
      intro h
      replace h := _root_.map_dvd (Int.castRingHom (𝓞 K)) h
      simp only [map_natCast, eq_intCast, ← dvd_iff_dvd_of_dvd_sub hn] at h
      refine hζ.zeta_sub_one_prime'.not_unit ((isUnit_pow_iff ?_).mp
        (isUnit_of_dvd_unit ((associated_zeta_sub_one_pow_prime hζ).dvd.trans h) u.isUnit))
      simpa only [ge_iff_le, ne_eq, tsub_eq_zero_iff_le, not_le] using hpri.out.one_lt
    replace hn' := _root_.map_dvd (Int.castRingHom (𝓞 K)) hn'
    simp only [map_natCast, eq_intCast, Int.cast_sub, Int.cast_pow, Int.cast_one] at hn'
    rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem,
      RingHom.map_sub, sub_eq_zero] at hn hn' ⊢
    rw [Units.val_pow_eq_pow_val, RingHom.map_pow, hn, ← RingHom.map_pow, hn']
  have : (hζ.unit' - 1 : 𝓞 K) ^ (p : ℕ) ∣ (↑(u ^ (p - 1 : ℕ)) : 𝓞 K) - 1
  · rw [hx]
    rw [sub_eq_iff_eq_add, add_comm] at hx
    have H : Algebra.norm ℤ (1 + (p : ℕ) • x) = 1 := norm_add_one_smul_of_isUnit hpri.out
      (PNat.coe_injective.ne_iff.mpr hp) x (by rw [nsmul_eq_mul, ← hx]; exact Units.isUnit _)
    have := H ▸ zeta_sub_one_pow_dvd_norm_sub_pow hζ x
    simpa [ge_iff_le, Int.cast_one, sub_self, nsmul_eq_mul, Nat.cast_mul, PNat.pos,
      Nat.cast_pred, zero_sub, IsUnit.mul_iff, ne_eq, tsub_eq_zero_iff_le, not_le, dvd_neg,
      Units.isUnit, and_true, zero_add] using this
  have : ¬(∀ v : K, _) := false_of_zeta_sub_one_pow_dvd_sub_one_of_pow_ne hp hreg hζ _ this
  simp only [not_forall, not_not] at this
  obtain ⟨v, hv⟩ := this
  have hv' : IsIntegral ℤ v
  · apply IsIntegral.of_pow p.pos; rw [hv]; exact NumberField.RingOfIntegers.isIntegral_coe _
  have : IsUnit (⟨v, hv'⟩ : 𝓞 K)
  · rw [← isUnit_pow_iff p.pos.ne.symm]; convert (u ^ (p - 1 : ℕ) : (𝓞 K)ˣ).isUnit; ext; exact hv
  have hv'' : this.unit ^ (p : ℕ) = u ^ (p - 1 : ℕ)
  · ext; simpa only [Units.val_pow_eq_pow_val, IsUnit.unit_spec, SubmonoidClass.coe_pow] using hv
  use u / this.unit
  rw [div_pow, hv'', div_eq_mul_inv, ← pow_sub _ tsub_le_self,
    tsub_tsub_cancel_of_le (Nat.Prime.one_lt hpri.out).le, pow_one]
