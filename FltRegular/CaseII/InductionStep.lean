import FltRegular.CaseII.AuxLemmas
import FltRegular.NumberTheory.KummersLemma

open scoped BigOperators nonZeroDivisors NumberField
open Polynomial

variable {K : Type*} {p : ℕ+} [hpri : Fact p.Prime] [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable (hp : p ≠ 2) [Fintype (ClassGroup (𝓞 K))] (hreg : (p : ℕ).Coprime <| Fintype.card <| ClassGroup (𝓞 K))

variable {ζ : K} (hζ : IsPrimitiveRoot ζ p)

variable {x y z : 𝓞 K} {ε : (𝓞 K)ˣ}

set_option quotPrecheck false
local notation "𝔭" => (Ideal.span ({(hζ.unit' : 𝓞 K) - 1} : Set (𝓞 K)))
local notation "𝔦" η => Ideal.span (singleton (x + y * ↑η : 𝓞 K))
local notation "𝔵" => Ideal.span <| singleton x
local notation "𝔶" => Ideal.span <| singleton y
local notation "𝔷" => Ideal.span <| singleton z
local notation "𝔪" => gcd 𝔵 𝔶

variable {m : ℕ} (e : x ^ (p : ℕ) + y ^ (p : ℕ) = ε * (((hζ.unit' : 𝓞 K) - 1) ^ (m + 1) * z) ^ (p : ℕ))
variable (hy : ¬((hζ.unit' : 𝓞 K) - 1 ∣ y)) (hz : ¬((hζ.unit' : 𝓞 K) - 1 ∣ z))
variable (η : nthRootsFinset p (𝓞 K))

lemma zeta_sub_one_dvd : (hζ.unit' : 𝓞 K) - 1 ∣ x ^ (p : ℕ) + y ^ (p : ℕ) := by
  rw [e, mul_pow, ← pow_mul]
  apply dvd_mul_of_dvd_right
  apply dvd_mul_of_dvd_left
  apply dvd_pow_self
  simp

lemma one_sub_zeta_dvd_zeta_pow_sub :
  (hζ.unit' : 𝓞 K) - 1 ∣ x + y * η := by
  letI : Fact (Nat.Prime p) := hpri
  letI := IsCyclotomicExtension.numberField {p} ℚ K
  have h := zeta_sub_one_dvd hζ e
  replace h : ∏ _η in (nthRootsFinset p (𝓞 K) : Set (𝓞 K)).toFinset,
    Ideal.Quotient.mk 𝔭 (x + y * η : 𝓞 K) = 0
  · rw [pow_add_pow_eq_prod_add_zeta_runity_mul (hpri.out.eq_two_or_odd.resolve_left
      (PNat.coe_injective.ne hp)) hζ.unit'_coe, ← Ideal.Quotient.eq_zero_iff_dvd, map_prod] at h
    convert h using 2 with η' hη'
    rw [map_add, map_add, map_mul, map_mul,
      IsPrimitiveRoot.eq_one_mod_one_sub' hζ.unit'_coe (by rwa [Set.mem_toFinset, SetLike.mem_coe] at hη'),
      IsPrimitiveRoot.eq_one_mod_one_sub' hζ.unit'_coe η.prop, one_mul, mul_one]
  rw [Finset.prod_const, ← map_pow, Ideal.Quotient.eq_zero_iff_dvd] at h
  exact (IsCyclotomicExtension.Rat.zeta_sub_one_prime' hζ hp).dvd_of_dvd_pow h

lemma div_one_sub_zeta_mem : (x + y * η : 𝓞 K) / (ζ - 1) ∈ 𝓞 K := by
  obtain ⟨⟨a, ha⟩, e⟩ := one_sub_zeta_dvd_zeta_pow_sub hp hζ e η
  rw [e, mul_comm]
  simp only [Submonoid.coe_mul, Subsemiring.coe_toSubmonoid, Subalgebra.coe_toSubsemiring,
    AddSubgroupClass.coe_sub, IsPrimitiveRoot.val_unit'_coe, OneMemClass.coe_one, ne_eq]
  rwa [mul_div_cancel _ (hζ.sub_one_ne_zero hpri.out.one_lt)]

def div_zeta_sub_one : nthRootsFinset p (𝓞 K) → 𝓞 K :=
λ η ↦ ⟨(x + y * η) / (ζ - 1), div_one_sub_zeta_mem hp hζ e η⟩

lemma div_zeta_sub_one_mul_zeta_sub_one (η) :
  div_zeta_sub_one hp hζ e η * ((hζ.unit' : 𝓞 K) - 1) = x + y * η := by
  ext
  simp [div_zeta_sub_one, div_mul_cancel _ (hζ.sub_one_ne_zero hpri.out.one_lt)]

lemma div_zeta_sub_one_sub (η₁ η₂) (hη : η₁ ≠ η₂) :
  Associated y (div_zeta_sub_one hp hζ e η₁ - div_zeta_sub_one hp hζ e η₂) := by
  letI := IsCyclotomicExtension.numberField {p} ℚ K
  apply Associated.of_mul_right _ (Associated.refl ((hζ.unit' : 𝓞 K) - 1))
    (hζ.unit'_coe.sub_one_ne_zero hpri.out.one_lt)
  convert_to Associated _ (y * (η₁ - η₂))
  · rw [sub_mul, div_zeta_sub_one_mul_zeta_sub_one, div_zeta_sub_one_mul_zeta_sub_one]
    ring
  apply Associated.mul_left
  apply hζ.unit'_coe.associated_sub_one hpri.out η₁.prop η₂.prop
  rw [Ne.def, ← Subtype.ext_iff.not]
  exact hη

lemma div_zeta_sub_one_Injective :
  Function.Injective (λ η ↦ Ideal.Quotient.mk 𝔭 (div_zeta_sub_one hp hζ e η)) := by
  letI : AddGroup (𝓞 K ⧸ 𝔭) := inferInstance
  intros η₁ η₂
  contrapose
  intro e₁ e₂
  apply hy
  obtain ⟨u, e⟩ := div_zeta_sub_one_sub hp hζ e η₁ η₂ e₁
  dsimp only at e₂
  rwa [← sub_eq_zero, ← map_sub, ← e, Ideal.Quotient.eq_zero_iff_dvd, u.isUnit.dvd_mul_right] at e₂

instance : Finite (𝓞 K ⧸ 𝔭) := by
  haveI : Fact (Nat.Prime p) := hpri
  letI := IsCyclotomicExtension.numberField {p} ℚ K
  rw [← Ideal.absNorm_ne_zero_iff, Ne.def, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
  exact hζ.unit'_coe.sub_one_ne_zero hpri.out.one_lt

lemma div_zeta_sub_one_Bijective :
  Function.Bijective (λ η ↦ Ideal.Quotient.mk 𝔭 (div_zeta_sub_one hp hζ e η)) := by
  haveI : Fact (Nat.Prime p) := hpri
  letI := Fintype.ofFinite (𝓞 K ⧸ 𝔭)
  letI := IsCyclotomicExtension.numberField {p} ℚ K
  rw [Fintype.bijective_iff_injective_and_card]
  use div_zeta_sub_one_Injective hp hζ e hy
  simp only [PNat.pos, mem_nthRootsFinset, Fintype.card_coe]
  rw [hζ.unit'_coe.card_nthRootsFinset, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply,
    Ideal.absNorm_span_singleton, norm_Int_zeta_sub_one hζ hp]
  rfl

lemma div_zeta_sub_one_eq_zero_iff (η) :
  Ideal.Quotient.mk 𝔭 (div_zeta_sub_one hp hζ e η) = 0 ↔
    ((hζ.unit' : 𝓞 K) - 1) ^ 2 ∣ x + y * η := by
  letI := IsCyclotomicExtension.numberField {p} ℚ K
  rw [Ideal.Quotient.eq_zero_iff_dvd, pow_two,
    ← div_zeta_sub_one_mul_zeta_sub_one hp hζ e,
      mul_dvd_mul_iff_right (hζ.unit'_coe.sub_one_ne_zero hpri.out.one_lt)]

lemma existsUnique_zeta_sub_one_pow_two_dvd :
  ∃! η : nthRootsFinset p (𝓞 K), ((hζ.unit' : 𝓞 K) - 1) ^ 2 ∣ x + y * η := by
  simp_rw [← div_zeta_sub_one_eq_zero_iff hp hζ e]
  exact (div_zeta_sub_one_Bijective hp hζ e hy).existsUnique _

lemma gcd_zeta_sub_one_eq_one : gcd 𝔪 𝔭 = 1 := by
  haveI : Fact (Nat.Prime p) := hpri
  rw [gcd_assoc]
  convert gcd_one_right 𝔵 using 2
  rwa [gcd_comm, Irreducible.gcd_eq_one_iff, Ideal.dvd_span_singleton, Ideal.mem_span_singleton]
  · rw [GCDMonoid.irreducible_iff_prime]
    exact hζ.prime_span_sub_one hp

lemma gcd_div_div_zeta_sub_one (η) :
  𝔪 ∣ (Ideal.span <| singleton <| div_zeta_sub_one hp hζ e η) := by
  haveI : Fact (Nat.Prime p) := hpri
  rw [← mul_one (Ideal.span <| singleton <| div_zeta_sub_one hp hζ e η),
    ← gcd_zeta_sub_one_eq_one hp hζ hy (x := x) (y := y)]
  apply dvd_mul_gcd_of_dvd_mul
  rw [Ideal.span_singleton_mul_span_singleton, div_zeta_sub_one_mul_zeta_sub_one,
  Ideal.dvd_span_singleton, Ideal.gcd_eq_sup]
  refine add_mem
    (Ideal.mem_sup_left (Ideal.subset_span (s := singleton x) rfl))
    (Ideal.mem_sup_right (Ideal.mul_mem_right _ _ (Ideal.subset_span (s := singleton y) rfl)))

noncomputable
def div_zeta_sub_one_dvd_gcd : Ideal (𝓞 K) :=
(gcd_div_div_zeta_sub_one hp hζ e hy η).choose

local notation "𝔠" => div_zeta_sub_one_dvd_gcd hp hζ e hy

lemma div_zeta_sub_one_dvd_gcd_spec :
  𝔪 * 𝔠 η = (Ideal.span <| singleton <| div_zeta_sub_one hp hζ e η) :=
(gcd_div_div_zeta_sub_one hp hζ e hy η).choose_spec.symm

lemma m_mul_c_mul_p : 𝔪 * 𝔠 η * 𝔭 = 𝔦 η := by
  rw [div_zeta_sub_one_dvd_gcd_spec, Ideal.span_singleton_mul_span_singleton,
    div_zeta_sub_one_mul_zeta_sub_one]

lemma m_ne_zero : 𝔪 ≠ 0 := by
  simp_rw [Ne.def, gcd_eq_zero_iff, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
  rintro ⟨rfl, rfl⟩
  exact hy (dvd_zero _)

lemma p_ne_zero : 𝔭 ≠ 0 := by
  letI := IsCyclotomicExtension.numberField {p} ℚ K
  rw [Ne.def, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
  exact hζ.unit'_coe.sub_one_ne_zero hpri.out.one_lt

lemma coprime_c_aux (η₁ η₂ : nthRootsFinset p (𝓞 K)) (hη : η₁ ≠ η₂) :
 (𝔦 η₁) ⊔ (𝔦 η₂) ∣ 𝔪 * 𝔭 := by
  have : 𝔭 = Ideal.span (singleton <| (η₁ : 𝓞 K) - η₂) := by
    rw [Ideal.span_singleton_eq_span_singleton]
    exact hζ.unit'_coe.associated_sub_one hpri.out η₁.prop η₂.prop (Subtype.coe_injective.ne hη)
  rw [(gcd_mul_right' 𝔭 𝔵 𝔶).symm.dvd_iff_dvd_right, dvd_gcd_iff]
  simp_rw [this, Ideal.span_singleton_mul_span_singleton, Ideal.dvd_span_singleton,
    Ideal.mem_span_singleton_sup, Ideal.mem_span_singleton]
  refine ⟨⟨-η₂, _, ⟨η₁, rfl⟩, ?_⟩, ⟨1, _, ⟨-1, rfl⟩, ?_⟩⟩
  · ring
  · ring

lemma coprime_c (η₁ η₂ : nthRootsFinset p (𝓞 K)) (hη : η₁ ≠ η₂) :
  IsCoprime (𝔠 η₁) (𝔠 η₂) := by
  rw [Ideal.isCoprime_iff_codisjoint, codisjoint_iff_le_sup, ← Ideal.dvd_iff_le]
  rw [← mul_dvd_mul_iff_left (m_ne_zero hζ e hy), ← mul_dvd_mul_iff_right (p_ne_zero hζ)]
  rw [Ideal.mul_sup, Ideal.sup_mul, m_mul_c_mul_p, m_mul_c_mul_p, Ideal.mul_top]
  exact coprime_c_aux hζ η₁ η₂ hη

lemma span_pow_add_pow_eq :
  Ideal.span (singleton <| x ^ (p : ℕ) + y ^ (p : ℕ)) = (𝔭 ^ (m + 1) * 𝔷) ^ (p : ℕ) := by
  simp only [e, ← Ideal.span_singleton_pow, ← Ideal.span_singleton_mul_span_singleton]
  convert one_mul _
  rw [Ideal.one_eq_top, Ideal.span_singleton_eq_top]
  exact ε.isUnit

lemma gcd_m_p_pow_eq_one : gcd 𝔪 (𝔭 ^ (m + 1)) = 1 := by
  rw [← Ideal.isCoprime_iff_gcd, IsCoprime.pow_right_iff, Ideal.isCoprime_iff_gcd,
    gcd_zeta_sub_one_eq_one hp hζ hy]
  simp only [add_pos_iff, or_true]

lemma m_dvd_z : 𝔪 ∣ 𝔷 := by
  rw [← one_mul 𝔷, ← gcd_m_p_pow_eq_one hp hζ hy (x := x) (m := m)]
  apply dvd_gcd_mul_of_dvd_mul
  rw [← pow_dvd_pow_iff_dvd hpri.out.ne_zero, ← span_pow_add_pow_eq hζ e,
    Ideal.dvd_span_singleton]
  apply add_mem
  · exact Ideal.pow_mem_pow (Ideal.mem_sup_left (Ideal.mem_span_singleton_self x)) (p : ℕ)
  · exact Ideal.pow_mem_pow (Ideal.mem_sup_right (Ideal.mem_span_singleton_self y)) (p : ℕ)

noncomputable
def z_div_m : Ideal (𝓞 K) :=
(m_dvd_z hp hζ e hy).choose

local notation "𝔷'" => z_div_m hp hζ e hy

lemma z_div_m_spec : 𝔷 = 𝔪 * 𝔷' :=
(m_dvd_z hp hζ e hy).choose_spec

lemma exists_ideal_pow_eq_c_aux :
  𝔪 ^ (p : ℕ) * (𝔷' * 𝔭 ^ m) ^ (p : ℕ) * 𝔭 ^ (p : ℕ) = (𝔭 ^ (m + 1) * 𝔷) ^ (p : ℕ) := by
  rw [mul_comm _ 𝔷, mul_pow, z_div_m_spec hp hζ e hy, mul_pow, mul_pow, ← pow_mul, ← pow_mul,
    add_mul, one_mul, pow_add, mul_assoc, mul_assoc, mul_assoc]

lemma prod_c : ∏ η in Finset.attach (nthRootsFinset p (𝓞 K)), 𝔠 η = (𝔷' * 𝔭 ^ m) ^ (p : ℕ) := by
  have e' := span_pow_add_pow_eq hζ e
  rw [pow_add_pow_eq_prod_add_zeta_runity_mul
    (hpri.out.eq_two_or_odd.resolve_left (PNat.coe_injective.ne hp)) hζ.unit'_coe] at e'
  rw [← Ideal.prod_span_singleton, ← Finset.prod_attach] at e'
  simp_rw [mul_comm _ y, ← m_mul_c_mul_p hp hζ e hy,
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_attach,
    hζ.unit'_coe.card_nthRootsFinset] at e'
  rw [← mul_right_inj'
    ((pow_ne_zero_iff hpri.out.pos).mpr (m_ne_zero hζ e hy) : _),
    ← mul_left_inj' ((pow_ne_zero_iff hpri.out.pos).mpr (p_ne_zero hζ) : _), e',
    exists_ideal_pow_eq_c_aux]

lemma exists_ideal_pow_eq_c : ∃ I : Ideal (𝓞 K), (𝔠 η) = I ^ (p : ℕ) := by
  letI inst1 : @IsDomain (Ideal (𝓞 K)) CommSemiring.toSemiring := @Ideal.isDomain (𝓞 K) _ _ _
  letI inst2 := @Ideal.instNormalizedGCDMonoidIdealToSemiringToCommSemiringCancelCommMonoidWithZero (𝓞 K) _ _ _
  letI inst3 := @NormalizedGCDMonoid.toGCDMonoid _ _ inst2
  exact @Finset.exists_eq_pow_of_mul_eq_pow_of_coprime (nthRootsFinset p (𝓞 K)) (Ideal (𝓞 K)) _
    (by convert inst1) (by convert inst3) _ _ _ _ _
    (λ η₁ _ η₂ _ hη ↦ coprime_c hp hζ e hy η₁ η₂ hη)
    (prod_c hp hζ e hy) η (Finset.mem_attach _ _)

noncomputable
def root_div_zeta_sub_one_dvd_gcd : Ideal (𝓞 K) :=
(exists_ideal_pow_eq_c hp hζ e hy η).choose

local notation "𝔞" => root_div_zeta_sub_one_dvd_gcd hp hζ e hy

lemma root_div_zeta_sub_one_dvd_gcd_spec : (𝔞 η) ^ (p : ℕ) = 𝔠 η :=
(exists_ideal_pow_eq_c hp hζ e hy η).choose_spec.symm

lemma c_div_principal_aux (η₁ η₂ : nthRootsFinset p (𝓞 K)) :
  ((𝔦 η₁) / (𝔦 η₂) : FractionalIdeal (𝓞 K)⁰ K) = 𝔠 η₁ / 𝔠 η₂ := by
  simp_rw [← m_mul_c_mul_p hp hζ e hy, FractionalIdeal.coeIdeal_mul]
  rw [mul_div_mul_right, mul_div_mul_left]
  · rw [← FractionalIdeal.coeIdeal_bot, (FractionalIdeal.coeIdeal_injective' le_rfl).ne_iff]
    exact m_ne_zero hζ e hy
  · rw [← FractionalIdeal.coeIdeal_bot, (FractionalIdeal.coeIdeal_injective' le_rfl).ne_iff]
    exact p_ne_zero hζ

lemma c_div_principal (η₁ η₂ : nthRootsFinset p (𝓞 K)) :
  Submodule.IsPrincipal ((𝔠 η₁ / 𝔠 η₂ : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) := by
  rw [← c_div_principal_aux, FractionalIdeal.coeIdeal_span_singleton,
    FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.spanSingleton_div_spanSingleton,
    FractionalIdeal.coe_spanSingleton]
  exact ⟨⟨_, rfl⟩⟩

lemma a_div_principal (η₁ η₂ : nthRootsFinset p (𝓞 K)) :
  Submodule.IsPrincipal ((𝔞 η₁ / 𝔞 η₂ : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) := by
  apply isPrincipal_of_isPrincipal_pow_of_Coprime' _ hreg
  rw [div_pow, ← FractionalIdeal.coeIdeal_pow, ← FractionalIdeal.coeIdeal_pow,
    root_div_zeta_sub_one_dvd_gcd_spec, root_div_zeta_sub_one_dvd_gcd_spec]
  exact c_div_principal hp hζ e hy η₁ η₂

noncomputable
def zeta_sub_one_dvd_root : nthRootsFinset p (𝓞 K) :=
(Equiv.ofBijective _ (div_zeta_sub_one_Bijective hp hζ e hy)).symm 0

local notation "η₀" => zeta_sub_one_dvd_root hp hζ e hy

lemma zeta_sub_one_dvd_root_spec : Ideal.Quotient.mk 𝔭 (div_zeta_sub_one hp hζ e η₀) = 0 :=
Equiv.ofBijective_apply_symm_apply _ (div_zeta_sub_one_Bijective hp hζ e hy) 0

lemma p_dvd_c_iff : 𝔭 ∣ (𝔠 η) ↔ η = η₀ := by
  rw [← (div_zeta_sub_one_Injective hp hζ e hy).eq_iff, zeta_sub_one_dvd_root_spec,
    Ideal.Quotient.eq_zero_iff_dvd, ← Ideal.mem_span_singleton (α := 𝓞 K),
    ← Ideal.dvd_span_singleton, ← div_zeta_sub_one_dvd_gcd_spec (hy := hy),
    ← dvd_gcd_mul_iff_dvd_mul, gcd_comm, gcd_zeta_sub_one_eq_one hp hζ hy, one_mul]

lemma p_pow_dvd_c_eta_zero_aux [DecidableEq K] :
  gcd (𝔭 ^ (m * p)) (∏ η in Finset.attach (nthRootsFinset p (𝓞 K)) \ {η₀}, 𝔠 η) = 1 := by
    rw [← Ideal.isCoprime_iff_gcd]
    apply IsCoprime.pow_left
    rw [Ideal.isCoprime_iff_gcd, (hζ.prime_span_sub_one hp).irreducible.gcd_eq_one_iff,
      (hζ.prime_span_sub_one hp).dvd_finset_prod_iff]
    rintro ⟨η, hη, h⟩
    rw [p_dvd_c_iff] at h
    simp only [Finset.mem_sdiff, Finset.mem_singleton] at hη
    exact hη.2 h

lemma p_pow_dvd_c_eta_zero : 𝔭 ^ (m * p) ∣ 𝔠 η₀ := by
  classical
  rw [← one_mul (𝔠 η₀), ← p_pow_dvd_c_eta_zero_aux hp hζ e hy, dvd_gcd_mul_iff_dvd_mul, mul_comm _ (𝔠 η₀),
    ← Finset.prod_eq_mul_prod_diff_singleton (Finset.mem_attach _ η₀) 𝔠, prod_c, mul_pow]
  apply dvd_mul_of_dvd_right
  rw [pow_mul]

lemma p_dvd_a_iff : 𝔭 ∣ (𝔞 η) ↔ η = η₀ := by
  rw [← p_dvd_c_iff hp hζ e hy, ← root_div_zeta_sub_one_dvd_gcd_spec,
    (hζ.prime_span_sub_one hp).dvd_pow_iff_dvd hpri.out.ne_zero]

lemma p_pow_dvd_a_eta_zero : 𝔭 ^ m ∣ 𝔞 η₀ := by
  rw [← pow_dvd_pow_iff_dvd hpri.out.ne_zero, root_div_zeta_sub_one_dvd_gcd_spec, ← pow_mul]
  exact p_pow_dvd_c_eta_zero hp hζ e hy

noncomputable
def a_eta_zero_dvd_p_pow : Ideal (𝓞 K) :=
(p_pow_dvd_a_eta_zero hp hζ e hy).choose

local notation "𝔞₀" => a_eta_zero_dvd_p_pow hp hζ e hy

lemma a_eta_zero_dvd_p_pow_spec : 𝔭 ^ m * 𝔞₀ = 𝔞 η₀ :=
(p_pow_dvd_a_eta_zero hp hζ e hy).choose_spec.symm

lemma not_p_div_a_zero : ¬ 𝔭 ∣ 𝔞₀ := by
  intro h
  have := pow_dvd_pow_of_dvd (mul_dvd_mul (dvd_refl (𝔭 ^ m)) h) p
  rw [a_eta_zero_dvd_p_pow_spec, root_div_zeta_sub_one_dvd_gcd_spec] at this
  have := this.trans (Finset.dvd_prod_of_mem 𝔠 (Finset.mem_attach _ η₀))
  rw [prod_c, mul_pow, mul_pow, mul_comm, mul_dvd_mul_iff_right,
    pow_dvd_pow_iff_dvd hpri.out.ne_zero] at this
  apply hz
  rw [← Ideal.mem_span_singleton, ← Ideal.dvd_span_singleton, z_div_m_spec hp hζ e hy]
  exact this.trans (dvd_mul_left _ _)
  · apply mt pow_eq_zero
    apply mt pow_eq_zero
    rw [Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact hζ.unit'_coe.sub_one_ne_zero hpri.out.one_lt

lemma one_le_m : 1 ≤ m := by
  have ha := not_p_div_a_zero hp hζ e hy hz
  rw [← (hζ.prime_span_sub_one hp).irreducible.gcd_eq_one_iff] at ha
  have := (p_dvd_a_iff hp hζ e hy η₀).mpr rfl
  rw [← a_eta_zero_dvd_p_pow_spec, mul_comm, ← dvd_gcd_mul_iff_dvd_mul, ha, one_mul] at this
  nth_rw 1 [← pow_one 𝔭] at this
  rwa [← pow_dvd_pow_iff (p_ne_zero hζ) (hζ.prime_span_sub_one hp).not_unit]

lemma isPrincipal_a_div_a_zero :
  Submodule.IsPrincipal ((𝔞 η / 𝔞₀ : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) := by
  have := a_div_principal hp hreg hζ e hy η η₀
  rw [← a_eta_zero_dvd_p_pow_spec, mul_comm, FractionalIdeal.coeIdeal_mul, ← div_div,
   FractionalIdeal.isPrincipal_iff] at this
  obtain ⟨a, ha⟩ := this
  rw [div_eq_iff, Ideal.span_singleton_pow, FractionalIdeal.coeIdeal_span_singleton,
    FractionalIdeal.spanSingleton_mul_spanSingleton] at ha
  rw [FractionalIdeal.isPrincipal_iff]
  exact ⟨_, ha⟩
  · rw [← FractionalIdeal.coeIdeal_bot,
      (FractionalIdeal.coeIdeal_injective' (le_rfl : (𝓞 K)⁰ ≤ (𝓞 K)⁰)).ne_iff]
    apply mt pow_eq_zero
    rw [Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact hζ.unit'_coe.sub_one_ne_zero hpri.out.one_lt

lemma exists_not_dvd_spanSingleton_eq_a_div_a_zero (hη : η ≠ η₀) :
  ∃ a b : 𝓞 K, ¬((hζ.unit' : 𝓞 K) - 1 ∣ a) ∧ ¬((hζ.unit' : 𝓞 K) - 1 ∣ b) ∧
    FractionalIdeal.spanSingleton (𝓞 K)⁰ (a / b : K) = 𝔞 η / 𝔞₀ := by
  haveI : Fact (Nat.Prime p) := hpri
  exact exists_not_dvd_spanSingleton_eq (IsCyclotomicExtension.Rat.zeta_sub_one_prime' hζ hp)
    _ _ ((p_dvd_a_iff hp hζ e hy η).not.mpr hη) (not_p_div_a_zero hp hζ e hy hz)
      (isPrincipal_a_div_a_zero hp hreg hζ e hy η)

noncomputable
def a_div_a_zero_num (hη : η ≠ η₀) : 𝓞 K :=
(exists_not_dvd_spanSingleton_eq_a_div_a_zero hp hreg hζ e hy hz η hη).choose

noncomputable
def a_div_a_zero_denom (hη : η ≠ η₀) : 𝓞 K :=
(exists_not_dvd_spanSingleton_eq_a_div_a_zero hp hreg hζ e hy hz η hη).choose_spec.choose

local notation "α" => a_div_a_zero_num hp hreg hζ e hy hz
local notation "β" => a_div_a_zero_denom hp hreg hζ e hy hz

lemma a_div_a_zero_num_spec (hη : η ≠ η₀) : ¬((hζ.unit' : 𝓞 K) - 1 ∣ α η hη) :=
(exists_not_dvd_spanSingleton_eq_a_div_a_zero hp hreg hζ e hy hz η hη).choose_spec.choose_spec.1

lemma a_div_a_zero_denom_spec (hη : η ≠ η₀) : ¬((hζ.unit' : 𝓞 K) - 1 ∣ β η hη) :=
(exists_not_dvd_spanSingleton_eq_a_div_a_zero hp hreg hζ e hy hz η hη).choose_spec.choose_spec.2.1

lemma a_div_a_zero_eq (hη : η ≠ η₀) :
  FractionalIdeal.spanSingleton (𝓞 K)⁰ (α η hη / β η hη : K) = 𝔞 η / 𝔞₀ :=
(exists_not_dvd_spanSingleton_eq_a_div_a_zero hp hreg hζ e hy hz η hη).choose_spec.choose_spec.2.2

lemma a_mul_denom_eq_a_zero_mul_num (hη : η ≠ η₀) :
  𝔞 η * Ideal.span (singleton <| β η hη) = 𝔞₀ * Ideal.span (singleton <| α η hη) := by
  apply FractionalIdeal.coeIdeal_injective (K := K)
  simp only [FractionalIdeal.coeIdeal_mul, FractionalIdeal.coeIdeal_span_singleton]
  rw [mul_comm (𝔞₀ : FractionalIdeal (𝓞 K)⁰ K), ← div_eq_div_iff,
    ← a_div_a_zero_eq hp hreg hζ e hy hz η hη, FractionalIdeal.spanSingleton_div_spanSingleton]
  · rfl
  · intro ha
    rw [FractionalIdeal.coeIdeal_eq_zero] at ha
    apply not_p_div_a_zero hp hζ e hy hz
    rw [ha]
    exact dvd_zero _
  · rw [Ne.def, FractionalIdeal.spanSingleton_eq_zero_iff, ← (algebraMap (𝓞 K) K).map_zero,
      (IsFractionRing.injective (𝓞 K) K).eq_iff]
    intro hβ
    apply a_div_a_zero_denom_spec hp hreg hζ e hy hz η hη
    rw [hβ]
    exact dvd_zero _

lemma associated_eta_zero (hη : η ≠ η₀) :
  Associated ((x + y * η₀) * (α η hη) ^ (p : ℕ))
    ((x + y * η) * ((hζ.unit' : 𝓞 K) - 1) ^ (m * p) * (β η hη) ^ (p : ℕ)) := by
  simp_rw [← Ideal.span_singleton_eq_span_singleton,
    ← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_pow,
    ← m_mul_c_mul_p hp hζ e hy, ← root_div_zeta_sub_one_dvd_gcd_spec, ← a_eta_zero_dvd_p_pow_spec]
  rw [mul_comm _ 𝔞₀, mul_pow]
  simp only [mul_assoc, mul_left_comm _ 𝔭]
  rw [mul_left_comm (𝔞 η ^ (p : ℕ)), mul_left_comm (𝔞₀ ^ (p : ℕ)), ← pow_mul, ← mul_pow, ← mul_pow,
    a_mul_denom_eq_a_zero_mul_num]

noncomputable
def associated_eta_zero_unit (hη : η ≠ η₀) : (𝓞 K)ˣ :=
(associated_eta_zero hp hreg hζ e hy hz η hη).choose

local notation "ε" => associated_eta_zero_unit hp hreg hζ e hy hz

lemma associated_eta_zero_unit_spec (η) (hη : η ≠ η₀) :
  (ε η hη) * (x + y * η₀) * (α η hη) ^ (p : ℕ) =
  (x + y * η) * ((hζ.unit' : 𝓞 K) - 1) ^ (m * p) * (β η hη) ^ (p : ℕ) := by
  rw [mul_assoc, mul_comm (ε η hη : 𝓞 K)]
  exact (associated_eta_zero hp hreg hζ e hy hz η hη).choose_spec

lemma x_plus_y_mul_ne_zero : x + y * η ≠ 0 := by
  intro hη
  have : x + y * η ∣ x ^ (p : ℕ) + y ^ (p : ℕ) := by
    rw [pow_add_pow_eq_prod_add_zeta_runity_mul
      (hpri.out.eq_two_or_odd.resolve_left (PNat.coe_injective.ne hp)) hζ.unit'_coe]
    simp_rw [mul_comm _ y]
    exact Finset.dvd_prod_of_mem _ η.prop
  rw [hη, zero_dvd_iff, e] at this
  simp only [mul_eq_zero, Units.ne_zero, PNat.pos,
    pow_eq_zero_iff, add_pos_iff, or_true, false_or] at this
  rw [this.resolve_left (hζ.unit'_coe.sub_one_ne_zero hpri.out.one_lt)] at hz
  exact hz (dvd_zero _)

lemma stuff (η₁) (hη₁ : η₁ ≠ η₀) (η₂) (hη₂ : η₂ ≠ η₀) :
  (η₂ - η₀ : 𝓞 K) * ε η₁ hη₁ * (α η₁ hη₁ * β η₂ hη₂) ^ (p : ℕ) +
    (η₀ - η₁) * ε η₂ hη₂ * (α η₂ hη₂ * β η₁ hη₁) ^ (p : ℕ) =
    (η₂ - η₁) * (((hζ.unit' : 𝓞 K) - 1) ^ m * (β η₁ hη₁ * β η₂ hη₂)) ^ (p : ℕ) := by
  rw [← mul_right_inj' (x_plus_y_mul_ne_zero hp hζ e hz η₀), mul_add]
  simp_rw [mul_left_comm (x + y * η₀), mul_pow, mul_assoc, mul_left_comm (η₂ - η₀ : 𝓞 K),
    mul_left_comm (η₀ - η₁ : 𝓞 K), ← mul_assoc,
    associated_eta_zero_unit_spec, mul_assoc, ← mul_left_comm (η₂ - η₀ : 𝓞 K),
    ← mul_left_comm (η₀ - η₁ : 𝓞 K), pow_mul, ← mul_pow, mul_comm (β η₂ hη₂), ← mul_assoc, ← add_mul]
  congr 1
  ring

lemma exists_solution :
  ∃ (x' y' z' : 𝓞 K) (ε₁ ε₂ ε₃ : (𝓞 K)ˣ),
    ¬((hζ.unit' : 𝓞 K) - 1 ∣ x') ∧ ¬((hζ.unit' : 𝓞 K) - 1 ∣ y') ∧ ¬((hζ.unit' : 𝓞 K) - 1 ∣ z') ∧
    ↑ε₁ * x' ^ (p : ℕ) + ε₂ * y' ^ (p : ℕ) = ε₃ * (((hζ.unit' : 𝓞 K) - 1) ^ m * z') ^ (p : ℕ) := by
  letI : Fact (Nat.Prime p) := hpri
  let η₁ : nthRootsFinset p (𝓞 K) := ⟨η₀ * hζ.unit', mul_mem_nthRootsFinset
    (η₀ : _).prop (hζ.unit'_coe.mem_nthRootsFinset hpri.out.pos)⟩
  let η₂ : nthRootsFinset p (𝓞 K) := ⟨η₀ * hζ.unit' * hζ.unit', mul_mem_nthRootsFinset
    η₁.prop (hζ.unit'_coe.mem_nthRootsFinset hpri.out.pos)⟩
  have hη₁ : η₁ ≠ η₀ := by
    rw [← Subtype.coe_injective.ne_iff]
    show (η₀ * hζ.unit' : 𝓞 K) ≠ η₀
    rw [Ne.def, mul_right_eq_self₀, not_or]
    exact ⟨hζ.unit'_coe.ne_one hpri.out.one_lt,
      ne_zero_of_mem_nthRootsFinset (η₀ : _).prop⟩
  have hη₂ : η₂ ≠ η₀ := by
    rw [← Subtype.coe_injective.ne_iff]
    show (η₀ * hζ.unit' * hζ.unit' : 𝓞 K) ≠ η₀
    rw [Ne.def, mul_assoc, ← pow_two, mul_right_eq_self₀, not_or]
    exact ⟨hζ.unit'_coe.pow_ne_one_of_pos_of_lt zero_lt_two
      (hpri.out.two_le.lt_or_eq.resolve_right (PNat.coe_injective.ne hp.symm)),
      ne_zero_of_mem_nthRootsFinset (η₀ : _).prop⟩
  have hη : η₂ ≠ η₁ := by
    rw [← Subtype.coe_injective.ne_iff]
    show (η₀ * hζ.unit' * hζ.unit' : 𝓞 K) ≠ η₀ * hζ.unit'
    rw [Ne.def, mul_right_eq_self₀, not_or]
    exact ⟨hζ.unit'_coe.ne_one hpri.out.one_lt,
      mul_ne_zero (ne_zero_of_mem_nthRootsFinset (η₀ : _).prop)
      (hζ.unit'_coe.ne_zero hpri.out.ne_zero)⟩
  obtain ⟨u₁, hu₁⟩ := hζ.unit'_coe.associated_sub_one hpri.out η₂.prop (η₀ : _).prop
    (Subtype.coe_injective.ne_iff.mpr hη₂)
  obtain ⟨u₂, hu₂⟩ := hζ.unit'_coe.associated_sub_one hpri.out (η₀ : _).prop η₁.prop
    (Subtype.coe_injective.ne_iff.mpr hη₁.symm)
  obtain ⟨u₃, hu₃⟩ := hζ.unit'_coe.associated_sub_one hpri.out η₂.prop (η₁ : _).prop
    (Subtype.coe_injective.ne_iff.mpr hη)
  have := stuff hp hreg hζ e hy hz η₁ hη₁ η₂ hη₂
  rw [← hu₁, ← hu₂, ← hu₃, mul_assoc _ (u₁ : 𝓞 K), mul_assoc _ (u₂ : 𝓞 K), mul_assoc _ (u₃ : 𝓞 K),
    mul_assoc ((hζ.unit' : 𝓞 K) - 1), mul_assoc ((hζ.unit' : 𝓞 K) - 1), ← mul_add,
    mul_right_inj' (hζ.unit'_coe.sub_one_ne_zero hpri.out.one_lt), ← Units.val_mul,
    ← Units.val_mul] at this
  refine ⟨_, _, _, _, _, _, ?_, ?_, ?_, this⟩
  · exact (IsCyclotomicExtension.Rat.zeta_sub_one_prime' hζ hp).not_dvd_mul
      (a_div_a_zero_num_spec hp hreg hζ e hy hz η₁ hη₁)
      (a_div_a_zero_denom_spec hp hreg hζ e hy hz η₂ hη₂)
  · exact (IsCyclotomicExtension.Rat.zeta_sub_one_prime' hζ hp).not_dvd_mul
      (a_div_a_zero_num_spec hp hreg hζ e hy hz η₂ hη₂)
      (a_div_a_zero_denom_spec hp hreg hζ e hy hz η₁ hη₁)
  · exact (IsCyclotomicExtension.Rat.zeta_sub_one_prime' hζ hp).not_dvd_mul
      (a_div_a_zero_denom_spec hp hreg hζ e hy hz η₁ hη₁)
      (a_div_a_zero_denom_spec hp hreg hζ e hy hz η₂ hη₂)

lemma exists_solution'_aux {ε₁ ε₂ : (𝓞 K)ˣ} (hx : ¬ (hζ.unit' : 𝓞 K) - 1 ∣ x)
 (h : (p : 𝓞 K) ∣ ε₁ * x ^ (p : ℕ) + ε₂ * y ^ (p : ℕ)) :
  ∃ a : 𝓞 K, ↑p ∣ ↑(ε₁ / ε₂) - a ^ (p : ℕ) := by
  letI : Fact (Nat.Prime p) := hpri
  obtain ⟨a, b, e⟩ : IsCoprime ↑p x := isCoprime_of_not_zeta_sub_one_dvd hζ hp hx
  have : (p : 𝓞 K) ∣ b * x - 1 := by use -a ; rw [← e]; ring
  have := (this.trans (sub_one_dvd_pow_sub_one _ p)).trans (dvd_mul_left _ ↑(ε₁ / ε₂))
  use - y * b
  replace h := (h.trans (dvd_mul_right _ (b ^ (p : ℕ)))).trans (dvd_mul_left _ ↑(ε₂⁻¹))
  simp_rw [add_mul, mul_assoc, ← mul_pow, mul_add, ← mul_assoc, ← Units.val_mul] at h
  rw [← mul_comm ε₁, ← div_eq_mul_inv, inv_mul_self, Units.val_one, one_mul] at h
  convert dvd_sub h this using 1
  rw [neg_mul, (Nat.Prime.odd_of_ne_two hpri.out (PNat.coe_injective.ne hp)).neg_pow,
    sub_neg_eq_add, mul_sub, mul_one, mul_comm x b, add_sub_sub_cancel, add_comm]

lemma exists_solution' :
  ∃ (x' y' z' : 𝓞 K) (ε₃ : (𝓞 K)ˣ),
    ¬((hζ.unit' : 𝓞 K) - 1 ∣ y') ∧ ¬((hζ.unit' : 𝓞 K) - 1 ∣ z') ∧
    x' ^ (p : ℕ) + y' ^ (p : ℕ) = ε₃ * (((hζ.unit' : 𝓞 K) - 1) ^ m * z') ^ (p : ℕ) := by
  obtain ⟨x', y', z', ε₁, ε₂, ε₃, hx', hy', hz', e'⟩ := exists_solution hp hreg hζ e hy hz
  obtain ⟨ε', hε'⟩ : ∃ ε', ε₁ / ε₂ = ε' ^ (p : ℕ) := by
    apply eq_pow_prime_of_unit_of_congruent
    have : p - 1 ≤ m * p := (Nat.sub_le _ _).trans
      ((le_of_eq (one_mul _).symm).trans (Nat.mul_le_mul_right p (one_le_m hp hζ e hy hz)))
    obtain ⟨u, hu⟩ := (associated_zeta_sub_one_pow_prime hζ).symm
    rw [mul_pow, ← pow_mul, mul_comm (ε₃ : 𝓞 K), mul_assoc, ← Nat.sub_add_cancel this,
      add_comm _ (p - 1 : ℕ), pow_add, mul_assoc] at e'
    apply_fun Ideal.Quotient.mk (Ideal.span <| singleton (p : 𝓞 K)) at e'
    rw [map_mul, (Ideal.Quotient.eq_zero_iff_dvd _ _).mpr
      (associated_zeta_sub_one_pow_prime hζ).symm.dvd, zero_mul, Ideal.Quotient.eq_zero_iff_dvd] at e'
    obtain ⟨a, ha⟩ := exists_solution'_aux hp hζ hx' e'
    obtain ⟨b, hb⟩ := exists_dvd_pow_sub_Int_pow hp a
    have := dvd_add ha hb
    rw [sub_add_sub_cancel, ← Int.cast_pow] at this
    exact ⟨b ^ (p : ℕ), this⟩
  refine ⟨ε' * x', y', z', ε₃ / ε₂, hy', hz', ?_⟩
  rwa [mul_pow, ← Units.val_pow_eq_pow_val, ← hε', ← mul_right_inj' ε₂.isUnit.ne_zero,
    mul_add, ← mul_assoc, ← Units.val_mul, mul_div_cancel'_right,
    ← mul_assoc, ← Units.val_mul, mul_div_cancel'_right]
