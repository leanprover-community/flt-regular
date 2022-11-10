import number_theory.cyclotomic.Unit_lemmas
import number_theory.cyclotomic.cycl_rat
import number_theory.regular_primes
import number_theory.cyclotomic.factoring

open_locale number_field non_zero_divisors

variables {p : ℕ+} {K : Type*} [field K] [char_zero K] [is_cyclotomic_extension {p} ℚ K]
variables {ζ : K} (hζ : is_primitive_root ζ p)

open fractional_ideal

variable (i : ℤ)

namespace flt_regular.caseI

lemma exists_int_sum_eq_zero (hpodd : p ≠ 2) [hp : fact(p : ℕ).prime] {x y i : ℤ} {u : (𝓞 K)ˣ}
  {α : 𝓞 K} (h : (x : 𝓞 K) + y * (hζ.unit' ^ i : (𝓞 K)ˣ) = u * α ^ (p : ℕ)) :
  ∃ k : ℤ, (x : 𝓞 K) + y * (hζ.unit' ^ i : (𝓞 K)ˣ) - (hζ.unit' ^ (2 * k) : (𝓞 K)ˣ) *
    (x + y * (hζ.unit' ^ -i : (𝓞 K)ˣ)) ∈ ideal.span ({p} : set (𝓞 K)) :=
begin
  letI : number_field K := is_cyclotomic_extension.number_field {p} ℚ _,
  obtain ⟨β, k, hβreal : gal_conj K p β = β, H⟩ := unit_lemma_gal_conj hζ hpodd hp.out u,
  have : ((x + y * (hζ.unit' ^ -i : (𝓞 K)ˣ)) : K) = gal_conj K p (x + y * hζ.unit' ^ i),
  { simp [gal_conj_zeta_runity hζ, ← coe_life] },
  obtain ⟨a, ha⟩ := exists_int_sub_pow_prime_dvd p α,
  refine ⟨k, _⟩,
  rw [ideal.mem_span_singleton] at ha ⊢,
  obtain ⟨γ, hγ⟩ := ha,
  rw [h, sub_eq_iff_eq_add.1 hγ, mul_add, ← mul_assoc, mul_comm ↑u, mul_assoc, add_sub_assoc],
  refine dvd_add (dvd.intro _ rfl) _,
  have h' := congr_arg (coe : 𝓞 K → K) h,
  have hγ' := congr_arg (coe : 𝓞 K → K) hγ,
  simp only [add_subgroup_class.coe_sub, subsemiring_class.coe_pow, subring_class.coe_int_cast,
    mul_mem_class.coe_mul, subring_class.coe_nat_cast, add_mem_class.coe_add, coe_zpow'] at h' hγ',
  rw [h', sub_eq_iff_eq_add.1 hγ', H, mul_mem_class.coe_mul, alg_equiv.map_mul, alg_equiv.map_mul,
    alg_equiv.map_add, map_int_cast, alg_equiv.map_mul, ← coe_coe β, coe_zpow', map_zpow₀, coe_coe,
    coe_zpow'] at this,
  simp only [coe_coe, hζ.coe_unit'_coe, subring_class.coe_nat_cast, map_nat_cast] at this,
  let γ' := (⟨gal_conj K p γ, number_field.ring_of_integers.map_mem (gal_conj K p) γ⟩ : 𝓞 K),
  have hint : ↑γ' = gal_conj K p γ := rfl,
  rw [← coe_coe β, hβreal, gal_conj_zeta_runity hζ, ← hζ.coe_unit'_coe, inv_zpow, ← zpow_neg,
    coe_coe, ← hint, ← subring_class.coe_int_cast (𝓞 K) x, ← subring_class.coe_int_cast (𝓞 K) y,
    ← coe_coe, ← coe_zpow', ← subring_class.coe_nat_cast (𝓞 K) p, ← coe_zpow',
    ← subring_class.coe_int_cast (𝓞 K) a, ← mul_mem_class.coe_mul (𝓞 K),
    ← add_mem_class.coe_add (𝓞 K), ← mul_mem_class.coe_mul (𝓞 K), ← mul_mem_class.coe_mul (𝓞 K),
    ← add_mem_class.coe_add (𝓞 K), ← mul_mem_class.coe_mul (𝓞 K), subtype.coe_inj] at this,
  rw [this, mul_add, mul_add, sub_add_eq_sub_sub, sub_right_comm],
  refine dvd_sub _ (by simp),
  rw [mul_comm ↑β, ← mul_assoc, ← mul_assoc, ← units.coe_mul, ← zpow_add, two_mul,
    ← sub_eq_add_neg, add_sub_assoc, sub_self, add_zero, mul_comm _ ↑β, ← H, sub_self],
  exact dvd_zero _
end

end flt_regular.caseI
