import norm.norm_prime
import number_theory.cyclotomic.gal
import number_theory.cyclotomic.rat

variables {K : Type*} [field K] {ζ : K}

open_locale number_field

open polynomial algebra

local notation `R` := 𝓞 K

namespace is_cyclotomic_extension.rat

variables {p : ℕ+} {k : ℕ} [hp : fact (p : ℕ).prime] [char_zero K]

include hp

lemma zeta_sub_one_prime [is_cyclotomic_extension {p ^ (k + 1)} ℚ K]
  (hζ : is_primitive_root ζ ↑(p ^ (k + 1))) (hodd : p ≠ 2) :
  prime (⟨ζ - 1, subalgebra.sub_mem _ (hζ.is_integral (p ^ _).pos) (subalgebra.one_mem _)⟩ : R) :=
begin
  letI := is_cyclotomic_extension.number_field {p ^ (k + 1)} ℚ K,
  letI := is_cyclotomic_extension.is_galois (p ^ (k + 1)) ℚ K,
  rw [← hζ.sub_one_integral_power_basis_gen],
  refine prime_of_norm_prime _,
  rw [hζ.sub_one_integral_power_basis_gen],
  simp only [norm', monoid_hom.restrict_apply, set_like.coe_mk, monoid_hom.cod_restrict_apply,
    hζ.sub_one_norm_prime_ne_two (cyclotomic.irreducible_rat (p ^ (k + 1)).pos) hodd],
  rw [mul_equiv.prime_iff rat.ring_of_integers_equiv.to_mul_equiv],
  simp only [coe_coe, ring_equiv.to_mul_equiv_eq_coe, ring_equiv.coe_to_mul_equiv],
  convert nat.prime_iff_prime_int.1 hp.1,
  refine equiv_like.injective rat.ring_of_integers_equiv.symm (subtype.ext _),
  simp only [set_like.coe_mk, ring_equiv.symm_apply_apply],
  norm_cast,
  simp [← ring_equiv.coe_to_ring_hom]
end

lemma zeta_sub_one_prime' [h : is_cyclotomic_extension {p} ℚ K] (hζ : is_primitive_root ζ p)
  (hodd : p ≠ 2) :
  prime (⟨ζ - 1, subalgebra.sub_mem _ (hζ.is_integral p.pos) (subalgebra.one_mem _)⟩ : R) :=
begin
  convert @zeta_sub_one_prime K _ _ p 0 _ _ (by { convert h, rw [zero_add, pow_one] }) _ hodd,
  simpa,
end

end is_cyclotomic_extension.rat
