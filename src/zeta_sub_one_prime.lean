import norm_prime
import number_theory.cyclotomic.gal
import number_theory.cyclotomic.rat
import z_basis

variables {K : Type*} [field K] [char_zero K] {ζ : K}

open_locale number_field

open polynomial algebra

local notation `R` := 𝓞 K

namespace is_primitive_root

variables {n : ℕ+} variables (hζ : is_primitive_root ζ n)

lemma sub_one_mem_ring_of_integers : ζ - 1 ∈ R :=
subalgebra.sub_mem _ (hζ.is_integral n.pos) (subalgebra.one_mem _)

--generalize this to any element of subtype
lemma sub_one_int_is_integral : _root_.is_integral ℤ (⟨ζ - 1, hζ.sub_one_mem_ring_of_integers⟩ : R) :=
begin
  obtain ⟨P, hPm, hP⟩ := is_integral_sub (hζ.is_integral n.pos) is_integral_one,
  refine ⟨P, hPm, _⟩,
  rw [← aeval_def, ← subalgebra.coe_eq_zero, aeval_subalgebra_coe, set_like.coe_mk,
    aeval_def, hP]
end

end is_primitive_root

namespace is_cyclotomic_extension.rat

variables {p : ℕ+} {k : ℕ} [hp : fact (p : ℕ).prime]

include hp

/-- The `power_basis` of `𝓞 K` given by `ζ - 1`, where `K` is a `p ^ k` cyclotomic
extension of `ℚ`. -/
@[simps]
noncomputable def power_basis_sub_one_int [is_cyclotomic_extension {p ^ k} ℚ K]
  (hζ : is_primitive_root ζ ↑(p ^ k)) : power_basis ℤ (𝓞 K) :=
let _ := is_cyclotomic_extension.number_field {p ^ k} ℚ K in by exactI
  power_basis.of_gen_mem_adjoin' (algebra_map ℤ (𝓞 K)).injective_int (power_basis_int hζ)
  hζ.sub_one_int_is_integral
begin
  simp only [power_basis_int_gen],
  have := subalgebra.add_mem _
    (self_mem_adjoin_singleton ℤ (⟨ζ - 1, hζ.sub_one_mem_ring_of_integers⟩ : R))
    (subalgebra.one_mem _),
  convert this,
  simp
end

lemma zeta_sub_one_prime [is_cyclotomic_extension {p ^ (k + 1)} ℚ K]
  (hζ : is_primitive_root ζ ↑(p ^ (k + 1))) (hodd : p ≠ 2) :
  prime (⟨ζ - 1, hζ.sub_one_mem_ring_of_integers⟩ : R) :=
begin
  letI := is_cyclotomic_extension.number_field {p ^ (k + 1)} ℚ K,
  letI := is_cyclotomic_extension.is_galois (p ^ (k + 1)) ℚ K,
  rw [← power_basis_sub_one_int_gen hζ],
  refine prime_of_norm_prime _,
  rw [power_basis_sub_one_int_gen hζ],
  simp only [norm', monoid_hom.restrict_apply, set_like.coe_mk, monoid_hom.cod_restrict_apply,
    hζ.sub_one_norm_prime_ne_two (cyclotomic.irreducible_rat (p ^ (k + 1)).pos) hodd],
  rw [mul_equiv.prime_iff rat.ring_of_integers_equiv.to_mul_equiv],
  simp only [coe_coe, ring_equiv.to_mul_equiv_eq_coe, ring_equiv.coe_to_mul_equiv],
  convert nat.prime_iff_prime_int.1 hp.1,
  refine equiv_like.injective rat.ring_of_integers_equiv.symm (subtype.ext _),
  simp only [set_like.coe_mk, ring_equiv.symm_apply_apply],
  norm_cast,
  simp [← ring_equiv.coe_to_ring_hom, ring_hom.eq_int_cast]

end

end is_cyclotomic_extension.rat
