import ring_theory.polynomial.eisenstein
import number_theory.cyclotomic.galois_action_on_cyclo

import ready_for_mathlib.zeta_sub_one

universes u

open finite_dimensional polynomial algebra

variables (n : ℕ+) (L : Type u) [field L] [char_zero L]

namespace is_cyclotomic_extension

open_locale number_field

local attribute [instance] is_cyclotomic_extension.number_field
local attribute [-instance] cyclotomic_field.algebra

lemma cyclotomic_ring.is_integral_closure_prime {p : ℕ+} [hp : fact (p : ℕ).prime] (hodd : p ≠ 2) :
  is_integral_closure (cyclotomic_ring p ℤ ℚ) ℤ (cyclotomic_field p ℚ) :=
begin
  refine ⟨is_fraction_ring.injective _ _, λ x, ⟨λ h, ⟨⟨x, _⟩, rfl⟩, _⟩⟩,
  { haveI : is_cyclotomic_extension {p} ℚ (cyclotomic_field p ℚ),
    { convert cyclotomic_field.is_cyclotomic_extension p _,
      { apply subsingleton.elim (algebra_rat) _,
        exact algebra_rat_subsingleton },
      { exact ne_zero.char_zero } },
    let B := (zeta_primitive_root p ℚ (cyclotomic_field p ℚ)).sub_one_power_basis ℚ,
    have hζ := zeta_primitive_root p ℚ (cyclotomic_field p ℚ),
    have hint : is_integral ℤ B.gen :=  is_integral_sub (hζ.is_integral hp.out.pos) is_integral_one,
    have H := discr_mul_is_integral_mem_adjoin ℚ hint h,
    rw [discr_odd_prime' hζ hodd] at H,
    replace H : (p : ℤ) ^ ((p : ℕ) - 2) • x ∈ adjoin ℤ ({B.gen} : set (cyclotomic_field p ℚ)),
    { by_cases heven : even (((p : ℕ) - 1) / 2),
      { rw [heven.neg_one_pow, one_mul] at H,
        simp only [coe_coe] at H,
        simp only [coe_coe, zsmul_eq_mul, int.cast_pow, int.cast_coe_nat],
        convert H,
        simp },
      { rw [(nat.odd_iff_not_even.2 heven).neg_one_pow] at H,
        simp only [coe_coe, neg_mul, one_mul, neg_smul] at H,
        simp only [coe_coe, zsmul_eq_mul, int.cast_pow, int.cast_coe_nat],
        convert subalgebra.neg_mem _ H,
        rw [neg_neg],
        congr,
        simp } },
    have hmin : (minpoly ℤ B.gen).is_eisenstein_at (submodule.span ℤ {((p : ℕ) : ℤ)}),
    { have h₁ := minpoly.gcd_domain_eq_field_fractions ℚ hint,
      have h₂ := hζ.minpoly_sub_one_eq_cyclotomic_comp (cyclotomic.irreducible_rat hp.out.pos),
      rw [is_primitive_root.sub_one_power_basis_gen] at h₁,
      rw [h₁, ← map_cyclotomic_int, show int.cast_ring_hom ℚ = algebra_map ℤ ℚ, by refl,
        show ((X + 1)) = map (algebra_map ℤ ℚ) (X + 1), by simp, ← map_comp] at h₂,
      rw [is_primitive_root.sub_one_power_basis_gen, map_injective (algebra_map ℤ ℚ)
        ((algebra_map ℤ ℚ).injective_int) h₂],
      exact cyclotomic_comp_X_add_one_is_eisenstein_at p },
    replace H := mem_adjoin_of_smul_prime_pow_smul_of_minpoly_is_eiseinstein_at
      (nat.prime_iff_prime_int.1 hp.out) hint h H hmin,
    convert adjoin_le _ H,
    { exact subsingleton.elim _ _ },
    { exact subsingleton.elim _ _ },
    { simp only [is_primitive_root.sub_one_power_basis_gen, set.singleton_subset_iff,
        set_like.mem_coe],
      refine subalgebra.sub_mem _ (subset_adjoin _) (subalgebra.one_mem _),
      simp only [set.mem_set_of_eq, zeta_pow] } },
  { haveI : is_cyclotomic_extension {p} ℤ (cyclotomic_ring p ℤ ℚ),
    { convert cyclotomic_ring.is_cyclotomic_extension p ℤ ℚ,
      exact subsingleton.elim (algebra_int _) _ },
    rintro ⟨y, rfl⟩,
    exact is_integral.algebra_map ((is_cyclotomic_extension.integral {p} ℤ _) _) }
end

end is_cyclotomic_extension
