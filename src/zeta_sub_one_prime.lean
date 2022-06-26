import norm_prime
import number_theory.cyclotomic.gal
import number_theory.cyclotomic.rat
import z_basis

namespace is_cyclotomic_extension.rat

variables {p : ℕ+} {k : ℕ} {K : Type*} [field K] [char_zero K] {ζ : K} [fact (p : ℕ).prime]
variables  [is_cyclotomic_extension {p} ℚ K] (hζ : is_primitive_root ζ p)

open_locale number_field

local notation `R` := 𝓞 K

include hζ

lemma zeta_sub_one_mem_ring_of_integers : ζ - 1 ∈ R :=
subalgebra.sub_mem _ (hζ.is_integral p.pos) (subalgebra.one_mem _)

/-- The `power_basis` of `𝓞 K` given by `ζ - 1`, where `K` is a `p ^ k` cyclotomic
extension of `ℚ`. -/
noncomputable def power_basis_sub_one_int [hcycl : is_cyclotomic_extension {p ^ k} ℚ K]
  (hζ : is_primitive_root ζ ↑(p ^ k)) : power_basis ℤ (𝓞 K) :=
begin
  letI : number_field K := is_cyclotomic_extension.number_field {p ^ k} ℚ _,
  let uffa := power_basis_int hζ,
  have : is_integral ℤ (⟨(ζ - 1), subalgebra.sub_mem _ (hζ.is_integral (p ^ k).pos) (subalgebra.one_mem _)⟩ : 𝓞 K) ,
  { sorry },
  refine power_basis.of_gen_mem_adjoin' (algebra_map ℤ (𝓞 K)).injective_int uffa this _,
  {
    simp [uffa],
    sorry
  }
end

lemma zeta_sub_one_prime  : prime (⟨ζ - 1, zeta_sub_one_mem_ring_of_integers hζ⟩ : R) :=
begin
  simp_rw [← hζ.sub_one_power_basis_gen ℚ],
  sorry
 --refine prime_of_norm_prime _ _,
end

end is_cyclotomic_extension.rat
