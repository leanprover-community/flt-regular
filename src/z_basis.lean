import number_theory.cyclotomic.rat
import ready_for_mathlib.adjoin_root

namespace is_cyclotomic_extension.rat

open_locale number_field

open algebra adjoin_root is_cyclotomic_extension.rat

variables {p : ℕ+} {k : ℕ} {K : Type*} [field K] [char_zero K] {ζ : K} [fact (p : ℕ).prime]

noncomputable
def power_basis_int [hcycl : is_cyclotomic_extension {p ^ k} ℚ K]
  (hζ : is_primitive_root ζ ↑(p ^ k)) : power_basis ℤ (𝓞 K) :=
let _ := is_integral_closure_adjoing_singleton_of_prime_pow hζ in by exactI
  (adjoin.power_basis' ℚ (hζ.is_integral (p ^ k).pos)).map
  (is_integral_closure.equiv ℤ (adjoin ℤ ({ζ} : set K)) K (𝓞 K))

@[simp] lemma power_basis_int_gen [hcycl : is_cyclotomic_extension {p ^ k} ℚ K]
  (hζ : is_primitive_root ζ ↑(p ^ k)) : (power_basis_int hζ).gen = ⟨ζ, hζ.is_integral (p ^ k).pos⟩ :=
begin
  suffices : algebra_map _ K (power_basis_int hζ).gen = (⟨ζ, hζ.is_integral (p ^ k).pos⟩ : (𝓞 K)),
    { exact subtype.ext this },
  simpa [power_basis_int]
end

end is_cyclotomic_extension.rat

instance {n : ℕ+} : is_domain (adjoin_root $ polynomial.cyclotomic n ℤ) :=
begin
  suffices : prime (polynomial.cyclotomic n ℤ),
  { erw [ideal.quotient.is_domain_iff_prime, ideal.span_singleton_prime this.1],
    exact this },
  rw ←gcd_monoid.irreducible_iff_prime,
  exact polynomial.cyclotomic.irreducible n.pos,
end

instance {n} : is_cyclotomic_extension {n} ℤ (adjoin_root $ polynomial.cyclotomic n ℤ) :=
{ exists_prim_root := λ a ha,
  begin
    obtain rfl : a = n := ha,
    use adjoin_root.root _,
    sorry,
    --rw ←polynomial.is_root_cyclotomic_iff,
    -- I want to get `char_zero` automatically - surely quotienting by a pos-degree poly
    -- preserves characteristic, but I haven't given it too much thought (my idea: if you have
    -- an ideal of the form `(p)`, then all polys have degree ≥ `p`'s (bar `0`))
  end,
  adjoin_roots := sorry }

example {K L M} [comm_ring K] [comm_ring L] [comm_ring M] [algebra K L] [algebra K M]
  {n} [is_cyclotomic_extension {n} K L] [is_cyclotomic_extension {n} K M] : L ≃ₐ[K] M :=
begin
  sorry
end
