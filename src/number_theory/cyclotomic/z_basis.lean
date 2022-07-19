import number_theory.cyclotomic.rat

namespace is_cyclotomic_extension.rat

open_locale number_field nat

open algebra adjoin_root is_cyclotomic_extension.rat

variables {p : ℕ+} {k : ℕ} {K : Type*} [field K] [char_zero K] {ζ : K} [fact (p : ℕ).prime]

/-- The `power_basis` of `𝓞 K` given by a primitive root of unity, where `K` is a `p ^ k` cyclotomic
extension of `ℚ`. -/
noncomputable def power_basis_int [hcycl : is_cyclotomic_extension {p ^ k} ℚ K]
  (hζ : is_primitive_root ζ ↑(p ^ k)) : power_basis ℤ (𝓞 K) :=
let _ := is_integral_closure_adjoing_singleton_of_prime_pow hζ in by exactI
 (adjoin.power_basis' (hζ.is_integral (p ^ k).pos)).map
 (is_integral_closure.equiv ℤ (adjoin ℤ ({ζ} : set K)) K (𝓞 K))

@[simp] lemma power_basis_int_gen [hcycl : is_cyclotomic_extension {p ^ k} ℚ K]
  (hζ : is_primitive_root ζ ↑(p ^ k)) : (power_basis_int hζ).gen = ⟨ζ, hζ.is_integral (p ^ k).pos⟩ :=
subtype.ext $ show algebra_map _ K (power_basis_int hζ).gen = _, by simpa [power_basis_int]

@[simp] lemma power_basis_int_dim [hcycl : is_cyclotomic_extension {p ^ k} ℚ K]
  (hζ : is_primitive_root ζ ↑(p ^ k)) : (power_basis_int hζ).dim = φ (p ^ k) :=
by simp [power_basis_int, ←polynomial.cyclotomic_eq_minpoly hζ, polynomial.nat_degree_cyclotomic]

/-- The `power_basis` of `𝓞 K` given by a primitive root of unity, where `K` is a `p`-th cyclotomic
extension of `ℚ`. -/
noncomputable def power_basis_int' [hcycl : is_cyclotomic_extension {p} ℚ K]
  (hζ : is_primitive_root ζ p) : power_basis ℤ (𝓞 K) :=
@power_basis_int p 1 K _ _ _ _ (by { convert hcycl, rw pow_one }) (by rwa pow_one)

@[simp] lemma power_basis_int'_gen [hcycl : is_cyclotomic_extension {p} ℚ K]
  (hζ : is_primitive_root ζ p) : (power_basis_int' hζ).gen = ⟨ζ, hζ.is_integral p.pos⟩ :=
@power_basis_int_gen p 1 K _ _ _ _ (by { convert hcycl, rw pow_one }) (by rwa pow_one)

@[simp] lemma power_basis_int'_dim [hcycl : is_cyclotomic_extension {p} ℚ K]
  (hζ : is_primitive_root ζ p) : (power_basis_int' hζ).dim = φ p :=
by erw [@power_basis_int_dim p 1 K _ _ _ _ (by { convert hcycl, rw pow_one }) (by rwa pow_one), pow_one]


end is_cyclotomic_extension.rat

/-

This was an attempt to make `adjoin_root $ polynomial.cyclotomic n R` a cyclotomic extension in
some generality, but it's not true in such generality in many cases, and is anyways completely
overkill for this project.

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
    admit,
    --rw ←polynomial.is_root_cyclotomic_iff,
    -- I want to get `char_zero` automatically - surely quotienting by a pos-degree poly
    -- preserves characteristic, but I haven't given it too much thought (my idea: if you have
    -- an ideal of the form `(p)`, then all polys have degree ≥ `p`'s (bar `0`))
  end,
  adjoin_roots := admit }

example {K L M} [comm_ring K] [comm_ring L] [comm_ring M] [algebra K L] [algebra K M]
  {n} [is_cyclotomic_extension {n} K L] [is_cyclotomic_extension {n} K M] : L ≃ₐ[K] M :=
begin
  admit
end

-/
