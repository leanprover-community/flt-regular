/-
Copyright (c) 2022 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

import ring_theory.eisenstein_criterion

/-!
# Eisenstein polynomials
Given an ideal `𝓟` of a commutative semiring `R`, we say that a polynomial `f : polynomial R` is
*Eisenstein at `𝓟`* if `f.leading_coeff ∉ 𝓟`, `∀ n, n < f.nat_degree → f.coeff n ∈ 𝓟` and
`f.coeff 0 ∉ 𝓟 ^ 2`.

## Main definition
* `polynomial.is_eisenstein_at f 𝓟` : the property of being Eisenstein at `𝓟`.

## Main results
* `polynomial.is_eisenstein_at.irreducible` : if a primitive `f` satisfies `f.is_eisenstein_at 𝓟`,
  where `𝓟.is_prime`, then `f` is irreducible.
-/

universe u

variables {R : Type u}

namespace polynomial

/-- Given an ideal `𝓟` of a commutative semiring `R`, we say that a polynomial `f : polynomial R`
is *Eisenstein at `𝓟`* if `f.leading_coeff ∉ 𝓟`, `∀ n, n < f.nat_degree → f.coeff n ∈ 𝓟` and
`f.coeff 0 ∉ 𝓟 ^ 2`. -/
@[mk_iff] structure is_eisenstein_at [comm_semiring R] (f : polynomial R) (𝓟 : ideal R) : Prop :=
(leading : f.leading_coeff ∉ 𝓟)
(mem : ∀ {n}, n < f.nat_degree → f.coeff n ∈ 𝓟)
(not_mem : f.coeff 0 ∉ 𝓟 ^ 2)

namespace is_eisenstein_at

lemma coeff_mem [comm_semiring R] {f : polynomial R} {𝓟 : ideal R} {n : ℕ} (hn : n ≠ f.nat_degree)
  (hf : f.is_eisenstein_at 𝓟) : f.coeff n ∈ 𝓟 :=
begin
  cases ne_iff_lt_or_gt.1 hn,
  { exact hf.mem h },
  { rw [coeff_eq_zero_of_nat_degree_lt h],
    exact ideal.zero_mem _}
end

/-- If a primitive `f` satisfies `f.is_eisenstein_at 𝓟`, where `𝓟.is_prime`, then `f` is
irreducible. -/
lemma irreducible [comm_ring R] [is_domain R] {f : polynomial R} {𝓟 : ideal R}
  (hprime : 𝓟.is_prime) (hu : f.is_primitive) (hei : f.is_eisenstein_at 𝓟)
  (hfd0 : 0 < f.nat_degree) : irreducible f :=
irreducible_of_eisenstein_criterion hprime hei.leading (λ n hn, hei.mem (coe_lt_degree.1 hn))
  (nat_degree_pos_iff_degree_pos.1 hfd0) hei.not_mem hu

end is_eisenstein_at

end polynomial
