import ring_theory.polynomial.eisenstein
import ring_theory.polynomial.cyclotomic.basic

variables {p : ℕ} [hp : fact p.prime]

open_locale polynomial

namespace polynomial

local notation `𝓟` := submodule.span ℤ {p}

include hp

lemma cyclotomic.comp_is_eisenstein_at : ((cyclotomic p ℤ).comp (X + 1)).is_eisenstein_at 𝓟 :=
{ leading := sorry,
  mem := λ i hi,
  begin
    rw [nat_degree_comp, show (X + 1 : ℤ[X]) = X + C 1, by simp, nat_degree_X_add_C, mul_one] at hi,
    sorry
  end,
  not_mem := sorry }

end polynomial
