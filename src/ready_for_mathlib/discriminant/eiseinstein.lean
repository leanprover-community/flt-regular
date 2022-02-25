import ring_theory.polynomial.eisenstein
import ring_theory.polynomial.cyclotomic.basic

variables {p : ℕ} (hp : p.prime)

open_locale polynomial

namespace polynomial

local notation `𝓟` := submodule.span ℤ {p}

lemma cyclotomic.comp_is_eisenstein_at : ((cyclotomic p ℤ).comp (X + 1)).is_eisenstein_at 𝓟 :=
{ leading := sorry,
  mem := sorry,
  not_mem := sorry }

end polynomial
