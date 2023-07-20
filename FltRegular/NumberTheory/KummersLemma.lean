import FltRegular.NumberTheory.RegularPrimes
import Mathlib.NumberTheory.Cyclotomic.Rat

-- Let 𝑝 be a regular prime (i.e. an odd prime which does not divide the class number of
-- Let 𝑝 be a regular prime (i.e. an odd prime which does not divide the class number of
-- the 𝑝-th cyclotomic field) and 𝜉 a primitive 𝑝-th root of unity;
-- the 𝑝-th cyclotomic field) and 𝜉 a primitive 𝑝-th root of unity;
-- if a unit 𝑢∈𝐐(𝜉) is congruent to an integer modulo 𝑝, then 𝑢 is a 𝑝-th power in 𝐐(𝜉).
-- if a unit 𝑢∈𝐐(𝜉) is congruent to an integer modulo 𝑝, then 𝑢 is a 𝑝-th power in 𝐐(𝜉).
variable {K : Type _} [Field K] [CharZero K]

open scoped NumberField

theorem eq_pow_prime_of_unit_of_congruent (p : ℕ) [hp : Fact p.Prime] (hptwo : p ≠ 2)
    (hpr : IsRegularNumber p) [IsCyclotomicExtension {⟨p, hp.out.pos⟩} ℚ K] (u : (𝓞 K)ˣ)
    (hcong : ∃ n : ℤ, (↑u : 𝓞 K) - n ∈ Ideal.span ({(p : 𝓞 K)} : Set (𝓞 K))) : ∃ v, u = v ^ p :=
  sorry
