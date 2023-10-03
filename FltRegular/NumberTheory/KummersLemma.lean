import FltRegular.NumberTheory.RegularPrimes
import Mathlib.NumberTheory.Cyclotomic.Rat

open scoped NumberField

-- Let 𝑝 be a regular prime (i.e. an odd prime which does not divide the class number off
-- the 𝑝-th cyclotomic field) and 𝜉 a primitive 𝑝-th root of unity;
-- if a unit 𝑢∈𝐐(𝜉) is congruent to an integer modulo 𝑝, then 𝑢 is a 𝑝-th power in 𝐐(𝜉).
variable {K : Type*} {p : ℕ+} [hpri : Fact p.Prime] [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable (hp : p ≠ 2) [Fintype (ClassGroup (𝓞 K))] (hreg : (p : ℕ).Coprime <| Fintype.card <| ClassGroup (𝓞 K))

theorem eq_pow_prime_of_unit_of_congruent (u : (𝓞 K)ˣ)
    (hcong : ∃ n : ℤ, ↑p ∣ (↑u : 𝓞 K) - n) : ∃ v, u = v ^ (p : ℕ) :=
  sorry
