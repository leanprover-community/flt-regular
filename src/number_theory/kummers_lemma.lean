import number_theory.regular_primes
import number_theory.cyclotomic.rat


-- Let 𝑝 be a regular prime (i.e. an odd prime which does not divide the class number of
-- the 𝑝-th cyclotomic field) and 𝜉 a primitive 𝑝-th root of unity;
-- if a unit 𝑢∈𝐐(𝜉) is congruent to an integer modulo 𝑝, then 𝑢 is a 𝑝-th power in 𝐐(𝜉).

/--
Kummer's lemma, a converse to `flt_fact_3`
-/

variables {K : Type*} [field K] [char_zero K]

open_locale number_field

lemma eq_pow_prime_of_unit_of_congruent (p : ℕ) [hp : fact p.prime] (hptwo : p ≠ 2)
  (hpr : is_regular_number p) [is_cyclotomic_extension {⟨p, hp.out.pos⟩} ℚ K]
  (u : (𝓞 K)ˣ)  (hcong : ∃ n : ℤ, (↑u : 𝓞 K) - n ∈ ideal.span ({p} : set (𝓞 K))) :
  ∃ v, u = v ^ p := sorry
