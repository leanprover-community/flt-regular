import number_theory.regular_primes
import number_theory.cyclotomic.rat


-- Let 𝑝 be a regular prime (i.e. an odd prime which does not divide the class number of
-- the 𝑝-th cyclotomic field) and 𝜉 a primitive 𝑝-th root of unity;
-- if a unit 𝑢∈𝐐(𝜉) is congruent to an integer modulo 𝑝, then 𝑢 is a 𝑝-th power in 𝐐(𝜉).

/--
Kummer's lemma, a converse to `flt_fact_3`
-/
lemma eq_pow_prime_of_unit_of_congruent (p : ℕ) [fact (0 < p)] (hpp : prime p) (hptwo : p ≠ 2)
  (hpr : is_regular_number p) (u : units (cyclotomic_ring ⟨p, fact.out _⟩ ℤ ℚ))
  (hcong : ∃ n : ℤ, (↑u : cyclotomic_ring _ _ _) - n ∈ ideal.span ({p} : set (cyclotomic_ring ⟨p, fact.out _⟩ ℤ ℚ))) :
  ∃ v, u = v ^ p := sorry
