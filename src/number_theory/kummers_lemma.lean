import number_theory.regular_primes
import number_theory.cyclotomic.rat


-- Let đ be a regular prime (i.e. an odd prime which does not divide the class number of
-- the đ-th cyclotomic field) and đ a primitive đ-th root of unity;
-- if a unit đąâđ(đ) is congruent to an integer modulo đ, then đą is a đ-th power in đ(đ).

/--
Kummer's lemma, a converse to `flt_fact_3`
-/

variables {K : Type*} [field K] [char_zero K]

open_locale number_field

lemma eq_pow_prime_of_unit_of_congruent (p : â) [fact (0 < p)] (hpp : prime p) (hptwo : p â  2)
  (hpr : is_regular_number p) [is_cyclotomic_extension {âšp, fact.out _â©} â K]
  (u : (đ K)ËŁ)  (hcong : â n : â€, (âu : đ K) - n â ideal.span ({p} : set (đ K))) :
  â v, u = v ^ p := sorry
