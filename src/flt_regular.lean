import ring_theory.class_group
import number_theory.regular_primes



theorem flt_regular_case_one (p a b c : ℕ) [fact p.prime] (hp : is_regular_number p)
  (h : a ^ p + b ^ p = c ^ p) : p ∣  a*b*c := sorry

theorem flt_regular (p a b c : ℕ) [fact p.prime] (hp : is_regular_number p)
  (h : a ^ p + b ^ p = c ^ p) : a * b * c = 0 := sorry
