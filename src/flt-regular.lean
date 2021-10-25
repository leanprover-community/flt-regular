import ring_theory.class_group
import number_theory.regular_primes

theorem flt_regular (p a b c : ℕ) [fact p.prime] (hp : is_regular_number p)
  (h : a ^ p + b ^ p = c ^ p) : a * b * c = 0 := sorry
