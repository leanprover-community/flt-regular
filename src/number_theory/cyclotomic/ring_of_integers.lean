import number_theory.cyclotomic.basic

variables (n : ℕ) [fact (0 < n)]

open polynomial

lemma cyclotomic_ring_eq_int_adjoin : cyclotomic_ring n =
  algebra.adjoin ℤ {adjoin_root.root (cyclotomic n ℚ)} := sorry
