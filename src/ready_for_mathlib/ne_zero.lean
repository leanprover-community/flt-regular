import algebra.ne_zero

-- pr #11437
lemma pos_of_ne_zero_coe (n : ℕ) (R : Type*) [has_zero R] [has_one R] [has_add R]
  [ne_zero (n : R)] : 0 < n :=
(ne_zero.of_ne_zero_coe R).out.bot_lt
