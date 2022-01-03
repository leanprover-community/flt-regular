import algebra.ne_zero

lemma pos_of_ne_zero_coe (n : ℕ) (R : Type*) [has_zero R] [has_one R] [has_add R]
  [ne_zero (n : R)] : 0 < n :=
(ne_zero.of_ne_zero_coe R).out.bot_lt

lemma ne_zero.not_dvd_char (R) [add_monoid R] [has_one R]
  {p : ℕ} [char_p R p] (k : ℕ) [h : ne_zero (k : R)] : ¬ p ∣ k :=
by rwa [←not_iff_not.mpr $ char_p.cast_eq_zero_iff R p k, ←ne.def, ←ne_zero_iff]
