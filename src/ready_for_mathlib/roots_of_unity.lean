import ring_theory.roots_of_unity

variables {R : Type*} [comm_ring R] [is_domain R] {k : ℕ} {ζ : R}

open_locale big_operators

open finset nat

namespace is_primitive_root

lemma geom_sum_eq_zero (hζ : is_primitive_root ζ k) (hk : 1 < k) :
  (∑ i in range k, ζ ^ i) = 0 :=
begin
  have : 1 - ζ ≠ 0,
  { intro h,
    have := hζ.dvd_of_pow_eq_one 1,
    simp only [(eq_of_sub_eq_zero h).symm, one_pow, eq_self_iff_true, nat.dvd_one,
      forall_true_left] at this,
    simpa [this] using hk },
  refine eq_zero_of_ne_zero_of_mul_left_eq_zero this _,
  rw [mul_neg_geom_sum, hζ.pow_eq_one, sub_self]
end

lemma pow_sub_one_eq (hζ : is_primitive_root ζ k) (hk : 1 < k) :
  ζ ^ k.pred = -(∑ i in range k.pred, ζ ^ i) :=
begin
  have := hζ.geom_sum_eq_zero hk,
  rwa [← succ_pred_eq_of_pos (lt_trans zero_lt_one hk), range_succ, sum_insert not_mem_range_self,
    add_eq_zero_iff_eq_neg] at this
end

end is_primitive_root
