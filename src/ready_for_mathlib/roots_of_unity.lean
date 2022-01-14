import ring_theory.polynomial.cyclotomic.basic

-- pr 11455
lemma pnat.succ_nat_pred' (n : ℕ+) : 1 + n.nat_pred = n :=
by rw [pnat.nat_pred, add_tsub_cancel_iff_le.mpr $ show 1 ≤ (n : ℕ), from n.pos]

/-- Make an element of `roots_of_unity` from a member of the base ring, and a proof that it has
a positive power equal to one. -/
def roots_of_unity.mk_of_pow_eq {M} [comm_monoid M] (ζ : M) {n : ℕ+} (h : ζ ^ (n : ℕ) = 1) :
  roots_of_unity n M :=
⟨units.mk_of_mul_eq_one ζ (ζ ^ n.nat_pred) $
  by rwa [←pow_one ζ, ←pow_mul, ←pow_add, one_mul, pnat.succ_nat_pred'],
units.ext $ by simpa⟩

@[simp] lemma roots_of_unity.coe_mk_of_pow_eq {M} [comm_monoid M] {ζ : M} {n : ℕ+}
  {h : ζ ^ (n : ℕ) = 1} : (roots_of_unity.mk_of_pow_eq _ h : M) = ζ := rfl

-- I'm not too sure if this is strictly necessary
@[simp] lemma roots_of_unity.coe_mk_of_pow_eq' {M} [comm_monoid M] {ζ : M} {n : ℕ+}
  {h : ζ ^ (n : ℕ) = 1} : (↑(roots_of_unity.mk_of_pow_eq _ h : Mˣ) : M) = ζ := rfl

open polynomial

lemma is_root_of_unity_of {n : ℕ} {R} [comm_ring R] {ζ : R} {i : ℕ}
  (hi : i ∈ n.divisors) (h : (cyclotomic i R).is_root ζ) : ζ ^ n = 1 :=
begin
  rcases n.eq_zero_or_pos with rfl | hn,
  { exact pow_zero _ },
  have := congr_arg (eval ζ) (prod_cyclotomic_eq_X_pow_sub_one hn R).symm,
  rw [eval_sub, eval_pow, eval_X, eval_one] at this,
  convert eq_add_of_sub_eq' this,
  convert (add_zero _).symm,
  apply eval_eq_zero_of_dvd_of_eval_eq_zero _ h,
  exact finset.dvd_prod_of_mem _ hi
end
