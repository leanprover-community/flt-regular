/-
Copyright (c) 2020 Ruben Van de Velde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import data.int.parity
import ring_theory.int.basic
import ring_theory.prime

/-- Being equal to `4` or odd. -/
def odd_prime_or_four (z : ℤ) : Prop :=
  z = 4 ∨ (prime z ∧ odd z)

lemma odd_prime_or_four.ne_zero {z : ℤ} (h : odd_prime_or_four z) : z ≠ 0 :=
begin
  obtain rfl|⟨h, -⟩ := h,
  { norm_num },
  { exact h.ne_zero }
end

lemma odd_prime_or_four.ne_one {z : ℤ} (h : odd_prime_or_four z) : z ≠ 1 :=
begin
  obtain rfl|⟨h, -⟩ := h,
  { norm_num },
  { exact h.ne_one }
end

lemma odd_prime_or_four.one_lt_abs {z : ℤ} (h : odd_prime_or_four z) : 1 < abs z :=
begin
  obtain rfl|⟨h, -⟩ := h,
  { rw int.abs_eq_nat_abs, norm_cast, norm_num },
  { rw int.abs_eq_nat_abs,
    rw int.prime_iff_nat_abs_prime at h,
    norm_cast,
    exact h.one_lt, }
end

lemma odd_prime_or_four.not_unit {z : ℤ} (h : odd_prime_or_four z) : ¬ is_unit z :=
begin
  obtain rfl|⟨h, -⟩ := h,
  { rw is_unit_iff_dvd_one, norm_num },
  { exact h.not_unit }
end

lemma odd_prime_or_four.abs {z : ℤ} (h : odd_prime_or_four z) : odd_prime_or_four (abs z) :=
begin
  obtain rfl|⟨hp, ho⟩ := h,
  { left, rw abs_eq_self, norm_num },
  { right, exact ⟨hp.abs, odd_abs.mpr ho⟩ }
end

lemma odd_prime_or_four.exists_and_dvd
  {n : ℤ} (n2 : 2 < n) : ∃ p, p ∣ n ∧ odd_prime_or_four p :=
begin
  lift n to ℕ using (zero_lt_two.trans n2).le,
  norm_cast at n2,
  obtain ⟨k, rfl⟩|⟨p, hp, hdvd, hodd⟩ := n.eq_two_pow_or_exists_odd_prime_and_dvd,
  { refine ⟨4, ⟨2 ^ (k - 2), _⟩, or.inl rfl⟩,
    norm_cast,
    calc 2 ^ k
        = 2 ^ 2 * 2 ^ (k - 2) : (pow_mul_pow_sub _ _).symm
    ... = 4 * 2 ^ (k - 2) : by norm_num,

    rcases k with (_|_|_),
    { exfalso, norm_num at n2 },
    { exfalso, exact lt_irrefl _ n2 },
    { exact le_add_self } },
  { rw nat.prime_iff_prime_int at hp,
    rw ←int.odd_coe_nat at hodd,
    exact ⟨p, int.coe_nat_dvd.mpr hdvd, or.inr ⟨hp, hodd⟩⟩ },
end

lemma associated_of_dvd {a p : ℤ}
  (ha : odd_prime_or_four a)
  (hp : odd_prime_or_four p)
  (h: p ∣ a) : associated p a :=
begin
  obtain (rfl|⟨ap, aodd⟩) := ha;
  obtain (rfl|⟨pp, podd⟩) := hp,
  { refl },
  { exfalso,
    have h0 : (4 : ℤ) = 2 ^ 2,
    { norm_num },
    rw h0 at h,
    refine int.even_iff_not_odd.mp _ podd,
    rw even_iff_two_dvd,
    apply (associated.dvd _),
    exact ((pp.dvd_prime_iff_associated int.prime_two).mp (pp.dvd_of_dvd_pow h)).symm },
  { exfalso,
    rw int.odd_iff_not_even at aodd,
    refine aodd _,
    rw even_iff_two_dvd,
    refine (dvd_trans _ h),
    norm_num },
  { rwa prime.dvd_prime_iff_associated pp ap at h }
end

lemma dvd_or_dvd {a p x : ℤ}
  (ha : odd_prime_or_four a)
  (hp : odd_prime_or_four p)
  (hdvd : p ∣ a * x) : p ∣ a ∨ p ∣ x :=
begin
  obtain (rfl|⟨pp, podd⟩) := hp,
  { obtain (rfl|⟨ap, aodd⟩) := ha,
    { exact or.inl dvd_rfl },
    { right,
      have : (4 : ℤ) = 2 ^ 2,
      { norm_num },
      rw this at hdvd ⊢,
      apply int.prime_two.pow_dvd_of_dvd_mul_left _ _ hdvd,
      rwa [←even_iff_two_dvd, ←int.odd_iff_not_even] } },
  { exact (pp.dvd_or_dvd hdvd) }
end

lemma exists_associated_mem_of_dvd_prod''
  {p : ℤ} (hp : odd_prime_or_four p)
  {s : multiset ℤ}
  (hs : ∀ r ∈ s, odd_prime_or_four r)
  (hdvd : p ∣ s.prod) :
  ∃ q ∈ s, associated p q :=
begin
  induction s using multiset.induction_on with a s ih hs generalizing hs hdvd,
  { simpa [hp.not_unit, ←is_unit_iff_dvd_one] using hdvd },
  { rw [multiset.prod_cons] at hdvd,
    have := hs a (multiset.mem_cons_self _ _),
    obtain h|h := dvd_or_dvd this hp hdvd,
    { exact ⟨a, multiset.mem_cons_self _ _, associated_of_dvd this hp h⟩ },
    { obtain ⟨q, hq₁, hq₂⟩ := ih (λ r hr, hs _ (multiset.mem_cons_of_mem hr)) h,
      exact ⟨q, multiset.mem_cons_of_mem hq₁, hq₂⟩ } }
end

lemma factors_unique_prod' : ∀{f g : multiset ℤ},
  (∀x∈f, odd_prime_or_four x) →
  (∀x∈g, odd_prime_or_four x) →
  (associated f.prod g.prod) →
  multiset.rel associated f g :=
begin
  intros f,
  refine multiset.induction_on f _ _,
  { rintros g - hg h,
    rw [multiset.prod_zero] at h,
    rw [multiset.rel_zero_left],
    apply multiset.eq_zero_of_forall_not_mem,
    intros x hx,
    apply (hg x hx).not_unit,
    rw is_unit_iff_dvd_one,
    exact dvd_trans (multiset.dvd_prod hx) h.symm.dvd },
  { intros p f ih g hf hg hfg,
    have hp := hf p (multiset.mem_cons_self _ _),
    have hdvd : p ∣ g.prod,
    { rw [←hfg.dvd_iff_dvd_right, multiset.prod_cons],
      exact dvd_mul_right _ _ },
    obtain ⟨b, hbg, hb⟩ := exists_associated_mem_of_dvd_prod'' hp hg hdvd,
    rw ← multiset.cons_erase hbg,
    apply multiset.rel.cons hb,
    apply ih _ _ _,
    { exact (λ q hq, hf _ (multiset.mem_cons_of_mem hq)) },
    { exact (λ q (hq : q ∈ g.erase b), hg q (multiset.mem_of_mem_erase hq)) },
    { apply associated.of_mul_left _ hb hp.ne_zero,
      rwa [← multiset.prod_cons, ← multiset.prod_cons, multiset.cons_erase hbg] } },
end

/-- The odd factors. -/
noncomputable def odd_factors (x : ℤ) := multiset.filter odd (unique_factorization_monoid.normalized_factors x)

lemma odd_factors.zero : odd_factors 0 = 0 := rfl

lemma odd_factors.not_two_mem (x : ℤ) : (2 : ℤ) ∉ odd_factors x :=
begin
  simp only [odd_factors, even_bit0, not_true, not_false_iff, int.odd_iff_not_even, and_false,
    multiset.mem_filter],
end

lemma odd_factors.nonneg {z a : ℤ} (ha : a ∈ odd_factors z) : 0 ≤ a :=
begin
  simp only [odd_factors, multiset.mem_filter] at ha,
  exact int.nonneg_of_normalize_eq_self
    (unique_factorization_monoid.normalize_normalized_factor a ha.1)
end

lemma odd_factors.pow (z : ℤ) (n : ℕ) : odd_factors (z ^ n) = n • odd_factors z :=
begin
  simp only [odd_factors],
  rw [unique_factorization_monoid.normalized_factors_pow, multiset.filter_nsmul],
end

/-- The exponent of `2` in the factorization. -/
noncomputable def even_factor_exp (x : ℤ) := multiset.count 2 (unique_factorization_monoid.normalized_factors x)

lemma even_factor_exp.def (x : ℤ) : even_factor_exp x = multiset.count 2 (unique_factorization_monoid.normalized_factors x) := rfl

lemma even_factor_exp.zero : even_factor_exp 0 = 0 := rfl

lemma even_factor_exp.pow (z : ℤ) (n : ℕ) : even_factor_exp (z ^ n) = n * even_factor_exp z :=
begin
  simp only [even_factor_exp],
  rw [unique_factorization_monoid.normalized_factors_pow, multiset.count_nsmul]
end

lemma even_and_odd_factors'' (x : ℤ) :
  unique_factorization_monoid.normalized_factors x = (unique_factorization_monoid.normalized_factors x).filter (eq 2) + odd_factors x :=
begin
  by_cases hx : x = 0,
  { rw [hx, unique_factorization_monoid.normalized_factors_zero, odd_factors.zero, multiset.filter_zero,
    add_zero] },
  simp [even_factor_exp, odd_factors],
  rw multiset.filter_add_filter,
  convert (add_zero _).symm,
  { rw multiset.filter_eq_self,
    intros a ha,
    have hprime : prime a := unique_factorization_monoid.prime_of_normalized_factor a ha,
    have := unique_factorization_monoid.normalize_normalized_factor a ha,
    rw ←int.coe_nat_abs_eq_normalize at this,
    rw ←this at hprime,
    rw ←this,
    norm_cast,
    rw [eq_comm, nat.odd_iff],
    apply nat.prime.eq_two_or_odd,
    exact nat.prime_iff_prime_int.mpr hprime },
  { rw multiset.filter_eq_nil,
    rintros a ha ⟨rfl, hodd⟩,
    norm_num at hodd },
end

lemma even_and_odd_factors' (x : ℤ) :
  unique_factorization_monoid.normalized_factors x = multiset.repeat 2 (even_factor_exp x) + odd_factors x :=
begin
  convert even_and_odd_factors'' x,
  simp [even_factor_exp, ←multiset.filter_eq],
end

lemma even_and_odd_factors (x : ℤ) (hx : x ≠ 0) : associated x (2 ^ (even_factor_exp x) * (odd_factors x).prod) :=
begin
  convert (unique_factorization_monoid.normalized_factors_prod hx).symm,
  simp [even_factor_exp],
  rw [multiset.pow_count, ←multiset.prod_add, ←even_and_odd_factors'' x]
end

lemma factors_2_even {z : ℤ} (hz : z ≠ 0) : even_factor_exp (4 * z) = 2 + even_factor_exp z :=
begin
  have h₀ : (4 : ℤ) ≠ 0 := four_ne_zero,
  have h₁ : (2 : int) ^ 2 = 4,
  { norm_num },
  simp [even_factor_exp],
  rw [unique_factorization_monoid.normalized_factors_mul h₀ hz, multiset.count_add, ←h₁,
    unique_factorization_monoid.normalized_factors_pow, multiset.count_nsmul,
    unique_factorization_monoid.normalized_factors_irreducible int.prime_two.irreducible,
    int.normalize_of_nonneg zero_le_two, multiset.count_singleton_self, mul_one],
end

-- most useful with  (hz : even (even_factor_exp z))
/-- Odd factors or `4`. -/
noncomputable def factors_odd_prime_or_four (z : ℤ) : multiset ℤ :=
multiset.repeat 4 (even_factor_exp z / 2) + odd_factors z

lemma factors_odd_prime_or_four.nonneg {z a : ℤ} (ha : a ∈ factors_odd_prime_or_four z) : 0 ≤ a :=
begin
  simp only [factors_odd_prime_or_four, multiset.mem_add] at ha,
  cases ha,
  { rw multiset.eq_of_mem_repeat ha, norm_num },
  { exact odd_factors.nonneg ha }
end

lemma factors_odd_prime_or_four.prod'
  {a : ℤ}
  (ha : 0 < a)
  (heven : even (even_factor_exp a)) :
  (factors_odd_prime_or_four a).prod = a :=
begin
  apply int.eq_of_associated_of_nonneg,
  { have := unique_factorization_monoid.normalized_factors_prod ha.ne',
    apply associated.trans _ this,
    obtain ⟨m, hm⟩ := even_iff_two_dvd.mp heven,
    rw [even_and_odd_factors' _, multiset.prod_add, factors_odd_prime_or_four, multiset.prod_add,
      hm, nat.mul_div_right _ zero_lt_two, multiset.prod_repeat, multiset.prod_repeat, pow_mul],
    exact associated.refl _ },
  { apply multiset.prod_nonneg,
    apply factors_odd_prime_or_four.nonneg },
  { exact ha.le },
end

lemma factors_odd_prime_or_four.associated'
  {a : ℤ}
  {f : multiset ℤ}
  (hf : ∀x∈f, odd_prime_or_four x)
  (ha : 0 < a)
  (heven : even (even_factor_exp a))
  (hassoc : associated f.prod a) :
  multiset.rel associated f (factors_odd_prime_or_four a) :=
begin
  apply factors_unique_prod' hf,
  { intros x hx,
    simp only [factors_odd_prime_or_four, multiset.mem_add] at hx,
    apply or.imp _ _ hx,
    { exact multiset.eq_of_mem_repeat },
    { simp only [odd_factors, multiset.mem_filter],
      exact and.imp_left (unique_factorization_monoid.prime_of_normalized_factor _) } },
  { rwa factors_odd_prime_or_four.prod' ha heven, }
end

lemma factors_odd_prime_or_four.unique'
  {a : ℤ}
  {f : multiset ℤ}
  (hf : ∀x∈f, odd_prime_or_four x)
  (hf' : ∀x∈f, (0 : ℤ) ≤ x)
  (ha : 0 < a)
  (heven : even (even_factor_exp a))
  (hassoc : associated f.prod a) :
  f = (factors_odd_prime_or_four a) :=
begin
  rw ←multiset.rel_eq,
  apply multiset.rel.mono (factors_odd_prime_or_four.associated' hf ha heven hassoc),
  intros x hx y hy hxy,
  exact int.eq_of_associated_of_nonneg hxy (hf' x hx) (factors_odd_prime_or_four.nonneg hy)
end

lemma factors_odd_prime_or_four.pow
  (z : ℤ) (n : ℕ) (hz : even (even_factor_exp z)) :
  factors_odd_prime_or_four (z ^ n) = n • factors_odd_prime_or_four z :=
begin
  simp only [factors_odd_prime_or_four, nsmul_add, multiset.nsmul_repeat, even_factor_exp.pow,
    nat.mul_div_assoc _ (even_iff_two_dvd.mp hz), odd_factors.pow],
end
