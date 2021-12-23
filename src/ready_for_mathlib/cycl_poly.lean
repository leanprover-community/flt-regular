import ready_for_mathlib.multiplicity
import ready_for_mathlib.roots_of_unity
import ready_for_mathlib.totient

import ring_theory.polynomial.cyclotomic.basic

open polynomial is_primitive_root

lemma cyclotomic.is_primitive (n : ℕ) (R : Type*) [comm_ring R] : (cyclotomic n R).is_primitive :=
(cyclotomic.monic n R).is_primitive

lemma cyclotomic_injective {R : Type*} [comm_ring R] [is_domain R] [char_zero R] :
  function.injective (λ n, cyclotomic n R) :=
begin
  intros n m hnm,
  simp only at hnm,
  by_cases hzero : n = 0,
  { rw [hzero] at hnm ⊢,
    rw [cyclotomic_zero] at hnm,
    replace hnm := congr_arg nat_degree hnm,
    rw [nat_degree_one, nat_degree_cyclotomic] at hnm,
    by_contra,
    exact (nat.totient_pos (zero_lt_iff.2 (ne.symm h))).ne hnm },
  { rw [← map_cyclotomic_int _ R, ← map_cyclotomic_int _ R] at hnm,
    replace hnm := map_injective (int.cast_ring_hom R) int.cast_injective hnm,
    replace hnm := congr_arg (map (int.cast_ring_hom ℂ)) hnm,
    rw [map_cyclotomic_int, map_cyclotomic_int] at hnm,
    have hprim := complex.is_primitive_root_exp _ hzero,
    have hroot := (is_root_cyclotomic_iff (by exact_mod_cast hzero)).2 hprim,
    rw [hnm] at hroot,
    have hmzero : m ≠ 0 := λ h, by simpa [h] using hroot,
    rw [is_root_cyclotomic_iff] at hroot,
    { replace hprim := is_primitive_root.eq_order_of hprim,
      rwa [← is_primitive_root.eq_order_of hroot] at hprim },
    { exact nat.cast_ne_zero.mpr hmzero } }
end

lemma cyclotomic_eq_minpoly_rat {n : ℕ} {K : Type*} [field K] {μ : K}
  (h : is_primitive_root μ n) (hpos : 0 < n) [char_zero K] :
  cyclotomic n ℚ = minpoly ℚ μ :=
begin
  rw [← map_cyclotomic_int, cyclotomic_eq_minpoly h hpos],
  exact (minpoly.gcd_domain_eq_field_fractions _ (is_integral h hpos)).symm
end

lemma cyclotomic.irreducible_rat {n : ℕ} (hpos : 0 < n) : irreducible (cyclotomic n ℚ) :=
begin
  rw [← map_cyclotomic_int],
  exact (is_primitive.int.irreducible_iff_irreducible_map_cast (cyclotomic.is_primitive n ℤ)).1
    (cyclotomic.irreducible hpos),
end

lemma cyclotomic.is_coprime_rat {n m : ℕ} (h : n ≠ m) :
  is_coprime (cyclotomic n ℚ) (cyclotomic m ℚ) :=
begin
  rcases n.eq_zero_or_pos with rfl | hnzero,
  { exact is_coprime_one_left },
  rcases m.eq_zero_or_pos with rfl | hmzero,
  { exact is_coprime_one_right },
  rw (irreducible.coprime_iff_not_dvd $ cyclotomic.irreducible_rat $ hnzero),
  exact (λ hdiv, h $ cyclotomic_injective $ eq_of_monic_of_associated (cyclotomic.monic n ℚ)
    (cyclotomic.monic m ℚ) $ irreducible.associated_of_dvd (cyclotomic.irreducible_rat
    hnzero) (cyclotomic.irreducible_rat hmzero) hdiv),
end

@[simp] lemma cyclotomic_expand_eq_cyclotomic {p n : ℕ} (hp : nat.prime p) (hdiv : p ∣ n)
  (R : Type*) [comm_ring R] : expand R p (cyclotomic n R) = cyclotomic (n * p) R :=
begin
  by_cases hzero : n = 0,
  { simp [hzero] },
  suffices : expand ℤ p (cyclotomic n ℤ) = cyclotomic (n * p) ℤ,
  { rw [← map_cyclotomic_int, ← map_expand, this, map_cyclotomic_int] },
  refine eq_of_monic_of_dvd_of_nat_degree_le (cyclotomic.monic _ _)
    ((cyclotomic.monic n ℤ).expand (zero_lt_iff.2 (nat.prime.ne_zero hp))) _ _,
  { have hpos := nat.mul_pos (zero_lt_iff.mpr hzero) (nat.prime.pos hp),
    have hprim := complex.is_primitive_root_exp _ hpos.ne.symm,
    rw [cyclotomic_eq_minpoly hprim hpos],
    refine @minpoly.gcd_domain_dvd ℤ ℂ ℚ _ _ _ _ _ _ _ _ complex.algebra (algebra_int ℂ) _ _
      (is_primitive_root.is_integral hprim hpos) _ ((cyclotomic.monic n ℤ).expand
      (nat.prime.pos hp)).is_primitive _,
    rw [aeval_def, ← eval_map, map_expand, map_cyclotomic, expand_eval, ← is_root.def,
      is_root_cyclotomic_iff],
    { convert is_primitive_root.pow_of_div hprim (nat.prime.ne_zero hp) (dvd_mul_left p n),
      rw [nat.mul_div_cancel _ (nat.prime.pos hp)] },
    { exact_mod_cast hzero } },
  { rw [nat_degree_expand, nat_degree_cyclotomic, nat_degree_cyclotomic, mul_comm n,
      nat.totient_mul_prime_div hp hdiv, mul_comm] }
end

@[simp] lemma cyclotomic_expand_eq_cyclotomic_mul {p n : ℕ} (hp : nat.prime p) (hdiv : ¬p ∣ n)
  (R : Type*) [comm_ring R] :
  expand R p (cyclotomic n R) = (cyclotomic (n * p) R) * (cyclotomic n R) :=
begin
  cases nat.eq_zero_or_pos n with hzero hnpos,
  { simp [hzero] },
  suffices : expand ℤ p (cyclotomic n ℤ) = (cyclotomic (n * p) ℤ) * (cyclotomic n ℤ),
  { rw [← map_cyclotomic_int, ← map_expand, this, polynomial.map_mul, map_cyclotomic_int] },
  refine eq_of_monic_of_dvd_of_nat_degree_le (monic_mul (cyclotomic.monic _ _)
    (cyclotomic.monic _ _)) ((cyclotomic.monic n ℤ).expand hp.pos) _ _,
  { refine (is_primitive.int.dvd_iff_map_cast_dvd_map_cast _ _ (is_primitive.mul
      (cyclotomic.is_primitive (n * p) ℤ) (cyclotomic.is_primitive n ℤ))
      ((cyclotomic.monic n ℤ).expand hp.pos).is_primitive).2 _,
    rw [polynomial.map_mul, map_cyclotomic_int, map_cyclotomic_int, map_expand, map_cyclotomic_int],
    refine is_coprime.mul_dvd (cyclotomic.is_coprime_rat (λ h, _)) _ _,
    { replace h : n * p = n * 1 := by simp [h],
      exact nat.prime.ne_one hp (nat.eq_of_mul_eq_mul_left hnpos h) },
    { have hpos : 0 < n * p := mul_pos hnpos hp.pos,
      have hprim := complex.is_primitive_root_exp _ hpos.ne',
      rw [cyclotomic_eq_minpoly_rat hprim hpos],
      refine @minpoly.dvd ℚ ℂ _ _ algebra_rat _ _ _,
      rw [aeval_def, ← eval_map, map_expand, map_cyclotomic, expand_eval, ← is_root.def,
        is_root_cyclotomic_iff],
      { convert is_primitive_root.pow_of_div hprim hp.ne_zero (dvd_mul_left p n),
        rw [nat.mul_div_cancel _ (nat.prime.pos hp)] },
      { exact_mod_cast hnpos.ne' } },
    { have hprim := complex.is_primitive_root_exp _ hnpos.ne.symm,
      rw [cyclotomic_eq_minpoly_rat hprim hnpos],
      refine @minpoly.dvd ℚ ℂ _ _ algebra_rat _ _ _,
      rw [aeval_def, ← eval_map, map_expand, expand_eval, ← is_root.def,
        ← cyclotomic_eq_minpoly_rat hprim hnpos, map_cyclotomic, is_root_cyclotomic_iff],
      { exact is_primitive_root.pow_of_prime hprim hp hdiv },
      { exact_mod_cast hnpos.ne' } } },
  { rw [nat_degree_expand, nat_degree_cyclotomic, nat_degree_mul (cyclotomic_ne_zero _ ℤ)
      (cyclotomic_ne_zero _ ℤ), nat_degree_cyclotomic, nat_degree_cyclotomic, mul_comm n,
      nat.totient_mul ((nat.prime.coprime_iff_not_dvd hp).2 hdiv),
      nat.totient_prime hp, mul_comm (p - 1), ← nat.mul_succ, nat.sub_one,
      nat.succ_pred_eq_of_pos hp.pos] }
end
