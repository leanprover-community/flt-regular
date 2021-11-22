import ring_theory.polynomial.cyclotomic

open polynomial nat
open_locale big_operators

-- trying out this order to solve some `rw` issues, c.f.
-- https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/rw.20.2B.20apply_instance
lemma is_root_of_unity_iff {n : ℕ} (h : 0 < n) (R : Type*) [comm_ring R] [is_domain R] {ζ : R} :
  ζ ^ n = 1 ↔ ∃ i ∈ n.divisors, (cyclotomic i R).is_root ζ :=
by rw [←mem_nth_roots h, nth_roots, mem_roots $ X_pow_sub_C_ne_zero h _,
       C_1, ←prod_cyclotomic_eq_X_pow_sub_one h, is_root_prod]; apply_instance

open finset

-- `is_root_cyclotomic_iff` is strictly stronger, this is a necessary intermediate result
private lemma is_root_cyclotomic_iff' {n : ℕ} {K : Type*} [field K] {μ : K} (hn : (n : K) ≠ 0) :
  is_primitive_root μ n ↔ is_root (cyclotomic n K) μ :=
begin
  -- in this proof, `o` stands for `order_of μ`
  have hnpos : 0 < n := (show n ≠ 0, by { rintro rfl, contradiction }).bot_lt,
  refine ⟨is_root_cyclotomic hnpos, λ hμ, _⟩,
  have hμn : μ ^ n = 1,
  { rw is_root_of_unity_iff hnpos,
    exact ⟨n, n.mem_divisors_self hnpos.ne', hμ⟩ },
  by_contra hnμ,
  have ho : 0 < order_of μ,
  { apply order_of_pos',
    rw is_of_fin_order_iff_pow_eq_one,
    exact ⟨n, hnpos, hμn⟩ },
  have := pow_order_of_eq_one μ,
  rw is_root_of_unity_iff ho at this,
  obtain ⟨i, hio, hiμ⟩ := this,
  replace hio := nat.dvd_of_mem_divisors hio,
  rw is_primitive_root.not_iff at hnμ,
  rw ←order_of_dvd_iff_pow_eq_one at hμn,
  have key  : i < n := (nat.le_of_dvd ho hio).trans_lt ((nat.le_of_dvd hnpos hμn).lt_of_ne hnμ),
  have key' : i ∣ n := hio.trans hμn,
  rw ←polynomial.dvd_iff_is_root at hμ hiμ,
  have hni : {i, n} ⊆ n.divisors,
  { simpa [insert_subset, key'] using hnpos.ne' },
  obtain ⟨k, hk⟩ := hiμ,
  obtain ⟨j, hj⟩ := hμ,
  have := prod_cyclotomic_eq_X_pow_sub_one hnpos K,
  rw [←prod_sdiff hni, prod_pair key.ne, hk, hj] at this,
  replace hn := (X_pow_sub_one_separable_iff.mpr hn).squarefree,
  rw [←this, squarefree] at hn,
  contrapose! hn,
  refine ⟨X - C μ, ⟨(∏ x in n.divisors \ {i, n}, cyclotomic x K) * k * j, by ring⟩, _⟩,
  simp [polynomial.is_unit_iff_degree_eq_zero]
end

-- this needs to replace `polynomial.order_of_root_cyclotomic_eq` when it is merged
lemma is_root_cyclotomic_iff {n : ℕ} {R : Type*} [comm_ring R] [is_domain R]
  {μ : R} (hn : (n : R) ≠ 0) : is_primitive_root μ n ↔ is_root (cyclotomic n R) μ :=
begin
  let f := algebra_map R (fraction_ring R),
  have hf : function.injective f := is_localization.injective _ le_rfl,
  rw [←is_root_map_iff hf, ←is_primitive_root.map_iff_of_injective hf,
      map_cyclotomic, ←is_root_cyclotomic_iff'],
  simpa only [f.map_nat_cast, hn] using f.injective_iff.mp hf n
end

lemma multiset.empty_or_exists_mem {α} (s : multiset α) : s = 0 ∨ ∃ a, a ∈ s :=
begin
  rcases eq_or_ne s 0 with rfl | h,
  { exact or.inl rfl },
  exact or.inr (multiset.exists_mem_of_ne_zero h)
end

lemma roots.le_of_dvd {R} [comm_ring R] [is_domain R] {p q : polynomial R} (h : q ≠ 0) :
   p ∣ q → roots p ≤ roots q :=
begin
  classical,
  rintro ⟨k, rfl⟩,
  rw multiset.le_iff_exists_add,
  exact ⟨k.roots, roots_mul h⟩
end

lemma cyclotomic.dvd_X_pow_sub_one {n : ℕ} {R} [comm_ring R] :(cyclotomic n R) ∣ X ^ n - 1 :=
begin
  rcases n.eq_zero_or_pos with rfl | hn,
  { simp },
  refine ⟨∏ i in n.proper_divisors, cyclotomic i R, _⟩,
  rw [←prod_cyclotomic_eq_X_pow_sub_one hn,
      divisors_eq_proper_divisors_insert_self_of_pos hn, prod_insert],
  exact proper_divisors.not_self_mem
end

--if there are no roots OK, otherwise use `is_primitive_root.nth_roots_nodup`
lemma roots_cyclotomic_nodup {n : ℕ} {R : Type*} [comm_ring R] [is_domain R] (hn : (n : R) ≠ 0) :
  (cyclotomic n R).roots.nodup :=
begin
  have hn' : 0 < n := (show n ≠ 0, by { rintro rfl, contradiction }).bot_lt,
  obtain h | ⟨ζ, hζ⟩ := (cyclotomic n R).roots.empty_or_exists_mem,
  { exact h.symm ▸ multiset.nodup_zero },
  rw [mem_roots $ cyclotomic_ne_zero n R, ←is_root_cyclotomic_iff hn] at hζ,
  refine multiset.nodup_of_le (roots.le_of_dvd (X_pow_sub_C_ne_zero hn' 1)
                               cyclotomic.dvd_X_pow_sub_one) _,
  exact hζ.nth_roots_nodup
end

lemma primitive_roots_eq_roots_cyclotomic {n : ℕ} {R : Type*} [comm_ring R] [is_domain R]
  (hn : (n : R) ≠ 0) : primitive_roots n R = ⟨(cyclotomic n R).roots, roots_cyclotomic_nodup hn⟩ :=
let hn' : 0 < n := (show n ≠ 0, by { rintro rfl, contradiction }).bot_lt in
by { ext, simp [cyclotomic_ne_zero n R, ←is_root_cyclotomic_iff hn, mem_primitive_roots hn'] }

namespace polynomial

lemma cyclotomic_prime_mul_X_sub_one (R : Type*) [comm_ring R] (n : ℕ) [hn : fact (nat.prime n)] :
  (cyclotomic n R) * (X - 1) = X ^ n - 1 :=
begin
  rw [← (eq_cyclotomic_iff (prime.pos hn.out) _).1 rfl, prime.proper_divisors hn.out,
    prod_singleton, cyclotomic_one]
end

end polynomial
