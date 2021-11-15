import ring_theory.polynomial.cyclotomic

open polynomial nat
open_locale big_operators

lemma is_root_cyclotomic_iff' {n : ℕ} {K : Type*} [field K] (hpos : 0 < n) {μ : K}
  (h : ∃ ζ : K, is_primitive_root ζ n) : is_primitive_root μ n ↔ is_root (cyclotomic n K) μ :=
begin
  obtain ⟨ζ, hζ⟩ := h,
  rw [← mem_roots (cyclotomic_ne_zero n K), cyclotomic_eq_prod_X_sub_primitive_roots hζ,
    roots_prod_X_sub_C, ← finset.mem_def, ← mem_primitive_roots hpos],
end

lemma is_root_prod {R : Type*} [comm_ring R] [is_domain R] {ι : Type*}
  (s : finset ι) (p : ι → polynomial R) (x : R) :
  is_root (∏ j in s, p j) x ↔ ∃ i ∈ s, is_root (p i) x :=
by simp only [is_root, eval_prod, finset.prod_eq_zero_iff]

-- trying out this order to solve some `rw` issues, c.f.
-- https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/rw.20.2B.20apply_instance
lemma is_root_of_unity_iff {n : ℕ} (h : 0 < n) (R : Type*) [comm_ring R] [is_domain R] {ζ : R} :
  ζ ^ n = 1 ↔ ∃ i ∈ n.divisors, (cyclotomic i R).is_root ζ :=
by rw [←mem_nth_roots h, nth_roots, mem_roots $ X_pow_sub_C_ne_zero h _,
       C_1, ←prod_cyclotomic_eq_X_pow_sub_one h, is_root_prod]; apply_instance

@[nontriviality] lemma is_primitive_root.trivial {M : Type*}
  [comm_monoid M] [subsingleton M] (x : M) : is_primitive_root x 1 :=
⟨subsingleton.elim _ _, λ _ _, one_dvd _⟩

lemma is_primitive_root.zero {R : Type*} [comm_semiring R] [nontrivial R] :
  is_primitive_root (0 : R) 0 :=
-- why does simpa need so much hand-holding...
⟨pow_zero 0, λ l hl, by simpa [zero_pow_eq, show ∀ p, ¬p → false ↔ p, by tauto!] using hl⟩

lemma is_primitive_root.order_of {M : Type*} [comm_monoid M] (ζ : M) :
  is_primitive_root ζ (order_of ζ) :=
⟨pow_order_of_eq_one ζ, λ l, order_of_dvd_of_pow_eq_one⟩

lemma is_primitive_root.unique {n m : ℕ} {M : Type*} [comm_monoid M] {ζ : M}
  (hn : is_primitive_root ζ n) (hm : is_primitive_root ζ m) : n = m :=
begin
  wlog hnm : n ≤ m,
  rcases hnm.eq_or_lt with rfl | hnm,
  { refl },
  rcases n.eq_zero_or_pos with rfl | hn',
  { exact (zero_dvd_iff.mp $ hn.dvd_of_pow_eq_one m hm.pow_eq_one).symm },
  exact absurd hn.pow_eq_one (hm.pow_ne_one_of_pos_of_lt hn' hnm)
end

lemma is_primitive_root.eq_order_of {n : ℕ} {M : Type*} [comm_monoid M] {ζ : M}
  (h : is_primitive_root ζ n) : n = order_of ζ :=
h.unique (is_primitive_root.order_of ζ)

-- equivalent statement for n : ℕ availab,e but too lazy
lemma is_primitive_root_iff {n : ℕ+} {M : Type*} [comm_monoid M] (ζ : M) :
  is_primitive_root ζ n ↔ ζ ^ (n : ℕ) = 1 ∧ ∀ l : ℕ, 0 < l → l < n → ζ ^ l ≠ 1 :=
begin
  refine ⟨λ h, ⟨h.pow_eq_one, λ l hl' hl, _⟩, λ ⟨hζ, hl⟩, is_primitive_root.mk_of_lt ζ n.pos hζ hl⟩,
  rw h.eq_order_of at hl,
  exact pow_ne_one_of_lt_order_of' hl'.ne' hl,
end

lemma is_not_primitive_root_iff {n : ℕ} {M : Type*} [comm_monoid M] (ζ : M) :
  ¬ is_primitive_root ζ n ↔ order_of ζ ≠ n :=
⟨λ h hn, h $ hn ▸ is_primitive_root.order_of ζ,
 λ h hn, h.symm $ hn.unique $ is_primitive_root.order_of ζ⟩

open finset

lemma nat.mem_divisors_self (n : ℕ) (h : n ≠ 0) : n ∈ n.divisors := by simpa

-- this needs to replace `polynomial.order_of_root_cyclotomic_eq` when it is merged
lemma is_root_cyclotomic_iff {n : ℕ} {K : Type*} [field K] {μ : K} (hn : (↑n : K) ≠ 0) :
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
  rw is_not_primitive_root_iff at hnμ,
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

namespace polynomial

lemma cyclotomic_prime_mul_X_sub_one (R : Type*) [comm_ring R] (n : ℕ) [hn : fact (nat.prime n)] :
  (cyclotomic n R) * (X - 1) = X ^ n - 1 :=
begin
  rw [← (eq_cyclotomic_iff (prime.pos hn.out) _).1 rfl, prime.proper_divisors hn.out,
    prod_singleton, cyclotomic_one]
end

end polynomial
