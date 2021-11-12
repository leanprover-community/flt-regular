import ring_theory.polynomial.cyclotomic

open polynomial
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

-- trying out this order and the ⦃⦄ to solve some `rw` issues, c.f.
-- https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/rw.20.2B.20apply_instance
lemma is_root_of_unity_iff {n : ℕ} (h : 0 < n) ⦃R : Type*⦄ [comm_ring R] [is_domain R] {ζ : R} :
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

lemma is_primitive_root.order_of {M : Type*} [comm_monoid M] {ζ : M} :
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
h.unique is_primitive_root.order_of

lemma is_primitive_root_iff {n : ℕ+} {M : Type*} [comm_monoid M] (ζ : M) :
  is_primitive_root ζ n ↔ ζ ^ (n : ℕ) = 1 ∧ ∀ l : ℕ, 0 < l → l < n → ζ ^ l ≠ 1 :=
begin
  refine ⟨λ h, ⟨h.pow_eq_one, λ l hl' hl, _⟩, λ ⟨hζ, hl⟩, is_primitive_root.mk_of_lt ζ n.pos hζ hl⟩,
  rw h.eq_order_of at hl,
  exact pow_ne_one_of_lt_order_of' hl'.ne' hl,
end

lemma is_root_cyclotomic_iff {n : ℕ} {K : Type*} [field K] {μ : K} (hn : (↑n : K) ≠ 0)
  : is_primitive_root μ n ↔ is_root (cyclotomic n K) μ :=
begin
  have : n ≠ 0, by { rintro rfl, contradiction },
  lift n to ℕ+ using this.bot_lt,
  refine ⟨is_root_cyclotomic n.pos, λ hμ, _⟩,
  have hμ' : μ ^ (n : ℕ) = 1,
  { rw is_root_of_unity_iff n.pos,
    exact ⟨n, by simp /- n ∈ divisors n is not a lemma... -/, hμ⟩ },
  rw is_primitive_root_iff,
  refine ⟨hμ', λ l hl' hl hlμ, _⟩,
  rw is_root_of_unity_iff hl' at hlμ,
  obtain ⟨i, hi, hμ⟩ := hlμ,
  have : i < n := (nat.le_of_dvd hl' (nat.dvd_of_mem_divisors hi)).trans_lt hl,
  sorry
  -- WILL FINISH TODAY!
  -- this isn't the right way, `by_contra` earlier is better because we get
  -- direct access to `order_of`, which has a good api
end
