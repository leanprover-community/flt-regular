/-
Copyright (c) 2021 Alex J. Best. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best
-/
import ring_theory.roots_of_unity
import number_theory.number_field
import data.real.nnreal
import analysis.special_functions.pow
import field_theory.splitting_field
-- import generalisation_linter
import field_theory.is_alg_closed.basic
import field_theory.polynomial_galois_group
import field_theory.adjoin

open_locale nnreal
-- probably this isn't needed but is another annoying example of 0 < n vs n ≠ 0 causing library
-- search to fail on "obvious" lemmas
lemma eq_one_of_pow_eq_one {n : ℕ} (hn : 0 < n) {t : ℝ≥0} (h_pow : t ^ n = 1) : t = 1 :=
(pow_eq_one_iff hn.ne.symm).mp h_pow

section forward

lemma complex.abs_pow {n : ℕ} (x : ℂ) : complex.abs (x ^ n) = complex.abs x ^ n :=
is_absolute_value.abv_pow complex.abs x n

-- TODO maybe gen to is_R_or_C?
variables {K : Type*} [monoid K] {n : ℕ} (x : K) (hx : x ^ n = 1) (hn : 0 < n)
variables (φ : K →* ℂ)
include hx hn
open complex

-- The clean way to do this is to show that abs of phi is a monoid hom to ℝ≥0, and monoid homs take
-- roots of unity to roots of unity, and that roots of unity ℝ≥0 is trivial
lemma absolute_value_one : abs (φ x) = 1 :=
begin
  have h_pow : (abs (φ x)) ^ n = 1,
  { rw (_ : abs (φ x) ^ n = abs (φ x ^ n)),
    rw (_ : φ x ^ n = φ (x ^ n)),
    simp only [hx, complex.abs_one, monoid_hom.map_one],
    rw monoid_hom.map_pow,
    rw is_absolute_value.abv_pow complex.abs, },
  set t := abs (φ x),
  have : 0 ≤ t, from (φ x).abs_nonneg,
  clear_value t,
  lift t to ℝ≥0 using this,
  norm_cast at *,
  rwa pow_eq_one_iff at h_pow,
  exact hn.ne.symm,
end

end forward
section polynomial_map_lemmas

@[simp] lemma apply_eq_zero_iff_of_injective {R S : Type*} [add_zero_class R] [add_zero_class S]
  {f : R →+ S} (hf : function.injective f) : ∀ x, f x = 0 ↔ x = 0 :=
begin
  intro x,
  split; intro h,
  focus { apply hf,
    rw h, },
  all_goals { simp [h], },
end

variables {R S : Type*} [semiring R]

@[simp] lemma ring_hom.apply_eq_zero_iff_of_injective {R S : Type*} [non_assoc_semiring R]
  [non_assoc_semiring S] {f : R →+* S} (hf : function.injective f) : ∀ x, f x = 0 ↔ x = 0 :=
begin
  intro x,
  split; intro h,
  focus { apply hf,
    rw h, },
  all_goals { simp [h], },
end
variables {p : polynomial R}
namespace polynomial
@[simp] lemma map_eq_zero_of_injective [semiring S] {f : R →+* S}
  (hf : function.injective f) : p.map f = 0 ↔ p = 0 :=
by simp [polynomial.ext_iff, coeff_map, ring_hom.apply_eq_zero_iff_of_injective hf, coeff_zero]

lemma map_ne_zero_of_injective [semiring S] {f : R →+* S}
  (hf : function.injective f) (hp : p ≠ 0) : p.map f ≠ 0 := mt (map_eq_zero_of_injective hf).1 hp

lemma mem_roots_map_of_injective [comm_ring S] [is_domain S] {f : R →+* S} {x : S}
  (hf : function.injective f) (hp : p ≠ 0) : x ∈ (p.map f).roots ↔ p.eval₂ f x = 0 :=
begin
  rw mem_roots (show p.map f ≠ 0, by exact map_ne_zero_of_injective hf hp),
  dsimp only [is_root],
  rw polynomial.eval_map,
end
end polynomial
end polynomial_map_lemmas

section choose_lemma
lemma nat.choose_add_one (a c : ℕ) : nat.choose a c ≤ nat.choose (a + 1) c :=
by cases c; simp [nat.choose_succ_succ]

lemma nat.choose_add_le (a b c : ℕ) : nat.choose a c ≤ nat.choose (a + b) c :=
begin
  induction b with b_n b_ih,
  { simp, },
  exact le_trans b_ih (nat.choose_add_one (a + b_n) c),
end
lemma nat.choose_mono {a b : ℕ} (c : ℕ) (h : a ≤ b) : nat.choose a c ≤ nat.choose b c :=
begin
  rw ← add_tsub_cancel_of_le h,
  exact nat.choose_add_le a (b - a) c,
end
end choose_lemma

section polynomial
variables {R : Type*} [ring R]
open polynomial

@[simp]
lemma X_pow_mul_coeff_succ (p : polynomial R) (j i : ℕ) : (X ^ j * p).coeff (i + j) = p.coeff i :=
begin
  rw coeff_mul,
  simp only [coeff_X_pow, boole_mul],
  have : ∀ x ∈ finset.nat.antidiagonal (i + j), prod.fst x = j ↔ (j, i) = x,
  simp only [prod.forall, iff_self_and, finset.nat.mem_antidiagonal, prod.mk.inj_iff, eq_comm],
  intros a b hs hb,
  linarith,
  conv in (prod.fst _ = _)
  { simp only [this x H], },
  simp [add_comm],
end

@[simp]
lemma X_mul_coeff_succ (p : polynomial R) (i : ℕ) : (X * p).coeff (i + 1) = p.coeff i :=
by simpa using X_pow_mul_coeff_succ p 1 i

end polynomial
section
open multiset
@[simp] theorem multiset.powerset_len_empty {α : Type*} (n : ℕ) {s : multiset α} (h : s.card < n) :
  powerset_len n s = 0 :=
multiset.card_eq_zero.mp (by rw [card_powerset_len, nat.choose_eq_zero_of_lt h])

-- TODO maybe a finset version of this too
@[simp]
lemma multiset.powerset_len_card_add {α : Type*} (s : multiset α) {i : ℕ} (hi : 0 < i) :
  s.powerset_len (s.card + i) = 0 :=
begin
  apply multiset.powerset_len_empty,
  exact lt_add_of_pos_right (card s) hi,
end

@[simp] theorem multiset.powerset_len_map {α β : Type*} (f : α → β) (n : ℕ) (s : multiset α) :
  powerset_len n (s.map f) = (powerset_len n s).map (map f) :=
begin
  induction s using multiset.induction with t s ih generalizing n,
  { cases n,
    { simp [powerset_len_zero_left], },
    { simp [powerset_len_zero_right], }, },
  { cases n,
    { simp, },
    { simp [ih], }, },
end

@[simp] theorem powerset_len_val {α : Type*} (s : finset α) (i : ℕ) :
  (s.powerset_len i).val.map finset.val = s.1.powerset_len i :=
begin
  rw finset.powerset_len,
  dsimp only,
  rw map_pmap,
  dsimp only,
  rw pmap_eq_map,
  rw map_id',
end
end

section polynomial
variables {R : Type*} [comm_ring R]
open polynomial
/--
The degree of a product of polynomials is at most the sum of the degrees,
where the degree of the zero polynomial is ⊥.
-/
lemma degree_multiset_prod_le [nontrivial R] (t : multiset (polynomial R)) :
  t.prod.degree ≤ (t.map polynomial.degree).sum :=
begin
  refine multiset.induction_on t _ (λ a t ht, _), { simp },
  { simp only [multiset.prod_cons, multiset.map_cons, multiset.sum_cons],
    exact le_trans (degree_mul_le _ _) (add_le_add_left ht _), }
end

-- TODO lol I hope this monstrosity is golfable
-- TODO remove the hi hypothesis, lemma is true without
lemma multiset_prod_X_sub_C_coeff [nontrivial R] (t : multiset R) {i : ℕ} (hi : i ≤ t.card) :
  (t.map (λ x, (X - C x))).prod.coeff i =
  (-1) ^ (t.card - i) * ((t.powerset_len (t.card - i)).map multiset.prod).sum :=
begin
-- sorry; { -- hack to not recompile constantly TODO remove
  revert t i,
  apply' multiset.induction,
  { intros i hi,
    simp only [multiset.card_zero, le_zero_iff] at hi,
    simp only [hi, multiset.card_zero, mul_one, multiset.map_singleton, coeff_one_zero,
      multiset.sum_singleton, multiset.prod_zero, multiset.map_zero,
      multiset.powerset_len_zero_left, pow_zero], },
  intros a s h i his,
  simp only [sub_mul, multiset.map_cons, multiset.prod_cons, coeff_C_mul, coeff_sub,
    multiset.card_cons],
  simp only [multiset.card_cons] at his,
  by_cases his' : i = s.card + 1,
  { simp only [his', mul_one, multiset.map_singleton, multiset.sum_singleton, multiset.prod_zero,
      tsub_self, multiset.powerset_len_zero_left, pow_zero],
    have : degree (multiset.map (λ (x : R), X - C x) s).prod ≤ s.card,
    { have := degree_multiset_prod_le (multiset.map (λ (x : R), X - C x) s),
      simpa, },
    have : degree (multiset.map (λ (x : R), X - C x) s).prod < s.card + 1,
    { calc _ ≤ _ : this
          ...< _ : _,
      norm_cast,
      exact lt_add_one s.card, },
    have : (multiset.map (λ (x : R), X - C x) s).prod.coeff (s.card + 1) = 0,
    { apply coeff_eq_zero_of_degree_lt this, },
    simp only [this, sub_zero, mul_zero, X_mul_coeff_succ,
      h (le_refl _), mul_one, multiset.map_singleton, multiset.sum_singleton, multiset.prod_zero,
      tsub_self, multiset.powerset_len_zero_left, pow_zero], },
  have : i ≤ s.card := nat.lt_succ_iff.mp (lt_of_le_of_ne his his'),
  rw [nat.succ_sub this, multiset.powerset_len_cons],
  simp only [h this, multiset.prod_cons, function.comp_app, multiset.map_map, multiset.map_add,
    multiset.sum_add],
  cases i,
  { simp only [tsub_zero, multiset.prod_cons, mul_coeff_zero, nat.nat_zero_eq_zero, zero_sub,
      zero_mul, function.comp_app, coeff_X_zero],
    specialize h this,
    simp only [tsub_zero, nat.nat_zero_eq_zero] at h,
    rw [← mul_assoc, mul_comm a, neg_eq_neg_one_mul, ← mul_assoc, ← mul_assoc, ← pow_succ,
      mul_assoc],
    congr,
    have := (add_monoid_hom.mul_left a).map_multiset_sum,
    simp only [add_monoid_hom.coe_mul_left] at this,
    simp [this], },
  rw [X_mul_coeff_succ, mul_add, sub_eq_add_neg],
  congr,
  { have hii : i ≤ multiset.card s := nat.le_of_succ_le this,
    have : multiset.card s - i = multiset.card s - i.succ + 1, -- I miss omega :'(
    { zify [his, hii, this],
      simp only [int.coe_nat_succ],
      abel, },
    rw [h hii, this], },
  { rw [← mul_assoc, mul_comm a, neg_eq_neg_one_mul, ← mul_assoc, ← mul_assoc, ← pow_succ,
      mul_assoc], -- TODO this rearranging is repeat of above, is it golfable?
    congr,
    have := (add_monoid_hom.mul_left a).map_multiset_sum,
    simp only [add_monoid_hom.coe_mul_left] at this,
    simp [this], }
-- }
end


open_locale big_operators
lemma prod_X_sub_C_coeff {ι : Type*} [nontrivial R] (s : finset ι)
  (f : ι → R) {i : ℕ} (hs : i ≤ s.card) :
  (∏ i in s, (X - C (f i))).coeff i =
  (-1) ^ (s.card - i) * ∑ i in s.powerset_len (s.card - i), i.prod f :=
begin
  have := multiset_prod_X_sub_C_coeff (s.1.map f) (by simpa using hs),
  simp only [multiset.card_map, function.comp_app, multiset.map_map,
    multiset.powerset_len_map] at this,
  convert this,
  rw finset.sum_eq_multiset_sum,
  refine congr_arg multiset.sum _,
  rw ← powerset_len_val,
  rw multiset.map_map,
  congr,
end

end polynomial

section abv_sum
variables {R S ι : Type*} [ordered_semiring S] [semiring R] (abv : R → S)
variables [is_absolute_value abv] (f : ι → R) (s : finset ι)

open_locale big_operators

theorem is_absolute_value.abv_sum : abv (∑ i in s, f i) ≤ ∑ i in s, abv (f i) :=
begin
  classical,
  induction s using finset.induction with i s hi ih,
  { simp [is_absolute_value.abv_zero abv], },
  { rw [finset.sum_insert hi, finset.sum_insert hi],
    calc _ ≤ _ : is_absolute_value.abv_add abv _ _
       ... ≤ _ : add_le_add_left ih _, }
end
end abv_sum

section abv_prod
variables {R S ι : Type*} [linear_ordered_field S] [comm_semiring R] [nontrivial R] (abv : R → S)
variables [is_absolute_value abv] (f : ι → R) (s : finset ι)
open_locale big_operators

theorem is_absolute_value.abv_prod : abv (∏ i in s, f i) = ∏ i in s, abv (f i) :=
begin
  classical,
  induction s using finset.induction with i s hi ih,
  { simp [is_absolute_value.abv_one abv], },
  { rw [finset.prod_insert hi, finset.prod_insert hi],
    simp [is_absolute_value.abv_mul abv, ih], },
end
end abv_prod

-- section ajoin
-- variables {E : Type*} [field E] [number_field E] (x : E)
-- instance : char_zero ℚ⟮x⟯ := sorry
-- instance : number_field ℚ⟮x⟯ :=
-- begin
--   haveI : finite_dimensional ℚ ℚ⟮x⟯ := intermediate_field.adjoin.finite_dimensional (is_separable.is_integral ℚ x),
--   convert number_field.mk,
--   exact char_p.char_p_to_char_zero ℚ⟮x⟯,
--   convert _inst,
-- end
-- end ajoin

section backwards

open set finite_dimensional complex
open_locale classical
open_locale big_operators

variables {K : Type*} [field K] [number_field K] {n : ℕ} (x : K)
open polynomial

noncomputable theory
def equiv_alg : (K →ₐ[ℚ] ℂ) ≃ (K →+* ℂ) :=
{ to_fun := coe,
  inv_fun := λ f : K →+* ℂ, alg_hom.mk' f (λ (c : ℚ) x,
    add_monoid_hom.map_rat_module_smul f.to_add_monoid_hom _ _),
  left_inv := begin
    intro f,
    ext x : 1,
    simp,
  end,
  right_inv :=
  begin
    intro f,
    ext x : 1,
    erw alg_hom.coe_mk' f
      (λ (c : ℚ) x, add_monoid_hom.map_rat_module_smul f.to_add_monoid_hom _ _),
  end}
-- There are finitely many complex embeddings of a number field
instance : fintype (K →+* ℂ) := fintype.of_equiv (K →ₐ[ℚ] ℂ) equiv_alg
lemma card_embeddings : fintype.card (K →+* ℂ) = finrank ℚ K :=
by rw [fintype.of_equiv_card equiv_alg, alg_hom.card]

-- something like this will be useful
-- note this wouldn't be true as multisets
-- probably will make use of `alg_hom_adjoin_integral_equiv`
lemma roots_equal_embeddings : ((map (algebra_map ℚ ℂ) (minpoly ℚ x)).roots.to_finset : finset ℂ) =
  (range (λ φ : K →+* ℂ, φ x)).to_finset := sorry

lemma nat_degree_le_finrank {K : Type*} [field K] [number_field K] {x : K} (hx : is_integral ℤ x) :
  (minpoly ℤ x).nat_degree ≤ finrank ℚ K :=
begin
  rw (_ : (minpoly ℤ x).nat_degree = (minpoly ℚ x).nat_degree),
  rw [← intermediate_field.adjoin.finrank (is_separable.is_integral ℚ x),
    ← intermediate_field.finrank_eq_finrank_subalgebra],
  convert submodule.finrank_le (ℚ⟮x⟯.to_subalgebra.to_submodule : submodule _ _),
  have : minpoly ℚ x = (minpoly ℤ x).map (algebra_map ℤ ℚ),
  from minpoly.gcd_domain_eq_field_fractions ℚ hx,
  rw [this, nat_degree_map' _],
  exact is_fraction_ring.injective ℤ ℚ,
end

lemma minpoly_coeff_le_of_all_abs_eq_one (hx : x ∈ {x : K | ∀ (φ : K →+* ℂ), abs (φ x) = 1})
  (hxi : is_integral ℤ x) (i : ℕ) : |(minpoly ℤ x).coeff i| ≤ (finrank ℚ K).choose i :=
begin
  by_cases hi : i ≤ (finset.univ : finset (K →+* ℂ)).card,
  { have h_mins : minpoly ℚ x = (minpoly ℤ x).map (algebra_map ℤ ℚ),
    from minpoly.gcd_domain_eq_field_fractions ℚ hxi,
    suffices : abs ((minpoly ℚ x).coeff i : ℂ) ≤ (finrank ℚ K).choose i,
    { suffices : (|(minpoly ℤ x).coeff i| : ℝ) ≤ ↑((finrank ℚ K).choose i),
      { exact_mod_cast this, },
      convert this,
      simp only [h_mins, coeff_map, ring_hom.eq_int_cast, rat.cast_coe_int],
      norm_cast, },
    rw (by simp [coeff_map, ring_hom.eq_rat_cast] :
      ((minpoly ℚ x).coeff i : ℂ) = ((minpoly ℚ x).map (algebra_map ℚ ℂ)).coeff i),
    rw (_ : map (algebra_map ℚ ℂ) (minpoly ℚ x) = ∏ φ : K →+* ℂ, (X - C (φ x))),
    { rw prod_X_sub_C_coeff,
      swap, exact hi,
      simp [is_absolute_value.abv_pow complex.abs],
      calc _ ≤ _ : is_absolute_value.abv_sum _ _ _
        ... ≤ _ : _,
      conv in (complex.abs _)
      { rw [is_absolute_value.abv_prod complex.abs],
        congr,
        skip,
        funext,
        rw hx i, },
      simp only [finset.prod_const_one, finset.sum_const, finset.card_powerset_len,
        nat.cast_le, nat.smul_one_eq_coe],
      rw nat.choose_symm hi,
      apply le_of_eq,
      congr,
      rw ← card_embeddings,
      exact finset.card_univ, },
    { -- this goal isn't true as stated right now, the rhs could be a power of the lhs
      have : splits (algebra_map ℚ ℂ) (minpoly ℚ x),
      from is_alg_closed.splits_codomain (minpoly ℚ x),
      rw eq_prod_roots_of_splits this,
      simp only [monic.def.mp (minpoly.monic (is_separable.is_integral ℚ x)),
        one_mul, ring_hom.map_one],
      sorry, }, },
  { push_neg at hi,
    rw finset.card_univ at hi,
    rw card_embeddings at hi,
    rw nat.choose_eq_zero_of_lt hi,
    rw coeff_eq_zero_of_nat_degree_lt,
    simp [hi, le_refl, int.coe_nat_zero],
    calc _ ≤ finrank ℚ K : nat_degree_le_finrank hxi
       ... < _           : by exact_mod_cast hi, },
end

lemma finite_all_abs_eq_one : finite {x : K | is_integral ℤ x ∧ ∀ φ : K →+* ℂ, abs (φ x) = 1} :=
begin
  suffices :
    finite (⋃ (f : polynomial ℤ)
      (hf : f.nat_degree ≤ finrank ℚ K ∧ ∀ i, |f.coeff i| ≤ (finrank ℚ K).choose i),
      ((f.map (algebra_map ℤ K)).roots.to_finset : set K)),
  { refine this.subset _,
    intros x hx,
    rw mem_Union,
    use minpoly ℤ x,
    simp only [exists_prop, mem_Union, multiset.mem_to_finset, finset.mem_coe],
    refine ⟨⟨_, _⟩, _⟩,
    { exact nat_degree_le_finrank hx.1, },
    { exact minpoly_coeff_le_of_all_abs_eq_one x hx.2 hx.1, },
    rw [polynomial.mem_roots_map_of_injective, polynomial.eval₂_eq_eval_map, ← coe_aeval_eq_eval,
        aeval_map, minpoly.aeval],
    exact int.cast_injective,
    refine minpoly.ne_zero hx.1, },
  refine finite.bUnion _ _,
  { have : inj_on (λ g : polynomial ℤ, λ d : fin (finrank ℚ K + 1), g.coeff d)
      { f | f.nat_degree ≤ finrank ℚ K
            ∧ ∀ (i : ℕ), |f.coeff i| ≤ (finrank ℚ K).choose i },
    { intros x hx y hy he,
      ext,
      by_cases n < finrank ℚ K + 1,
      { simpa using congr_fun he ⟨n, h⟩, },
      rw [coeff_eq_zero_of_nat_degree_lt, coeff_eq_zero_of_nat_degree_lt],
      { rcases hy with ⟨hy_left, hy_right⟩,
        linarith, },
      { rcases hx with ⟨hx_left, hx_right⟩,
        linarith, }, },
    { refine finite_of_finite_image this _,
      have : (set.pi univ (λ d : fin (finrank ℚ K + 1), Icc (-(finrank ℚ K).choose d : ℤ)
              ((finrank ℚ K).choose d))).finite,
      { refine finite.pi _,
        intro d,
        exact finite_Icc _ _, },
      refine finite.subset this _,
      simp only [pi_univ_Icc, image_subset_iff],
      intros f hf,
      simp only [pi_univ_Icc, mem_preimage, mem_Icc, pi.le_def] at *,
      rw ← forall_and_distrib,
      intro x,
      rw mem_def at hf,
      rcases hf with ⟨hf_left, hf_right⟩,
      specialize hf_right x,
      rw abs_le at hf_right,
      suffices : f.nat_degree.choose x ≤ (finrank ℚ K).choose x,
      { split; linarith, },
      apply nat.choose_mono _ hf_left, }, },
  { intros p hp,
    -- few possibilites here
    exact polynomial.root_set_finite p K, },
end

-- TODO we don't really need K to be a number field here, more general field extensions are fine
-- as long as we keep the condition that x is integral over ℤ
variables (hx : ∀ φ : K →+* ℂ, abs (φ x) = 1) (hxi : is_integral ℤ x)
include hx hxi
lemma mem_roots_of_unity_of_abs_eq_one : ∃ (n : ℕ) (hn : 0 < n), x ^ n = 1 :=
begin
  have : ∃ (a : ℕ) (ha : a ∈ univ) (b : ℕ) (hb : b ∈ univ), a ≠ b ∧ x ^ a = x ^ b :=
    @infinite.exists_ne_map_eq_of_maps_to _ _ _ _
      ((^) x : ℕ → K) infinite_univ _ (finite_all_abs_eq_one),
  { have : ∃ (a b : ℕ), a ≠ b ∧ x ^ a = x ^ b,
    { simpa, },
    obtain ⟨a, b, habne, h⟩ := this,
    replace habne := habne.lt_or_lt,
    wlog : a < b := habne using [a b],
    use b - a,
    split,
    exact tsub_pos_of_lt habne,
    have hxne : x ≠ 0,
    { contrapose! hx,
      simp [hx],
      use is_alg_closed.lift ℚ K ℂ (number_field.is_algebraic K), },
    rw [pow_sub₀ _ hxne habne.le, h, mul_inv_cancel (pow_ne_zero b hxne)], },
  { simp only [set.maps_univ_to],
    intro a,
    split,
    exact is_integral.pow hxi a,
    intro φ,
    specialize hx φ,
    simp [hx, is_absolute_value.abv_pow complex.abs], },
end
end backwards

-- #lint only generalisation_linter
