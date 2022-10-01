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
import ready_for_mathlib.number_field_embeddings
import order.succ_pred.basic
import data.nat.succ_pred
import data.nat.choose
import algebra.char_p.algebra
import tactic.may_assume

open_locale big_operators

open_locale nnreal
-- probably this isn't needed but is another annoying example of 0 < n vs n ≠ 0 causing library
-- search to fail on "obvious" lemmas
lemma eq_one_of_pow_eq_one {n : ℕ} (hn : 0 < n) {t : ℝ≥0} (h_pow : t ^ n = 1) : t = 1 :=
(@pow_eq_one_iff _ _ _ nnreal.covariant_mul _ _ hn.ne').mp h_pow


section forward

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
    simp only [hx, map_one],
    rw monoid_hom.map_pow,
    rw is_absolute_value.abv_pow complex.abs, },
  set t := abs (φ x),
  have : 0 ≤ t := map_nonneg _ _,
  clear_value t,
  lift t to ℝ≥0 using this,
  norm_cast at *,
  rwa (@pow_eq_one_iff _ _ _ nnreal.covariant_mul _ _ hn.ne') at h_pow,
end

end forward

section polynomial

variables {R : Type*} [comm_semiring R]
open polynomial

/--
The degree of a product of polynomials is at most the sum of the degrees,
where the degree of the zero polynomial is ⊥.
-/
lemma degree_multiset_prod_le (t : multiset (polynomial R)) :
  t.prod.degree ≤ (t.map polynomial.degree).sum :=
begin
  nontriviality R,
  refine multiset.induction_on t _ (λ a t ht, _), { simp },
  { simp only [multiset.prod_cons, multiset.map_cons, multiset.sum_cons],
    exact le_trans (degree_mul_le _ _) (add_le_add_left ht _), }
end

@[simp]
lemma degree_eq_bot [subsingleton R] (p : polynomial R) : p.degree = ⊥ :=
by simp [subsingleton.elim p 0] -- should subsingleton.elim r 0 be a simp lemma in rings?

@[simp]
lemma nat_degree_eq_bot [subsingleton R] (p : polynomial R) : p.nat_degree = 0 :=
by simp [subsingleton.elim p 0] -- should subsingleton.elim r 0 be a simp lemma in rings?

lemma multiset_prod_X_add_C_degree' (s : multiset R) :
  degree (multiset.map (λ (x : R), X + C x) s).prod ≤ s.card :=
begin
  nontriviality R,
  have := polynomial.degree_multiset_prod_le (multiset.map (λ (x : R), X + C x) s),
  simpa,
end

lemma multiset_prod_X_add_C_degree (s : multiset R) :
  degree (multiset.map (λ (x : R), X + C x) s).prod < s.card + 1 :=
begin
  have := multiset_prod_X_add_C_degree' s,
  rwa ← order.lt_succ_iff at this
end


-- TODO turns out this is already in ring_theory.polynomial.vieta in one form
-- TODO lol I hope this monstrosity is golfable
-- unfortunately this lemma isn't true without the hi hypothesis, due to nat subtraction weirdness
lemma multiset_prod_X_add_C_coeff (t : multiset R) {i : ℕ} (hi : i ≤ t.card) :
  (t.map (λ x, (X + C x))).prod.coeff i =
  ((t.powerset_len (t.card - i)).map multiset.prod).sum :=
begin
  revert t i,
  apply' multiset.induction,
  { intros i hi,
    simp only [multiset.card_zero, le_zero_iff] at hi,
    simp only [hi, multiset.card_zero, mul_one, multiset.map_singleton, coeff_one_zero,
      multiset.sum_singleton, multiset.prod_zero, multiset.map_zero,
      multiset.powerset_len_zero_left, pow_zero], },
  intros a s h i his,
  simp only [add_mul, multiset.map_cons, multiset.prod_cons, coeff_C_mul, coeff_add,
    multiset.card_cons],
  simp only [multiset.card_cons] at his,
  by_cases his' : i = s.card + 1,
  { simp only [his', multiset.map_singleton, multiset.sum_singleton, multiset.prod_zero,
      tsub_self, multiset.powerset_len_zero_left, polynomial.coeff_X_pow_mul],

    have : (multiset.map (λ (x : R), X + C x) s).prod.coeff (s.card + 1) = 0,
    from coeff_eq_zero_of_degree_lt (multiset_prod_X_add_C_degree _),
    simp [this, sub_zero, mul_zero, h (le_refl _), mul_one, multiset.map_singleton,
      multiset.sum_singleton, multiset.prod_zero, tsub_self, multiset.powerset_len_zero_left,
      pow_zero, h (le_refl _), multiset.map_singleton, multiset.sum_singleton, multiset.prod_zero,
      tsub_self, multiset.powerset_len_zero_left, add_right_eq_self], },
  have : i ≤ s.card := nat.lt_succ_iff.mp (lt_of_le_of_ne his his'),
  rw [nat.succ_sub this, multiset.powerset_len_cons],
  simp only [h this, multiset.prod_cons, function.comp_app, multiset.map_map, multiset.map_add,
    multiset.sum_add],
  cases i,
  { simp only [tsub_zero, multiset.prod_cons, mul_coeff_zero, nat.nat_zero_eq_zero, zero_sub,
      zero_mul, function.comp_app, coeff_X_zero, tsub_zero, multiset.prod_cons,
      multiset.powerset_len_card_add, mul_coeff_zero, nat.nat_zero_eq_zero,
    zero_mul, eq_self_iff_true, function.comp_app, coeff_X_zero, zero_add, nat.lt_one_iff,
    multiset.map_zero, multiset.sum_zero],
    specialize h this,
    simp [tsub_zero, nat.nat_zero_eq_zero] at h,
    have := (add_monoid_hom.mul_left a).map_multiset_sum,
    simp only [add_monoid_hom.coe_mul_left] at this,
    simp [this], },
  rw [coeff_X_mul],
  congr,
  { have hii : i ≤ multiset.card s := nat.le_of_succ_le this,
    have : multiset.card s - i = multiset.card s - i.succ + 1, -- I miss omega :'(
    { zify [his, hii, this],
      simp only [int.coe_nat_succ],
      abel, },
    rw [h hii, this], },
  { -- TODO this rearranging is repeat of above, is it golfable?
    have := (add_monoid_hom.mul_left a).map_multiset_sum,
    simp only [add_monoid_hom.coe_mul_left] at this,
    simp [this], },
end
end polynomial
section polynomial
open polynomial
variables {R : Type*} [comm_ring R]

-- TODO lol I hope this monstrosity is golfable
lemma multiset_prod_X_sub_C_coeff (t : multiset R) {i : ℕ} (hi : i ≤ t.card) :
  (t.map (λ x, (X - C x))).prod.coeff i =
  (-1) ^ (t.card - i) * ((t.powerset_len (t.card - i)).map multiset.prod).sum :=
begin
  simp_rw [sub_eq_add_neg, ← C_neg],
  rw (by simp : t.map (λ x, X + C (-x)) = (t.map (((*) (-1 : R)) : R → R)).map (λ x, X + C x)),
  rw multiset_prod_X_add_C_coeff,
  simp only [multiset.card_map, one_mul, function.comp_app, multiset.map_map,
    multiset.powerset_len_map],
  have := (add_monoid_hom.mul_left ((-1 : R) ^ (t.card - i))).map_multiset_sum,
  simp only [add_monoid_hom.coe_mul_left] at this,
  simp [this],
  congr' 1, -- TODO its weird that congr doesn't do what we want here without hand-holding
  { apply multiset.map_congr,
    { refl },
    { intros s hs,
      simp at hs,
      rw ← hs.2 } },
  { simp [hi] }
end

-- TODO remove the hs hypothesis, lemma is true without
lemma prod_X_add_C_coeff {ι : Type*} (s : finset ι)
  (f : ι → R) {i : ℕ} (hs : i ≤ s.card) :
  (∏ i in s, (X + C (f i))).coeff i =
  ∑ i in s.powerset_len (s.card - i), i.prod f :=
begin
  have := multiset_prod_X_add_C_coeff (s.1.map f) (by simpa using hs),
  simp only [multiset.card_map, function.comp_app, multiset.map_map,
    multiset.powerset_len_map] at this,
  convert this,
  rw finset.sum_eq_multiset_sum,
  refine congr_arg multiset.sum _,
  rw ← finset.map_val_val_powerset_len,
  rw multiset.map_map,
  congr,
end

lemma prod_X_sub_C_coeff {ι : Type*} (s : finset ι)
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
  rw ← finset.map_val_val_powerset_len,
  rw multiset.map_map,
  congr,
end

end polynomial

section backwards

open set finite_dimensional complex
open_locale classical
open_locale big_operators

variables {K : Type*} [field K] [number_field K] {n : ℕ} (x : K)
open polynomial

noncomputable theory

lemma nat_degree_le_finrank {K : Type*} [field K] [number_field K] {x : K} (hx : is_integral ℤ x) :
  (minpoly ℤ x).nat_degree ≤ finrank ℚ K :=
begin
  rw (_ : (minpoly ℤ x).nat_degree = (minpoly ℚ x).nat_degree),
  rw [← intermediate_field.adjoin.finrank (is_separable.is_integral ℚ x),
    ← intermediate_field.finrank_eq_finrank_subalgebra],
  convert submodule.finrank_le (ℚ⟮x⟯.to_subalgebra.to_submodule : submodule _ _),
  have : minpoly ℚ x = (minpoly ℤ x).map (algebra_map ℤ ℚ),
  from minpoly.gcd_domain_eq_field_fractions' ℚ hx,
  rw [this, nat_degree_map_eq_of_injective _],
  exact is_fraction_ring.injective ℤ ℚ,
end

lemma minpoly_coeff_le_of_all_abs_eq_one (hx : x ∈ {x : K | ∀ (φ : K →+* ℂ), abs (φ x) = 1})
  (hxi : is_integral ℤ x) (i : ℕ) :
  |(minpoly ℤ x).coeff i| ≤ ((minpoly ℤ x).nat_degree.choose i) :=
begin
  by_cases hi : i ≤ (minpoly ℤ x).nat_degree,
  { have h_mins : minpoly ℚ x = (map (algebra_map ℤ ℚ) (minpoly ℤ x)),
    from minpoly.gcd_domain_eq_field_fractions' ℚ hxi,
    have h_degree : (minpoly ℚ x).nat_degree = (minpoly ℤ x).nat_degree,
    { rw ( _ : (minpoly ℤ x).nat_degree = (map (algebra_map ℤ ℚ) (minpoly ℤ x)).nat_degree),
      rwa h_mins,
      have : function.injective (algebra_map ℤ ℚ), { exact (algebra_map ℤ ℚ).injective_int, },
      rw polynomial.nat_degree_map_eq_of_injective this, },
    suffices : abs ((minpoly ℚ x).coeff i : ℂ) ≤ (minpoly ℤ x).nat_degree.choose i,
    { suffices : (|(minpoly ℤ x).coeff i| : ℝ) ≤ ↑((minpoly ℤ x).nat_degree.choose i),
      { exact_mod_cast this, },
      convert this,
      simp only [h_mins, coeff_map, rat.cast_coe_int, eq_int_cast],
      norm_cast, },
    rw (by simp [coeff_map] :
      ((minpoly ℚ x).coeff i : ℂ) = ((minpoly ℚ x).map (algebra_map ℚ ℂ)).coeff i),
    have : splits (algebra_map ℚ ℂ) (minpoly ℚ x),
      from is_alg_closed.splits_codomain (minpoly ℚ x),
    have h_roots : multiset.card (map (algebra_map ℚ ℂ) (minpoly ℚ x)).roots =
      (minpoly ℚ x).nat_degree, { exact (polynomial.nat_degree_eq_card_roots this).symm, },
    rw eq_prod_roots_of_splits this,
    simp only [monic.def.mp (minpoly.monic (is_separable.is_integral ℚ x)),
        one_mul, ring_hom.map_one],
    rw multiset_prod_X_sub_C_coeff,
    swap, rwa [h_roots, h_degree],
    simp only [absolute_value.map_mul, complex.abs_pow, absolute_value.map_neg,
      absolute_value.map_one, one_pow, one_mul],
    let T := (multiset.powerset_len (multiset.card (map (algebra_map ℚ ℂ) (minpoly ℚ x)).roots - i)
        (map (algebra_map ℚ ℂ) (minpoly ℚ x)).roots),
    suffices : complex.abs (multiset.map multiset.prod T).sum  ≤
      (multiset.map (λ t, (multiset.map complex.abs t).prod) T).sum,
    { apply le_trans this,
      suffices : ∀ t ∈ T, (multiset.map complex.abs t).prod = 1,
      { rw multiset.map_congr (eq.refl T) this,
        have : multiset.card T = ((minpoly ℤ x).nat_degree.choose i),
        { rw ←nat.choose_symm,
          convert multiset.card_powerset_len (multiset.card (map (algebra_map ℚ ℂ)
          (minpoly ℚ x)).roots - i) (map (algebra_map ℚ ℂ) (minpoly ℚ x)).roots,
          { rw h_roots, exact h_degree.symm, },
          { rw h_roots, exact h_degree.symm, },
          exact hi, },
        simp only [this, multiset.map_const, multiset.sum_repeat, nat.smul_one_eq_coe], },
      { intros s hs,
        rw ( _ : (multiset.map complex.abs s) = multiset.repeat 1
          (multiset.card (map (algebra_map ℚ ℂ) (minpoly ℚ x)).roots - i)),
        simp only [multiset.prod_repeat, one_pow],
        suffices hz : ∀ z ∈ s, complex.abs z = 1,
        { rw ( _ : multiset.map complex.abs s = multiset.map (function.const ℂ 1) s),
          { rw multiset.mem_powerset_len at hs,
            simp only [hs.right, multiset.map_const], },
          exact multiset.map_congr (eq.refl s) hz },
        { intros z hz,
          suffices : z ∈ (minpoly ℚ x).root_set ℂ,
          { rw [← number_field.embeddings.range_eq_roots ℚ K ℂ x] at this,
            rcases set.mem_range.mp this with ⟨φ, hφ⟩,
            rw ←hφ,
            exact (set.mem_set_of.mp hx) φ },
          apply multiset.mem_to_finset.mpr,
          refine multiset.mem_of_le _ hz,
          exact (multiset.mem_powerset_len.mp hs).left, }}},
    suffices : complex.abs (multiset.map multiset.prod T).sum ≤
        (multiset.map complex.abs (multiset.map multiset.prod T)).sum,
    { apply le_trans this,
      apply le_of_eq,
      suffices :  ∀ t ∈ T, complex.abs (multiset.prod t) = (multiset.map complex.abs t).prod,
      { simp only [multiset.map_congr (eq.refl T) this, multiset.map_map], },
      intros t ht,
      exact (multiset.prod_hom t _).symm },
      refine multiset.le_sum_of_subadditive complex.abs _ _ (multiset.map multiset.prod T),
      simp,
      exact (λ a b, complex.abs.add_le a b) },
  { push_neg at hi,
    rw nat.choose_eq_zero_of_lt hi,
    rw coeff_eq_zero_of_nat_degree_lt,
    norm_cast,
    exact hi, },
end

lemma finite_all_abs_eq_one : {x : K | is_integral ℤ x ∧ ∀ φ : K →+* ℂ, abs (φ x) = 1}.finite :=
begin
  suffices :
    (⋃ (f : polynomial ℤ)
       (hf : f.nat_degree ≤ finrank ℚ K ∧ ∀ i, |f.coeff i| ≤ f.nat_degree.choose i),
       ((f.map (algebra_map ℤ K)).roots.to_finset : set K)).finite,
  { refine this.subset _,
    intros x hx,
    rw mem_Union,
    use minpoly ℤ x,
    simp only [exists_prop, mem_Union, multiset.mem_to_finset, finset.mem_coe],
    refine ⟨⟨_, _⟩, _⟩,
    { exact nat_degree_le_finrank hx.1, },
    { exact minpoly_coeff_le_of_all_abs_eq_one x hx.2 hx.1, },
    rw [mem_roots, is_root.def, ←polynomial.eval₂_eq_eval_map,
      ←aeval_def],
    exact minpoly.aeval ℤ x,
    suffices : (minpoly ℤ x) ≠ 0,
    { contrapose! this,
      simp only [polynomial.ext_iff, coeff_map, coeff_zero] at this ⊢,
      suffices inj : function.injective (algebra_map ℤ K),
      { exact λ n : ℕ, inj (by rw [(this n), (algebra_map ℤ K).map_zero]),},
      exact int.cast_injective, },
      refine minpoly.ne_zero hx.1, },
  refine finite.bUnion _ _,
  { have : inj_on (λ g : polynomial ℤ, λ d : fin (finrank ℚ K + 1), g.coeff d)
      { f | f.nat_degree ≤ finrank ℚ K
            ∧ ∀ (i : ℕ), |f.coeff i| ≤ f.nat_degree.choose i },
    { intros x hx y hy he,
      ext,
      by_cases n < finrank ℚ K + 1,
      { simpa using congr_fun he ⟨n, h⟩, },
      rw [coeff_eq_zero_of_nat_degree_lt, coeff_eq_zero_of_nat_degree_lt],
      { rcases hy with ⟨hy_left, hy_right⟩,
        linarith, },
      { rcases hx with ⟨hx_left, hx_right⟩,
        linarith, }, },
    { refine finite.of_finite_image _ this,
      have : (set.pi univ (λ d : fin (finrank ℚ K + 1), Icc (-(finrank ℚ K).choose d : ℤ)
              ((finrank ℚ K).choose d))).finite := finite.pi (λ d, finite_Icc _ _),
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
/-- Lemma 1.6 of Washington's Introduction to cyclotomic fields -/
lemma mem_roots_of_unity_of_abs_eq_one : ∃ (n : ℕ) (hn : 0 < n), x ^ n = 1 :=
begin
  obtain ⟨a, -, b, -, habne, h⟩ := @infinite.exists_ne_map_eq_of_maps_to _ _ _ _
      ((^) x : ℕ → K) infinite_univ _ (finite_all_abs_eq_one),
  { replace habne := habne.lt_or_lt,
    wlog : a < b := habne using [a b],
    refine ⟨b - a, tsub_pos_of_lt habne, _⟩,
    have hxne : x ≠ 0,
    { contrapose! hx,
      simp only [hx, ring_hom.map_zero, ne.def, not_false_iff, zero_ne_one, absolute_value.map_zero],
      use (is_alg_closed.lift (number_field.is_algebraic K)).to_ring_hom },
    rw [pow_sub₀ _ hxne habne.le, h, mul_inv_cancel (pow_ne_zero b hxne)] },
  { rw [set.maps_univ_to],
    exact λ a, ⟨hxi.pow a, λ φ, by simp [hx φ, is_absolute_value.abv_pow complex.abs]⟩ },
end
end backwards

-- #lint generalisation_linter
