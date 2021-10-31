/-
Copyright (c) 2021 Alex J. Best. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best
-/
import ring_theory.roots_of_unity
import number_theory.number_field
import data.complex.basic
import data.real.nnreal
import analysis.special_functions.pow
import algebra.abs
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

section backwards

open set finite_dimensional complex
open_locale classical
open_locale big_operators

variables {K : Type*} [field K] [number_field K] {n : ℕ} (x : K)
open polynomial

-- There are finitely many complex embeddings of a number field
instance : fintype (K →+* ℂ) := sorry

open polynomial.gal
local attribute [instance] splits_ℚ_ℂ

-- something like this will be useful
lemma roots_equal_embeddings : ((map (algebra_map ℚ ℂ) (minpoly ℚ x)).roots.to_finset : finset ℂ) =
  (range (λ φ : K →+* ℂ, φ x)).to_finset := sorry

lemma minpoly_coeff_le_of_all_abs_eq_one (hx : x ∈ {x : K | ∀ (φ : K →+* ℂ), abs (φ x) = 1})
  (hxi : is_integral ℤ x) (i : ℕ) : |(minpoly ℤ x).coeff i| ≤ (minpoly ℤ x).nat_degree.choose i :=
begin
  have : minpoly ℚ x = (minpoly ℤ x).map (algebra_map ℤ ℚ),
  from minpoly.gcd_domain_eq_field_fractions ℚ hxi,
  suffices : abs (((minpoly ℚ x).coeff i) : ℂ) ≤ (minpoly ℚ x).nat_degree.choose i,
  { sorry, },
  rw (by simp [coeff_map, ring_hom.eq_rat_cast] :
    ((minpoly ℚ x).coeff i : ℂ) = ((minpoly ℚ x).map (algebra_map ℚ ℂ)).coeff i),
  rw (_ : map (algebra_map ℚ ℂ) (minpoly ℚ x) = ∏ φ : K →+* ℂ, (X - C (φ x))),
  { sorry,
    --rw prod_X_sub_C_coeff, -- maybe need a lemma like this, should be provable by induction
    -- likely one version for fintypes and another for finsets
    },
  { have : splits (algebra_map ℚ ℂ) (minpoly ℚ x), from is_alg_closed.splits_codomain (minpoly ℚ x),
    rw eq_prod_roots_of_splits this,
    simp [monic.def.mp (minpoly.monic (is_separable.is_integral ℚ x))],
    sorry, }
end

lemma finite_all_abs_eq_one : finite {x : K | is_integral ℤ x ∧ ∀ φ : K →+* ℂ, abs (φ x) = 1} :=
begin
  suffices :
    finite (⋃ (f : polynomial ℤ)
      (hf : f.nat_degree ≤ finrank ℚ K ∧ ∀ i, |f.coeff i| ≤ f.nat_degree.choose i),
      ((f.map (algebra_map ℤ K)).roots.to_finset : set K)),
  { refine this.subset _,
    intros x hx,
    rw mem_Union,
    use (minpoly ℤ x),
    simp only [exists_prop, mem_Union, multiset.mem_to_finset, finset.mem_coe],
    refine ⟨⟨_, _⟩, _⟩,
    { rw (_ : (minpoly ℤ x).nat_degree = (minpoly ℚ x).nat_degree),
      rw [← intermediate_field.adjoin.finrank (is_separable.is_integral ℚ x),
        ← intermediate_field.finrank_eq_finrank_subalgebra],
      convert submodule.finrank_le (ℚ⟮x⟯.to_subalgebra.to_submodule : submodule _ _),
      have : minpoly ℚ x = (minpoly ℤ x).map (algebra_map ℤ ℚ),
      from minpoly.gcd_domain_eq_field_fractions ℚ hx.1,
      rw [this, nat_degree_map' _],
      exact is_fraction_ring.injective ℤ ℚ, },
    { exact minpoly_coeff_le_of_all_abs_eq_one x hx.2 hx.1, },
    rw [polynomial.mem_roots_map_of_injective, polynomial.eval₂_eq_eval_map, ← coe_aeval_eq_eval,
        aeval_map, minpoly.aeval],
    exact int.cast_injective,
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
