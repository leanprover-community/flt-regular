/-
Copyright (c) 2021 Alex J. Best. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best
-/
import ring_theory.roots_of_unity
import number_theory.number_field
import data.complex.basic
import data.real.nnreal
import algebra.abs

open_locale nnreal
lemma eq_one_of_pow_eq_one {n : ℕ} (hn : 0 < n) {t : ℝ≥0} (h_pow : t ^ n = 1) : t = 1 :=
sorry

section forward
-- TODO maybe gen to is_R_or_C?
variables {K : Type*} [field K] [number_field K] {n : ℕ} (x : K) (hx : x ^ n = 1) (hn : 0 < n)
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
    -- rw pow_abs,
    sorry, },
  set t := abs (φ x),
  have : 0 ≤ t, from (φ x).abs_nonneg,
  clear_value t,
  lift t to ℝ≥0 using this,
  norm_cast at *,
  exact eq_one_of_pow_eq_one hn h_pow,
end

end forward

section backwards

open set finite_dimensional complex
open_locale classical

variables {K : Type*} [field K] [number_field K] {n : ℕ} (x : K)

lemma finite_all_abs_eq_one : finite {x : K | ∀ φ : K →+* ℂ, abs (φ x) = 1} :=
begin
  suffices :
    finite (⋃ (f : polynomial ℤ)
      (hf : f.nat_degree ≤ finrank ℚ K ∧ ∀ i, complex.abs (f.coeff i) < f.nat_degree.choose i),
      ((f.map (algebra_map ℤ K)).roots.to_finset : set K)),
  { refine this.subset _,
    intros x hx,
    rw mem_Union,
    use (minpoly ℤ x),
    simp,
    split,
    { sorry, },
    -- something like this should work as poly is monic and we are going from integral domain to a field anyways
    -- rw polynomial.mem_roots_map,
    suffices : (minpoly ℤ x).eval₂ (algebra_map ℤ K) x = 0,
    sorry,
    simp,
    rw polynomial.eval₂_eq_eval_map,
    -- suggest,
    sorry, },
  simp,
  refine finite.bUnion _ _,
  { sorry, },
  { intros p hp,
    -- few possibilites here
    exact polynomial.root_set_finite p K, },
end

variables (hx : ∀ φ : K →+* ℂ, abs (φ x) = 1)
include hx
lemma mem_roots_of_unity_of_abs_eq_one : ∃ (n : ℕ) (hn : 0 < n), x ^ n = 1 :=
begin
  sorry
end
end backwards
