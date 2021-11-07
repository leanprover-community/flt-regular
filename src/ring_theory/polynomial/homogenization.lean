/-
Copyright (c) 2021 Alex J. Best. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best
-/

import ring_theory.polynomial.homogeneous

/-!
# Homogenization

## Main definitions

* `mv_polynomial.homogenization`

## Main statements

* foo_bar_unique

## Notation



## Implementation details

* We homogenize polynomials over a given ground set of variables, rather than adjoining an extra
  variable to give the user more choice in the type of the polynomials involved.

## References

* [F. Bar, *Quuxes*][]

## Tags


-/

variables {R ι : Type*} [comm_semiring R]
open mv_polynomial

open_locale big_operators
noncomputable theory
namespace mv_polynomial

section finsupp

-- TODO something like this should be true but unsure what
lemma finsupp.sum_update_add {α β : Type*} [has_zero α] [add_comm_monoid β] (f : ι →₀ α) (i : ι)
  (a : α) (g : ι → α → β) : (f.update i a).sum g + g i (f i) = f.sum g + g i a :=
begin
  -- rw finsupp.update,
  -- split_ifs,
  -- rw finsupp.sum,
  -- simp,
  -- rw finsupp.sum,
  -- rw add_comm,
  -- rw ← finset.sum_insert _,
  -- -- erw function.apply_update,
  sorry,
  -- rw finsupp.sum,
  -- simp,
  -- rw finset.sum_insert,
  -- simp,
  -- rw finsupp.sum,
end

end finsupp

/-- The homogenization of a multivariate polynomial at a single variable. -/
def homogenization (i : ι) (p : mv_polynomial ι R) :
  mv_polynomial ι R :=
-- ∑ j in p.support, monomial (j + finsupp.single i (p.total_degree - (j i))) (p.coeff j)
finsupp.map_domain (λ j, finsupp.update j i (p.total_degree - j.sum (λ _ m, m))) p
-- begin
--   intros x hx y hy hxy,
--   simp at *,
--   ext,
--   have : x.update i (p.total_degree - x.sum (λ (_x : ι) (m : ℕ), m)) a =
--     y.update i (p.total_degree - y.sum (λ (_x : ι) (m : ℕ), m)) a,
--   from congr_fun (congr_arg coe_fn hxy) a,
--   simp at this,
--   by_cases hai : a = i,
--   { subst hai,
--     simp at this,
--     have hx : x.sum (λ (_x : ι) (m : ℕ), m) ≤ p.total_degree,
--     sorry,
--     have hy : y.sum (λ (_x : ι) (m : ℕ), m) ≤ p.total_degree,
--     sorry,
--     have : x.sum (λ (_x : ι) (m : ℕ), m) = y.sum (λ (_x : ι) (m : ℕ), m),
--     sorry,
--     apply_fun (λ K, K.sum (λ _ m, m)) at hxy,
--     sorry,
--     --rw finsupp.sum_update,
--     -- simp at hxy,
--     --apply sub_eq_sub,
--     },
--   { simpa [hai], },
-- end

-- lemma total_degree_add {p q : mv_polynomial ι R} (h : p.total_degree = p.total_degree) :=


@[simp] lemma support_eq_empty {f : mv_polynomial ι R} : f.support = ∅ ↔ f = 0 :=
finsupp.support_eq_empty

@[simp] lemma finsupp.support_map_domain {α β M : Type*} [add_comm_monoid M] (f : α ↪ β)
  (v : α →₀ M) : (finsupp.map_domain f v).support ⊆ v.support.map f :=
begin
  rw finsupp.map_domain,
  apply finset.subset.trans finsupp.support_sum,
  -- convert finset.bUnion_mono _,
  -- rw finsupp.support_single_subset,
  -- simp,
  sorry,
  sorry,
end
lemma support_homogenization (i : ι) (p : mv_polynomial ι R)
  (h : ∀ j ∈ p.support, (j : ι → ℕ) i = 0) : (p.homogenization i).support = p.support.map sorry :=
begin
  rw homogenization,
  sorry,
  -- rw finsupp.support_map_domain,
end

lemma total_degree_homogenization (i : ι) (p : mv_polynomial ι R)
  (h : ∀ j ∈ p.support, (j : ι → ℕ) i = 0) :
  (p.homogenization i).total_degree = p.total_degree :=
begin
  sorry
end

lemma is_homogenous_homogenization (i : ι) (p : mv_polynomial ι R)
  (h : ∀ j ∈ p.support, (j : ι → ℕ) i = 0) :
  (p.homogenization i).is_homogeneous p.total_degree :=
begin
  sorry
end

lemma homogenization_monomial (x : R) (i : ι →₀ ℕ) (j : ι) (h : (i : ι → ℕ) j = 0) :
  (monomial i x).homogenization j = monomial i x := sorry

lemma homogenization_mul (i : ι) (p q : mv_polynomial ι R)
  (hp : ∀ j ∈ p.support, (j : ι → ℕ) i = 0) (hq : ∀ j ∈ q.support, (j : ι → ℕ) i = 0) :
  (p * q).homogenization i = p.homogenization i * q.homogenization i := sorry

-- TODO this probably still isn't true, must assume (p + q) total degree also equal?
lemma homogenization_add (i : ι) (p q : mv_polynomial ι R) (h : p.total_degree = q.total_degree)
  (hp : ∀ j ∈ p.support, (j : ι → ℕ) i = 0) (hq : ∀ j ∈ q.support, (j : ι → ℕ) i = 0) :
  (p + q).homogenization i = p.homogenization i + q.homogenization i :=
begin
  simp [homogenization],
  sorry,
end

end mv_polynomial
