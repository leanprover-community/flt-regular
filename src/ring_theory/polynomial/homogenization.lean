/-
Copyright (c) 2021 Alex J. Best. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best
-/

import data.set.finite
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

open_locale classical

-- TODO something like this should be true but unsure what
lemma finsupp.sum_update_add {α β : Type*} [has_zero α] [add_comm_monoid β] (f : ι →₀ α) (i : ι)
  (a : α) (g : ι → α → β) (hg : ∀ i, g i 0 = 0) : (f.update i a).sum g + g i (f i) = f.sum g + g i a :=
begin
  have hf : f.support ⊆ f.support ∪ {i} := f.support.subset_union_left {i},
  have hif : (f.update i a).support ⊆ f.support ∪ {i},
  { rw f.support_update i a, -- urgh why is this classical
    split_ifs,
    { exact finset.subset.trans (finset.erase_subset i f.support) hf, },
    { rw finset.union_comm, -- lemma?
      refl, }, }, -- TODO is there no lemma for this?
  rw finsupp.sum_of_support_subset f hf,
  rw finsupp.sum_of_support_subset _ hif,
  simp,
  -- conv in (g _ _)
  sorry; {-- { simp [function.apply_update _ f i a x], },
  rw finset.sum_update_of_mem,
  rw finset.sum_union,
  rw finset.sum_union,
  simp,
  rw add_assoc,
  rw add_comm (g i a),
  rw add_assoc,
  congr,


  sorry,},
  { intros i' hi',
    exact hg i', },
  { intros i' hi',
    exact hg i', },
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


-- TODO mathlib
@[simp] lemma mv_polynomial.support_eq_empty {f : mv_polynomial ι R} : f.support = ∅ ↔ f = 0 :=
finsupp.support_eq_empty

@[simp] lemma finsupp.support_map_domain {α β M : Type*} [add_comm_monoid M]
  (f : α ↪ β) (v : α →₀ M) : (finsupp.map_domain f v).support ⊆ v.support.map f :=
begin
  classical,
  rw finsupp.map_domain,
  refine finset.subset.trans finsupp.support_sum _,
  simp,
  intros x hx,
  apply finset.subset.trans finsupp.support_single_subset,
  simp [hx],
end

lemma degree_support_homogenization (i : ι) (p : mv_polynomial ι R)
  (h : ∀ j ∈ p.support, (j : ι → ℕ) i = 0) (exp : ι →₀ ℕ)
  (hexp : exp ∈ (p.homogenization i).support) : exp.sum (λ _ m, m) = p.total_degree :=
  sorry
-- lemma support_homogenization (i : ι) (p : mv_polynomial ι R)
--   (h : ∀ j ∈ p.support, (j : ι → ℕ) i = 0) : (p.homogenization i).support = p.support.image sorry :=
-- begin
--   rw homogenization,
--   apply finsupp.support_map_domain _ _ _,
-- end

@[simp]
lemma homogenization_zero (i : ι) : (0 : mv_polynomial ι R).homogenization i = 0 :=
by simp [homogenization]

@[simp]
lemma homogenization_C (i : ι) (c : R) : (C c : mv_polynomial ι R).homogenization i = C c :=
begin
  simp only [homogenization, total_degree_C, zero_tsub],
  convert finsupp.map_domain_single,
  rw single_eq_monomial,
  have : (0 : ι →₀ ℕ) i = 0,
  { simp only [finsupp.coe_zero, pi.zero_apply], },
  rw [← this, finsupp.update_self],
  simp,
end

lemma total_degree_monomial (s : ι →₀ ℕ) {r : R} (hr : r ≠ 0) :
  total_degree (monomial s r) = s.sum (λ _ e, e) :=
begin
  classical,
  simp [total_degree, support_monomial, if_neg, hr],
end

lemma homogenization_monomial (i : ι) (s : ι →₀ ℕ) (r : R) (hs : s i = 0) :
  (monomial s r : mv_polynomial ι R).homogenization i = monomial s r :=
begin
  by_cases hr : r = 0,
  { simp [hr], },
  erw [homogenization, finsupp.map_domain_single, single_eq_monomial, total_degree_monomial _ hr,
    tsub_self, ← hs, finsupp.update_self],
end

lemma total_degree_homogenization (i : ι) (p : mv_polynomial ι R)
  (h : ∀ j ∈ p.support, (j : ι → ℕ) i = 0) :
  (p.homogenization i).total_degree = p.total_degree :=
begin
  rw total_degree,
  have : (homogenization i p).support.nonempty,
  { simp [homogenization],
    sorry,
     },
  rw ← finset.sup'_eq_sup this,
  rw finset.nonempty.sup'_eq_cSup_image,
  suffices : (λ (s : ι →₀ ℕ), s.sum (λ (n : ι) (e : ℕ), e)) '' ↑((homogenization i p).support) =
    {p.total_degree},
  { simp [this], },
  refine set.eq_singleton_iff_unique_mem.mpr _,
  split,
  { simp, sorry, },
  { simp, sorry, },
end

lemma is_homogenous_homogenization (i : ι) (p : mv_polynomial ι R)
  (h : ∀ j ∈ p.support, (j : ι → ℕ) i = 0) :
  (p.homogenization i).is_homogeneous p.total_degree :=
begin
  sorry
end


lemma homogenization_mul (i : ι) (p q : mv_polynomial ι R)
  (hp : ∀ j ∈ p.support, (j : ι → ℕ) i = 0) (hq : ∀ j ∈ q.support, (j : ι → ℕ) i = 0) :
  (p * q).homogenization i = p.homogenization i * q.homogenization i :=
begin
  -- have := total_degree_mul,
  sorry,
end

-- TODO this probably still isn't true, must assume (p + q) total degree also equal?
lemma homogenization_add (i : ι) (p q : mv_polynomial ι R) (h : p.total_degree = q.total_degree)
  (hp : ∀ j ∈ p.support, (j : ι → ℕ) i = 0) (hq : ∀ j ∈ q.support, (j : ι → ℕ) i = 0) :
  (p + q).homogenization i = p.homogenization i + q.homogenization i :=
begin
  simp [homogenization],
  sorry,
end

end mv_polynomial
