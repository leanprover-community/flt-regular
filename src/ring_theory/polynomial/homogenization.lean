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

-- TODO decide if we should make this fix things with X i in already, or have assumptions that X i
-- does not appear everywhere
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
@[simp] lemma support_eq_empty {f : mv_polynomial ι R} : f.support = ∅ ↔ f = 0 :=
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

-- TODO name this
lemma aux {i : ι} {p : mv_polynomial ι R} {x : ι →₀ ℕ} (hp : x ∈ p.support) (hx : x i = 0) :
  (x.update i (p.total_degree - x.sum (λ _ m, m))).sum (λ _ m, m) = p.total_degree :=
begin
  have := finsupp.sum_update_add x i (p.total_degree - x.sum (λ _ m, m)) (λ _ m, m) _,
  { rw [hx, add_zero] at this,
    rw [this, add_tsub_cancel_iff_le],
    exact finset.le_sup hp, },
  { simp, }
end

lemma is_homogeneous_homogenization [decidable_eq ι] (i : ι) (p : mv_polynomial ι R)
  (h : ∀ j ∈ p.support, (j : ι → ℕ) i = 0) :
  (p.homogenization i).is_homogeneous p.total_degree :=
begin
  rw homogenization,
  intros d hd,
  rw [finsupp.map_domain, finsupp.sum, coeff_sum] at hd,
  simp_rw [single_eq_monomial, coeff_monomial] at hd,
  contrapose! hd,
  have : ∀ (x : ι →₀ ℕ) (hx : x ∈ p.support),
    ¬ x.update i (p.total_degree - x.sum (λ (_x : ι) (m : ℕ), m)) = d,
  { intros x hx hh,
    apply hd,
    rw ← hh,
    change (x.update i (p.total_degree - x.sum (λ (_x : ι) (m : ℕ), m))).sum (λ _ m, m) = _,
    rw aux hx (h x hx), },
  conv in (ite _ _ _)
  { simp [if_neg (this x H)], },
  simp,
end

lemma homogenization_of_is_homogeneous (n : ℕ) (i : ι) (p : mv_polynomial ι R)
  (hp : p.is_homogeneous n) (hxi : ∀ (x : ι →₀ ℕ) (hx : x ∈ p.support), x i = 0) :
  p.homogenization i = p :=
begin
  by_cases hpn : p = 0,
  { simp [hpn], },
  rw homogenization,
  have := (hp.total_degree hpn).symm,
  subst this,
  rw is_homogeneous at hp,
  have : ∀ x (hx : x ∈ p.support),
    (λ (j : ι →₀ ℕ), j.update i (p.total_degree - j.sum (λ (_x : ι) (m : ℕ), m))) x = x,
  { intros x hx,
    simp only,
    convert finsupp.update_self _ _,
    rw ← hp (mem_support_iff.mp hx),
    change x.support.sum x - x.support.sum x = _,
    simp [hxi, hx], },
  rw finsupp.map_domain_congr this,
  -- simp,
  erw finsupp.map_domain_id,
  -- TODO there should be a simp lemma version of this for λ x, x so simp works
end

section finsupp
open finsupp

-- TODO want something like this but unsure what
lemma map_domain_apply {α β M : Type*} [add_comm_monoid M] (S : set α) {f : α → β} (x : α →₀ M)
  (hf : set.inj_on f (x.support)) (a : α) : finsupp.map_domain f x (f a) = x a :=
begin
  sorry,
  -- rw [finsupp.map_domain, finsupp.sum_apply, finsupp.sum, finset.sum_eq_single a,
  -- finsupp.single_eq_same],
  -- { assume b _ hba, exact finsupp.single_eq_of_ne (_) }, -- TODO set.inj_on.ne
  -- { assume h, rw [not_mem_support_iff.1 h, single_zero, zero_apply] }
end
lemma map_domain_injective' {α β M : Type*} [add_comm_monoid M] (S : set α) {f : α → β}
  (hf : set.inj_on f S) :
  set.inj_on (finsupp.map_domain f : (α →₀ M) → (β →₀ M)) {f | (f.support : set α) ⊆ S} :=
begin
  assume v₁ hv₁ v₂ hv₂ eq, ext a,
  have : finsupp.map_domain f v₁ (f a) = finsupp.map_domain f v₂ (f a), { rw eq },
  sorry,
  -- rwa [finsupp.map_domain_apply hf, finsupp.map_domain_apply hf] at this,
end
end finsupp

lemma homogenization_ne_zero_of_ne_zero (i : ι) (p : mv_polynomial ι R) (hp : p ≠ 0) :
  p.homogenization i ≠ 0 :=
begin
  rw homogenization,
  intro h,
  apply hp,
  refine finsupp.map_domain_injective _ h,
  -- TODO something like this but this isnt exactly true
  sorry,
end

-- TODO this can follow from previous
lemma total_degree_homogenization (i : ι) (p : mv_polynomial ι R)
  (h : ∀ j ∈ p.support, (j : ι → ℕ) i = 0) :
  (p.homogenization i).total_degree = p.total_degree :=
begin
  classical,
  by_cases hp : p = 0,
  { simp [hp], },
  apply is_homogeneous.total_degree, --(homogenization_ne_zero_of_ne_zero hp),
  apply is_homogeneous_homogenization _ _ h,
  sorry, -- TODO lemma
  -- library_search!,
  -- rw total_degree,
  -- have : (homogenization i p).support.nonempty,
  -- { simp [homogenization],
  --   sorry,
  --    },
  -- rw ← finset.sup'_eq_sup this,
  -- rw finset.nonempty.sup'_eq_cSup_image,
  -- suffices : (λ (s : ι →₀ ℕ), s.sum (λ (n : ι) (e : ℕ), e)) '' ↑((homogenization i p).support) =
  --   {p.total_degree},
  -- { simp [this], },
  -- refine set.eq_singleton_iff_unique_mem.mpr _,
  -- split,
  -- { simp, sorry, },
  -- { simp, sorry, },
end

section leading_terms
-- TODO is this the best def?
/-- The sum of the monomials of highest degree of a multivariate polynomial. -/
def leading_terms (p : mv_polynomial ι R) : mv_polynomial ι R :=
homogeneous_component p.total_degree p

lemma leading_terms_apply (p : mv_polynomial ι R) : p.leading_terms =
  ∑ d in p.support.filter (λ d, ∑ i in d.support, d i = p.total_degree), monomial d (coeff d p) :=
homogeneous_component_apply _ _
-- (p.support.filter (λ s : ι →₀ ℕ, s.sum (λ _ e, e) = p.total_degree)).sum $
--   λ s, monomial s (p.coeff s)

@[simp]
lemma leading_terms_zero : (0 : mv_polynomial ι R).leading_terms = 0 :=
by simp [leading_terms]

lemma finset.filter_eq_self_iff {α : Type*} (S : finset α) (h : α → Prop) [decidable_pred h] :
  S.filter h = S ↔ ∀ s ∈ S, h s :=
begin
  cases S,
  simp only [finset.filter, finset.mem_mk, multiset.filter_eq_self],
end

-- TODO for non-zero polys this is true that p.lead = p iff p.is_homogenous n for a fixed n
-- TODO generalize to p.homog comp = n
lemma leading_terms_eq_self_iff_is_homogeneous (p : mv_polynomial ι R) :
  p.leading_terms = p ↔ p.is_homogeneous p.total_degree :=
begin
  split; intro h,
  { rw is_homogeneous,
    contrapose! h,
    rcases h with ⟨h_w, h_h₁, h_h₂⟩,
    rw [leading_terms, ne.def, mv_polynomial.ext_iff],
    push_neg,
    use h_w,
    classical,
    change ¬ h_w.sum (λ (_x : ι) (e : ℕ), e) = p.total_degree at h_h₂,
    simp [coeff_sum, h_h₁, h_h₂, ne.symm h_h₁, coeff_homogeneous_component],
    convert h_h₂, },
  { rw [leading_terms_apply],
    rw (_ : p.support.filter (λ (s : ι →₀ ℕ), ∑ (i : ι) in s.support, s i = p.total_degree)
            = p.support),
    { rw support_sum_monomial_coeff p, },
    { rw finset.filter_eq_self_iff,
      intros s hs,
      rw [mem_support_iff] at hs,
      rw ← h hs, }, },
end

@[simp]
lemma leading_terms_C (r : R) : (C r : mv_polynomial ι R).leading_terms = C r :=
begin
  rw leading_terms_eq_self_iff_is_homogeneous,
  convert is_homogeneous_C _ _,
  simp,
end

@[simp]
lemma leading_terms_monomial (s : ι →₀ ℕ) (r : R) : (monomial s r).leading_terms = monomial s r :=
begin
  by_cases hr : r = 0,
  { simp [hr], },
  rw leading_terms_eq_self_iff_is_homogeneous,
  convert is_homogeneous_monomial _ _ _ _,
  simpa [total_degree_monomial _ hr]
end

section dangerous_instance
local attribute [instance] mv_polynomial.unique
@[simp]
lemma leading_terms_X (s : ι) : (X s : mv_polynomial ι R).leading_terms = X s :=
begin
  nontriviality R,
  rw leading_terms_eq_self_iff_is_homogeneous,
  convert is_homogeneous_X _ _,
  exact total_degree_X _,
end
end dangerous_instance

lemma is_homogeneous_leading_terms (p : mv_polynomial ι R) :
  p.leading_terms.is_homogeneous p.total_degree :=
homogeneous_component_is_homogeneous (total_degree p) p

lemma exists_coeff_ne_zero_total_degree {p : mv_polynomial ι R} (hp : p ≠ 0) :
  ∃ (v : ι →₀ ℕ), v.sum (λ _ e, e) = p.total_degree ∧ p.coeff v ≠ 0 :=
begin
  obtain ⟨b, hb₁, hb₂⟩ := p.support.exists_mem_eq_sup (finsupp.support_nonempty_iff.mpr hp)
    (λ (m : ι →₀ ℕ), m.to_multiset.card),
  use b,
  split,
  { rw ← total_degree_eq p at hb₂,
    rw hb₂,
    dsimp, -- TODO break this out as a lemma
    funext m,
    exact (finsupp.card_to_multiset _).symm, },
  { exact mem_support_iff.mp hb₁, },
end

@[simp] lemma support_zero : (0 : mv_polynomial ι R).support = ∅ := finsupp.support_zero

lemma support_add_eq [decidable_eq ι] {g₁ g₂ : mv_polynomial ι R}
  (h : disjoint g₁.support g₂.support) : (g₁ + g₂).support = g₁.support ∪ g₂.support :=
finsupp.support_add_eq h

lemma add_ne_zero_of_ne_zero_of_support_disjoint [decidable_eq ι] (p q : mv_polynomial ι R)
  (hp : p ≠ 0) (h : disjoint p.support q.support) : p + q ≠ 0 :=
begin
  contrapose! hp,
  have := congr_arg support hp,
  rw [support_zero, support_add_eq h, finset.union_eq_empty_iff, -- TODO should this be simp?
    mv_polynomial.support_eq_empty] at this,
  exact this.left,
end

@[simp] lemma monomial_eq_zero (a : ι →₀ ℕ) (b : R) : monomial a b = 0 ↔ b = 0 :=
finsupp.single_eq_zero

lemma support_sum_monomial_subset (S : finset (ι →₀ ℕ)) (f : (ι →₀ ℕ) → R) :
  support (∑ v in S, monomial v (f v)) ⊆ S :=
begin
  classical,
  induction S using finset.induction with s S hs hsi,
  { simp, },
  { rw finset.sum_insert hs,
    apply finset.subset.trans support_add,
    apply finset.union_subset,
    { apply finset.subset.trans support_monomial_subset (finset.subset_union_left _ S), },
    { apply finset.subset.trans hsi (finset.subset_insert _ _), }, },
end

-- TODO probably other versions of this lemma for mathlib
lemma ite_subset_union {α : Type*} [decidable_eq α] (s s' : finset α) (P : Prop) [decidable P] :
  ite P s s' ⊆ s ∪ s' :=
begin
  split_ifs,
  exact finset.subset_union_left s s',
  exact finset.subset_union_right s s',
end

-- TODO probably there is a better proof?
lemma sum_monomial_ne_zero_of_exists_mem_ne_zero [decidable_eq ι] [decidable_eq R]
  (S : finset (ι →₀ ℕ)) (f : (ι →₀ ℕ) → R) (h : ∃ (s) (hs : s ∈ S), f s ≠ 0) :
  ∑ (s : ι →₀ ℕ) in S, monomial s (f s) ≠ 0 :=
begin
  induction S using finset.induction with s S hs hsi,
  { simpa using h, },
  rw finset.sum_insert hs,
  simp only [exists_prop, finset.mem_insert] at h,
  rcases h with ⟨h, rfl | h_h_left, h_h_right⟩,
  { apply add_ne_zero_of_ne_zero_of_support_disjoint,
    { simpa, },
    { simp only [support_monomial, h_h_right, not_not, mem_support_iff, if_false,
        finset.disjoint_singleton_left],
      rw coeff_sum,
      simp_rw [coeff_monomial],
      conv in (ite _ _ _)
      { rw if_neg (ne_of_mem_of_not_mem H hs : ¬ x = h), }, -- using classical makes this line fail
      simp, }, },
  { rw add_comm,
    apply add_ne_zero_of_ne_zero_of_support_disjoint,
    { apply hsi ⟨h, h_h_left, h_h_right⟩, },
    { simp only [support_monomial],
      apply finset.disjoint_of_subset_right,
      exact ite_subset_union _ _ _,
      simp only [finset.disjoint_singleton_right, finset.empty_union, not_not, mem_support_iff],
      rw coeff_sum,
      simp_rw [coeff_monomial],
      conv in (ite _ _ _)
      { rw if_neg (ne_of_mem_of_not_mem H hs : ¬ x = s), }, -- using classical makes this line fail
      simp, }, },
end

lemma leading_terms_ne_zero {p : mv_polynomial ι R} (hp : p ≠ 0) : p.leading_terms ≠ 0 :=
begin
  classical,
  rw leading_terms_apply,
  apply sum_monomial_ne_zero_of_exists_mem_ne_zero,
  simp only [exists_prop, mem_support_iff, finset.mem_filter],
  convert exists_coeff_ne_zero_total_degree hp,
  ext v,
  change v.sum (λ (_x : ι) (e : ℕ), e) with v.support.sum v,
  simp [and_comm],
end

@[simp]
lemma total_degree_homogenous_component_of_ne_zero {n : ℕ} {p : mv_polynomial ι R}
  (hp : homogeneous_component n p ≠ 0) :
  (homogeneous_component n p).total_degree = n :=
is_homogeneous.total_degree (homogeneous_component_is_homogeneous n p) hp

@[simp]
lemma total_degree_leading_terms (p : mv_polynomial ι R) :
  p.leading_terms.total_degree = p.total_degree :=
begin
  by_cases hp : p = 0,
  { simp [hp], },
  exact total_degree_homogenous_component_of_ne_zero (leading_terms_ne_zero hp),
end

-- TODO generalize this to homogeneous component idempotent?
lemma leading_terms_idempotent (p : mv_polynomial ι R) :
  p.leading_terms.leading_terms = p.leading_terms :=
begin
  rw [leading_terms_eq_self_iff_is_homogeneous, total_degree_leading_terms],
  exact is_homogeneous_leading_terms p,
end
lemma homogeneous_component_add (m  : ℕ) (p q : mv_polynomial ι R) :
  homogeneous_component m (p + q) = homogeneous_component m p + homogeneous_component m q :=
by rw [homogeneous_component, linear_map.comp_apply, linear_map.comp_apply, linear_map.comp_apply,
    linear_map.map_add, linear_map.map_add]

-- TODO lol this isn't true
-- lemma homogeneous_component_mul (m n : ℕ) (p q : mv_polynomial ι R) :
--   homogeneous_component (m + n) (p * q) = homogeneous_component m p * homogeneous_component n q :=
-- begin
--   sorry,
-- end

lemma leading_terms_mul [no_zero_divisors R] (p q : mv_polynomial ι R) :
  (p * q).leading_terms = p.leading_terms * q.leading_terms :=
begin
  sorry,
end

end leading_terms

lemma homogenization_mul (i : ι) (p q : mv_polynomial ι R)
  (hp : ∀ j ∈ p.support, (j : ι → ℕ) i = 0) (hq : ∀ j ∈ q.support, (j : ι → ℕ) i = 0) :
  (p * q).homogenization i = p.homogenization i * q.homogenization i :=
begin
  simp [homogenization],
  -- rw finsupp.map_domain_mul,
  sorry,
end

lemma homogenization_X_add_C {i j : ι} (hij : i ≠ j) (r : R) :
  (X j + C r : mv_polynomial ι R).homogenization i = X j + C r * X i :=
begin
  have : (X j + C r).total_degree = 1,
  sorry,
  erw [homogenization, finsupp.map_domain_add, finsupp.map_domain_single,
    finsupp.map_domain_single],
  simp only [tsub_zero, finsupp.sum_zero_index, finsupp.sum_single_index, this,
    finsupp.update_eq_single_add_erase, add_zero, finsupp.single_zero, zero_add, finsupp.erase_zero,
    single_eq_monomial, finsupp.erase_single_ne hij],
  rw [X, X],
  congr,
  rw [monomial_eq_C_mul_X, pow_one],
  refl,
end

lemma homogenization_prod (i : ι) (P : finset (mv_polynomial ι R))
  (hp : ∀ (p : mv_polynomial ι R) (hp : p ∈ P) (j) (hjp : j ∈ p.support), (j : ι → ℕ) i = 0) :
  (P.prod id).homogenization i = P.prod (λ p, p.homogenization i) :=
begin
  sorry, -- TODO should follow from previous easily
end

lemma homogenization_add_of_total_degree_eq (i : ι) (p q : mv_polynomial ι R)
  (h : p.total_degree = q.total_degree) (hpq : p.total_degree = (p + q).total_degree) :
  (p + q).homogenization i = p.homogenization i + q.homogenization i :=
by simp only [homogenization, finsupp.map_domain_add, ←h, ←hpq]

end mv_polynomial
