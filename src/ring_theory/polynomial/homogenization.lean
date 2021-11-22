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

-- TODO something like this should be true but unsure what
lemma finsupp.sum_update_add {α β : Type*} [has_zero α] [add_comm_monoid β]
  (f : ι →₀ α) (i : ι) (a : α) (g : ι → α → β) (hg : ∀ i, g i 0 = 0) :
  (f.update i a).sum g + g i (f i) = f.sum g + g i a :=
begin
  classical,
  have hf : f.support ⊆ f.support ∪ {i} := f.support.subset_union_left {i},
  have hif : (f.update i a).support ⊆ f.support ∪ {i},
  { rw f.support_update i a, -- urgh why is this classical
    split_ifs,
    { convert finset.subset.trans (finset.erase_subset i f.support) hf },
    { rw [finset.insert_eq, finset.union_comm],
      convert finset.subset.refl _  }, }, -- TODO is there no lemma for this?
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
-- TODO make this change and instead of update simply add to the i component the amount needed
-- this will have better properties (like being idempotent)

/-- The homogenization of a multivariate polynomial at a single variable. -/
def homogenization (i : ι) (p : mv_polynomial ι R) :
  mv_polynomial ι R :=
-- ∑ j in p.support, monomial (j + finsupp.single i (p.total_degree - (j i))) (p.coeff j)
finsupp.map_domain (λ j, j + finsupp.single i (p.total_degree - j.sum (λ _ m, m))) p
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

-- TODO this is probably useless
-- lemma map_domain_one {α β M : Type*} [has_zero β] [has_zero α] [has_one M]
--   [add_comm_monoid M] {f : α → β} (hf : f 0 = 0) :
--   finsupp.map_domain f (finsupp.single 0 1 : α →₀ M) = (finsupp.single 0 1 : β →₀ M) :=
-- by simp [hf]

-- TODO maybe instead prove this via is_homogeneous_one
@[simp]
lemma homogenization_one (i : ι) : (1 : mv_polynomial ι R).homogenization i = 1 :=
begin
  simp only [homogenization, total_degree_one, zero_tsub, add_zero, finsupp.single_zero],
  erw finsupp.map_domain_single,
  -- erw map_domain_one,
  refl,
end

@[simp]
lemma homogenization_C (i : ι) (c : R) : (C c : mv_polynomial ι R).homogenization i = C c :=
begin
  simp only [homogenization, total_degree_C, zero_tsub],
  convert finsupp.map_domain_single,
  rw single_eq_monomial,
  have : (0 : ι →₀ ℕ) i = 0,
  { simp only [finsupp.coe_zero, pi.zero_apply], },
  rw [← this],
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
    tsub_self, ← hs],
  rw monomial_add_single,
  simp only [hs, mul_one, pow_zero],
end

-- TODO name this
lemma aux {i : ι} {p : mv_polynomial ι R} {x : ι →₀ ℕ} (hp : x ∈ p.support) :
  (x + finsupp.single i (p.total_degree - x.sum (λ _ m, m))).sum (λ _ m, m) = p.total_degree :=
begin
  rw finsupp.sum_add_index,
  rw [finsupp.sum_single_index],
  rw [add_tsub_cancel_iff_le],
  exact finset.le_sup hp,
  refl,
  intro, refl,
  intros, refl,
end

lemma is_homogeneous_homogenization (i : ι) (p : mv_polynomial ι R) :
  (p.homogenization i).is_homogeneous p.total_degree :=
begin
  letI := classical.dec_eq ι,
  rw homogenization,
  intros d hd,
  rw [finsupp.map_domain, finsupp.sum, coeff_sum] at hd,
  simp_rw [single_eq_monomial, coeff_monomial] at hd,
  contrapose! hd,
  have : ∀ (x : ι →₀ ℕ) (hx : x ∈ p.support),
    ¬ x + finsupp.single i (p.total_degree - x.sum (λ (_x : ι) (m : ℕ), m)) = d,
  { intros x hx hh,
    apply hd,
    rw ← hh,
    change (x + finsupp.single i (p.total_degree - x.sum (λ _ m, m))).sum (λ _ m, m) = _,
    rw aux hx, },
  conv in (ite _ _ _)
  { rw [if_neg (this x H)], },
  simp,
end

lemma homogenization_of_is_homogeneous (n : ℕ) (i : ι) (p : mv_polynomial ι R)
  (hp : p.is_homogeneous n) : p.homogenization i = p :=
begin
  by_cases hpn : p = 0,
  { simp [hpn], },
  rw homogenization,
  have := (hp.total_degree hpn).symm,
  subst this,
  rw is_homogeneous at hp,
  have : ∀ x (hx : x ∈ p.support),
    (λ (j : ι →₀ ℕ), j + finsupp.single i (p.total_degree - j.sum (λ (_x : ι) (m : ℕ), m))) x = x,
  { intros x hx,
    simp only [add_right_eq_self, finsupp.single_eq_same, tsub_eq_zero_iff_le, finsupp.single_tsub,
      finsupp.single_le_iff],
    rw ← hp (mem_support_iff.mp hx),
    exact le_refl _, },
  rw finsupp.map_domain_congr this,
  -- simp,
  erw finsupp.map_domain_id,
  -- TODO there should be a simp lemma version of this for λ x, x so simp works
end

lemma homogenization_idempotent (i : ι) (p : mv_polynomial ι R) :
  (p.homogenization i).homogenization i = p.homogenization i :=
begin
  classical,
  apply homogenization_of_is_homogeneous p.total_degree,
  exact is_homogeneous_homogenization _ _,
end

section finsupp
open finsupp

-- TODO want something like this but unsure what
lemma map_domain_apply' {α β M : Type*} [add_comm_monoid M] (S : set α) {f : α → β} (x : α →₀ M)
  (hf : set.inj_on f x.support) (a : α) : finsupp.map_domain f x (f a) = x a :=
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
  -- rw [finsupp.map_domain_apply hf, finsupp.map_domain_apply hf] at this,
end
end finsupp

lemma homogenization_ne_zero_of_ne_zero (i : ι) {p : mv_polynomial ι R} (hp : p ≠ 0) :
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
lemma total_degree_homogenization (i : ι) (p : mv_polynomial ι R) :
  --(h : ∀ j ∈ p.support, (j : ι → ℕ) i = 0) : -- this arg is probably needed? I (RB) deleted it since
  --it's not needed, I am keeping as comment since I don't why it's here
  (p.homogenization i).total_degree = p.total_degree :=
begin
  classical,
  by_cases hp : p = 0,
  { simp [hp], },
  apply is_homogeneous.total_degree,
  refine is_homogeneous_homogenization _ _,
  exact (homogenization_ne_zero_of_ne_zero _ hp),
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
lemma sum_monomial_ne_zero_of_exists_mem_ne_zero (S : finset (ι →₀ ℕ)) (f : (ι →₀ ℕ) → R)
  (h : ∃ (s) (hs : s ∈ S), f s ≠ 0) : ∑ (s : ι →₀ ℕ) in S, monomial s (f s) ≠ 0 :=
begin
  letI := classical.dec_eq ι,
  letI := classical.dec_eq R,
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

lemma coeff_leading_terms (p : mv_polynomial ι R) (d : ι →₀ ℕ) :
  coeff d p.leading_terms = if ∑ i in d.support, d i = p.total_degree then coeff d p else 0 :=
coeff_homogeneous_component _ _ _

lemma support_homogeneous_component (n : ℕ) (p : mv_polynomial ι R) :
  (homogeneous_component n p).support = p.support.filter (λ d, d.sum (λ _ m, m) = n) :=
begin
  rw homogeneous_component,
  simp only [finsupp.restrict_dom_apply, submodule.subtype_apply, function.comp_app,
    linear_map.coe_comp, set.mem_set_of_eq],
  erw ← finsupp.support_filter,
  refl,
end

lemma support_homogeneous_component_subset (n : ℕ) (p : mv_polynomial ι R) :
  (homogeneous_component n p).support ⊆ p.support :=
begin
  rw support_homogeneous_component,
  exact finset.filter_subset _ _,
end

lemma support_leading_terms (p : mv_polynomial ι R) :
  p.leading_terms.support = p.support.filter (λ d, d.sum (λ _ m, m) = p.total_degree) :=
support_homogeneous_component _ _

lemma support_leading_terms_subset (p : mv_polynomial ι R) : p.leading_terms.support ⊆ p.support :=
support_homogeneous_component_subset _ _

lemma eq_leading_terms_add (p : mv_polynomial ι R) (hp : p.total_degree ≠ 0) :
  ∃ p_rest : mv_polynomial ι R,
    p = p.leading_terms + p_rest ∧ p_rest.total_degree < p.total_degree :=
begin
  letI := classical.dec_eq ι,
  existsi (∑ (v : ι →₀ ℕ) in p.support \ p.leading_terms.support, (monomial v) (coeff v p)),
  split,
  { nth_rewrite 0 p.leading_terms.as_sum,
    have : ∀ (x : ι →₀ ℕ) (hx : x ∈ p.leading_terms.support), x.support.sum x = p.total_degree,
    { intros x hx,
      rw support_leading_terms at hx,
      simp at hx,
      exact hx.2, },
    simp_rw coeff_leading_terms,
    conv in (ite _ _ _)
    { rw [if_pos (this x H)], },
    have : p.leading_terms.support ⊆ p.support,
    from support_leading_terms_subset _,
    have : p.leading_terms.support ∩ p.support = p.leading_terms.support,
    { rw finset.inter_eq_left_iff_subset,
      exact this },
    nth_rewrite 0 ← this,
    rw finset.inter_comm,
    rw finset.sum_inter_add_sum_diff,
    exact p.as_sum, },
  { rw total_degree,
    rw finset.sup_lt_iff,
    intros b hb,
    rw support_leading_terms at hb,
    rw ← finset.filter_not at hb, -- TODO this was also hard to find maybe a negated version is good
    have := support_sum_monomial_subset _ _ hb,
    simp only [finset.mem_filter] at this,
    cases this,
    rw total_degree,
    apply lt_of_le_of_ne,
    exact finset.le_sup this_left,
    exact this_right,
    rw [bot_eq_zero],
    exact pos_iff_ne_zero.mpr hp, },
end

lemma is_homogeneous_of_total_degree_zero {p : mv_polynomial ι R} (hp : p.total_degree = 0) :
  is_homogeneous p 0 :=
begin
  sorry
end
lemma total_degree_add_of_total_degree_lt (p q : mv_polynomial ι R)
  (h : q.total_degree < p.total_degree) : (p + q).total_degree = p.total_degree :=
begin
  apply le_antisymm,
  { have := total_degree_add p q,
    rwa max_eq_left_of_lt h at this, },
  { rw total_degree,
    rw total_degree,
    sorry, -- probably best to rethink this
     },
end

lemma leading_terms_add_of_total_degree_lt (p q : mv_polynomial ι R)
  (h : q.total_degree < p.total_degree) : (p + q).leading_terms = p.leading_terms :=
by rw [leading_terms, leading_terms, total_degree_add_of_total_degree_lt p q h,
  homogeneous_component_add, homogeneous_component_eq_zero _ q h, add_zero]

-- lemma C_mul_eq_smul {r : R} (p : mv_polynomial ι R) : C r * p = r • p :=
-- by rw [C_eq_smul_one, algebra.smul_mul_assoc, one_mul]

lemma homogeneous_component_C_mul (n : ℕ) (p : mv_polynomial ι R) (r : R) :
  homogeneous_component n (C r * p) = C r * homogeneous_component n p :=
begin
  rw homogeneous_component,
  simp only [finsupp.restrict_dom_apply, submodule.subtype_apply, function.comp_app,
    linear_map.coe_comp, set.mem_set_of_eq],
  rw C_mul', -- TODO this has a weird name
  rw finsupp.filter_smul,
  rw C_mul', -- TODO this has a weird name
end
--TODO maybe this for leading terms and homog
-- lemma homogeneous_s_monomial_mul [no_zero_divisors R] (p : mv_polynomial ι R) (r : R) (x : ι →₀ ℕ) :
  -- (p * monomial x r).leading_terms = p.leading_terms * monomial x r :=
  --TODO also maybe an smul version
lemma leading_terms_C_mul [no_zero_divisors R] (p : mv_polynomial ι R) (r : R) :
  (C r * p).leading_terms = C r * p.leading_terms :=
begin
  rw leading_terms,
  rw leading_terms,
  rw total_degree,
  have : (C r * p).support = p.support,
  sorry,
  rw this,
  rw homogeneous_component_C_mul,
  refl,
end

lemma leading_terms_mul [no_zero_divisors R] (p q : mv_polynomial ι R) :
  (p * q).leading_terms = p.leading_terms * q.leading_terms :=
begin
  by_cases hp : p.total_degree = 0,
  { have := is_homogeneous_of_total_degree_zero hp,
    -- have := is_homogeneous_of_total_degree_zero hq,
    -- rw (leading_terms_eq_self_iff_is_homogeneous _).mpr this,
    -- rw (sorry : p.leading_terms = p),
    -- rw (sorry : q.leading_terms = q),
    sorry, },
  by_cases hq : q.total_degree = 0,
  sorry,
  rcases eq_leading_terms_add p hp with ⟨wp, hp, tp⟩,
  rw hp,
  rcases eq_leading_terms_add q hq with ⟨wq, hq, tq⟩,
  rw hq,
  simp [add_mul, mul_add],
  -- rw leading_terms_C_mul,
  sorry,
end

lemma total_degree_mul_eq [no_zero_divisors R] {p q : mv_polynomial ι R} (hp : p ≠ 0) (hq : q ≠ 0) :
  (p * q).total_degree = p.total_degree + q.total_degree :=
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

end mv_polynomial
section finset_prod
namespace finset

-- Like everything else in this file, for mathlib, theory of add / mul on finsets, API duplicated
-- from the set version

open function
open finset

variables {α : Type*} {β : Type*} {s s₁ s₂ t t₁ t₂ u : finset α} {a b : α}
  {x y : β}
open_locale pointwise

/-- The set `(1 : finset α)` is defined as `{1}` in locale `pointwise`. -/
@[to_additive
/-"The set `(0 : finset α)` is defined as `{0}` in locale `pointwise`. "-/]
protected def has_one [has_one α] : has_one (finset α) := ⟨{1}⟩

localized "attribute [instance] finset.has_one finset.has_zero" in pointwise

@[to_additive]
lemma singleton_one [has_one α] : ({1} : finset α) = 1 := rfl

@[simp, to_additive]
lemma mem_one [has_one α] : a ∈ (1 : finset α) ↔ a = 1 :=
by simp [has_one.one]

@[to_additive]
lemma one_mem_one [has_one α] : (1 : α) ∈ (1 : finset α) := by simp [has_one.one]

@[simp, to_additive]
theorem one_subset [has_one α] : 1 ⊆ s ↔ (1 : α) ∈ s := singleton_subset_iff

@[to_additive]
theorem one_nonempty [has_one α] : (1 : finset α).nonempty := ⟨1, one_mem_one⟩

@[simp, to_additive]
theorem image_one [decidable_eq β] [has_one α] {f : α → β} : image f 1 = {f 1} :=
image_singleton f 1

-- @[simp, to_additive]
-- lemma image2_mul [has_mul α] : finset.image2 has_mul.mul s t = s * t := rfl

-- this is just a symmetrized version of the def, is it needed?
-- TODO why are these names weird
@[to_additive add_image_prod]
lemma image_mul_prod [decidable_eq α] [has_mul α] :
  image (λ x : α × α, x.fst * x.snd) (s.product t) = s * t := rfl

@[simp, to_additive]
lemma image_mul_left [decidable_eq α] [group α] :
  image (λ b, a * b) t = preimage t (λ b, a⁻¹ * b) (assume x hx y hy, (mul_right_inj a⁻¹).mp) :=
sorry

@[simp, to_additive]
lemma image_mul_right [decidable_eq α] [group α] :
  image (λ a, a * b) t = preimage t (λ a, a * b⁻¹) (assume x hx y hy, (mul_left_inj b⁻¹).mp) :=
sorry

@[to_additive]
lemma image_mul_left' [decidable_eq α] [group α] :
  image (λ b, a⁻¹ * b) t = preimage t (λ b, a * b) (assume x hx y hy, (mul_right_inj a).mp) :=
by simp

@[to_additive]
lemma image_mul_right' [decidable_eq α] [group α] :
  image (λ a, a * b⁻¹) t = preimage t (λ a, a * b) (assume x hx y hy, (mul_left_inj b).mp) :=
by simp

@[simp, to_additive]
lemma preimage_mul_left_singleton [group α] :
  preimage {b} ((*) a) (assume x hx y hy, (mul_right_inj a).mp) = {a⁻¹ * b} :=
by { classical, rw [← image_mul_left', image_singleton] }

@[simp, to_additive]
lemma preimage_mul_right_singleton [group α] :
  preimage {b} (* a) (assume x hx y hy, (mul_left_inj a).mp)= {b * a⁻¹} :=
by { classical, rw [← image_mul_right', image_singleton] }

-- TODO fill out these for finset, changing image and preimage to the finset version
-- @[simp, to_additive]
-- lemma preimage_mul_left_one [group α] : (λ b, a * b) ⁻¹' 1 = {a⁻¹} :=
-- by rw [← image_mul_left', image_one, mul_one]

-- @[simp, to_additive]
-- lemma preimage_mul_right_one [group α] : (λ a, a * b) ⁻¹' 1 = {b⁻¹} :=
-- by rw [← image_mul_right', image_one, one_mul]

-- @[to_additive]
-- lemma preimage_mul_left_one' [group α] : (λ b, a⁻¹ * b) ⁻¹' 1 = {a} := by simp

-- @[to_additive]
-- lemma preimage_mul_right_one' [group α] : (λ a, a * b⁻¹) ⁻¹' 1 = {b} := by simp

@[simp, to_additive]
lemma mul_singleton [decidable_eq α] [has_mul α] : s * {b} = image (λ a, a * b) s := sorry

@[simp, to_additive]
lemma singleton_mul [decidable_eq α] [has_mul α] : {a} * t = image (λ b, a * b) t := sorry --image2_singleton_left

-- @[simp, to_additive]
-- lemma singleton_mul_singleton [has_mul α] : ({a} : set α) * {b} = {a * b} := image2_singleton

@[to_additive]
protected lemma mul_comm [decidable_eq α] [comm_semigroup α] : s * t = t * s :=
by simp only [mul_def, mul_comm]; sorry

/-- `finset α` is a `mul_one_class` under pointwise operations if `α` is. -/
@[to_additive /-"`set α` is an `add_zero_class` under pointwise operations if `α` is."-/]
protected def mul_one_class [decidable_eq α] [mul_one_class α] : mul_one_class (finset α) :=
{ mul_one := λ s, by { simp only [← singleton_one, mul_singleton, mul_one, image_id'] },
  one_mul := λ s, by { simp only [← singleton_one, singleton_mul, one_mul, image_id'] },
  ..finset.has_one, ..finset.has_mul }

/-- `set α` is a `semigroup` under pointwise operations if `α` is. -/
@[to_additive /-"`set α` is an `add_semigroup` under pointwise operations if `α` is. "-/]
protected def semigroup [decidable_eq α] [semigroup α] : semigroup (finset α) :=
{ mul_assoc := λ _ _ _, sorry,--image2_assoc mul_assoc,
  ..finset.has_mul }

/-- `set α` is a `monoid` under pointwise operations if `α` is. -/
@[to_additive /-"`set α` is an `add_monoid` under pointwise operations if `α` is. "-/]
protected def monoid [decidable_eq α] [monoid α] : monoid (finset α) :=
{ ..finset.semigroup,
  ..finset.mul_one_class }

/-- `set α` is a `comm_monoid` under pointwise operations if `α` is. -/
@[to_additive /-"`set α` is an `add_comm_monoid` under pointwise operations if `α` is. "-/]
protected def comm_monoid [decidable_eq α] [comm_monoid α] : comm_monoid (finset α) :=
{ mul_comm := λ _ _, finset.mul_comm, ..finset.monoid }

localized "attribute [instance] finset.mul_one_class finset.add_zero_class finset.semigroup
  finset.add_semigroup finset.monoid finset.add_monoid finset.comm_monoid finset.add_comm_monoid"
  in pointwise

@[to_additive]
lemma mul_subset_mul [decidable_eq α] [has_mul α] (h₁ : s₁ ⊆ t₁) (h₂ : s₂ ⊆ t₂) :
  s₁ * s₂ ⊆ t₁ * t₂ := sorry

-- TODO there is loads more API in pointwise that could (should) be duplicated?

-- TODO a lemma mem_prod for both set and finset, saying that something is in a product of sets
-- only if it is a product of elements of each


end finset
end finset_prod

namespace mv_polynomial
section

-- generalized version of the unprimed version
lemma support_sum_monomial_subset' [decidable_eq ι] {α : Type*} (S : finset α) (g : α → ι →₀ ℕ)
  (f : α → R) : support (∑ v in S, monomial (g v) (f v)) ⊆ S.image g :=
begin
  letI := classical.dec_eq α,
  induction S using finset.induction with s S hs hsi,
  { simp, },
  { rw finset.sum_insert hs,
    apply finset.subset.trans support_add,
    apply finset.union_subset,
    { apply finset.subset.trans support_monomial_subset _,
      rw finset.image_insert,
      convert finset.subset_union_left _ (finset.image g S), },
    { apply finset.subset.trans hsi _,
      rw finset.image_insert,
      exact finset.subset_insert (g s) (finset.image g S), }, },
end
open_locale pointwise

lemma support_mul' [decidable_eq ι] (p q : mv_polynomial ι R) :
  (p * q).support ⊆ p.support + q.support :=
begin
  -- TODO this was really hard to find, maybe needs a docstring or alias?
  rw [p.as_sum, q.as_sum, finset.sum_mul_sum],
  simp_rw [monomial_mul],
  rw [support_sum_monomial_coeff, support_sum_monomial_coeff],
  exact finset.subset.trans (support_sum_monomial_subset' _ _ _) (finset.subset.refl _),
end
section
open_locale pointwise
@[simp] lemma support_one : (1 : mv_polynomial ι R).support ⊆ 0 :=
finsupp.support_single_subset
-- @[simp] lemma support_one [nontrivial R] : (1 : mv_polynomial ι R).support = 0 :=
-- begin
--   convert (finsupp.support_eq_singleton).mpr _,
--   split,
--   simp,
--   change (1 : R) ≠ 0,
-- end
end

variable [decidable_eq ι]
lemma support_prod (P : finset (mv_polynomial ι R)) : (P.prod id).support ⊆ P.sum support :=
begin
  classical,
  induction P using finset.induction with p S hS hSi,
  { simp [support_X], },
  rw [finset.prod_insert hS, finset.sum_insert hS],
  simp only [id.def],
  refine finset.subset.trans (support_mul' _ _) _,
  convert finset.add_subset_add (finset.subset.refl _) hSi,
end

end

lemma prod_contains_no (i : ι)
 (P : finset (mv_polynomial ι R))
  (hp : ∀ (p : mv_polynomial ι R) (hp : p ∈ P) (j) (hjp : j ∈ p.support), (j : ι → ℕ) i = 0)
  (j) (hjp : j ∈ (P.prod id).support) :
  (j : ι → ℕ) i = 0 :=
begin
  classical,
  induction P using finset.induction with p S hS hSi generalizing j,
  { simp only [mem_support_iff, finset.prod_empty] at hjp,
    have : j = 0,
    sorry,
    simp [this], },
  { have := support_prod _ hjp,
    rw finset.prod_insert hS at hjp,
    rw finset.sum_insert hS at this,
    simp at this,
    rw finset.mem_add at this,
    rcases this with ⟨y, z, hy, hz, hh⟩,
    have := hp _ (finset.mem_insert_self p S) _ hy,
    have := hSi _ z _,
    sorry,
    sorry,
    sorry,
    -- TODO probably need more lemmas for this still
    -- apply support_prod,
  }
  -- TODO this proof should be simple with `support_prod` we know j is in
  -- { simp only [finset.prod_insert hS, id.def, ne.def] at hjp,
  --   apply hSi, },
end

lemma homogenization_prod (i : ι) (P : finset (mv_polynomial ι R))
  (hp : ∀ (p : mv_polynomial ι R) (hp : p ∈ P) (j) (hjp : j ∈ p.support), (j : ι → ℕ) i = 0) :
  (P.prod id).homogenization i = P.prod (λ p, p.homogenization i) :=
begin
  classical,
  induction P using finset.induction with p S hS hSi,
  { simp, },
  simp only [finset.prod_insert hS],
  rw homogenization_mul,
  rw hSi,
  rw [id.def],
  { intros p_1 hp_1 j hjp,
    exact hp p_1 (finset.mem_insert_of_mem hp_1) _ hjp, },
  { intros j hj,
    exact hp p (finset.mem_insert_self p S) _ hj, },
  { intros j hj,
    have := support_prod _ hj,
    sorry,
     },
end

lemma homogenization_add_of_total_degree_eq (i : ι) (p q : mv_polynomial ι R)
  (h : p.total_degree = q.total_degree) (hpq : p.total_degree = (p + q).total_degree) :
  (p + q).homogenization i = p.homogenization i + q.homogenization i :=
by simp only [homogenization, finsupp.map_domain_add, ←h, ←hpq]

end mv_polynomial
